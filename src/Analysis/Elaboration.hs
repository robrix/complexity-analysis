{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Env
import Data.Expr as Expr
import Data.FreeTypeVariables
import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab = StateT (Subst (Fix (Partial Type Error))) (ReaderT (Env Name) Fresh)

runElab :: Elab a -> (a, Subst (Fix (Partial Type Error)))
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

elaborate :: Term Expr -> Elab (Term (Ann Expr (Fix (Partial Type Error))))
elaborate term = do
  term' <- infer term
  subst <- get
  let Fix (In ty tm) = substitute subst term'
  pure (Fix (In (generalize ty) tm))

infer :: Term Expr -> Elab (Term (Ann Expr (Fix (Partial Type Error))))
infer (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n t) (infer b)
  pure (Fix (In (tvar t .-> ann b') (Abs n b')))
infer (Fix (Var name)) = do
  env <- ask
  pure (Fix (In (maybe (stop (FreeVariable name)) tvar (envLookup name env)) (Var name)))
infer (Fix (App f a)) = do
  t <- fresh
  a' <- infer a
  f' <- check f (ann a' .-> tvar t)
  pure (Fix (In (tvar t) (App f' a')))
infer (Fix (Rec n b)) = do
  t <- fresh
  local (envExtend n t) (check b (tvar t))
infer (Fix Expr.Unit) = pure (Fix (In unitT Expr.Unit))
infer (Fix (Pair fst snd)) = do
  fst' <- infer fst
  snd' <- infer snd
  pure (Fix (In (ann fst' .* ann snd') (Pair fst' snd')))
infer (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (Fix (In (tvar t1) (Fst pair')))
infer (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (Fix (In (tvar t2) (Snd pair')))
infer (Fix (Expr.Bool b)) = pure (Fix (In boolT (Expr.Bool b)))
infer (Fix (If c t e)) = do
  c' <- check c boolT
  t' <- infer t
  e' <- infer e
  result <- unify (ann t') (ann e')
  pure (Fix (In result (If c' t' e')))
infer (Fix (Cons h t)) = do
  a <- fresh
  h' <- check h (tvar a)
  t' <- check t (listT (tvar a))
  pure (Fix (In (listT (tvar a)) (Cons h' t')))
infer (Fix Nil) = Fix . flip In Nil . listT . tvar <$> fresh
infer (Fix (Unlist empty full list)) = do
  a <- fresh
  empty' <- infer empty
  full' <- check full (tvar a .-> listT (tvar a) .-> ann empty')
  list' <- check list (listT (tvar a))
  pure (Fix (In (ann empty') (Unlist empty' full' list')))

check :: Term Expr -> Fix (Partial Type Error) -> Elab (Term (Ann Expr (Fix (Partial Type Error))))
check term ty = do
  term' <- infer term
  termTy <- unify (ann term') ty
  pure (Fix (In termTy (expr term')))


unify :: Fix (Partial Type Error) -> Fix (Partial Type Error) -> Elab (Fix (Partial Type Error))
unify (Fix (Stop e1))     _               = pure (stop e1)
unify _                   (Fix (Stop e2)) = pure (stop e2)
unify (Fix (Continue t1)) (Fix (Continue t2))
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | ForAll{}   <- t1, ForAll{}   <- t2 = fresh >>= \ n -> makeForAllT n <$> unify (specialize t1 n) (specialize t2 n)
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise = pure (stop (TypeMismatch t1 t2))

bind :: Name -> Type (Fix (Partial Type Error)) -> Elab (Fix (Partial Type Error))
bind name ty
  | TVar name' <- ty, name == name'        = pure (continue ty)
  | Set.member name (freeTypeVariables ty) = pure (stop (InfiniteType name ty))
  | otherwise                              = do
    subst <- get
    let ty' = substitute subst (continue ty)
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)
