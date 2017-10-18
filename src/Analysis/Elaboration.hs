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

type Elab = StateT (Subst (Partial Type Error)) (ReaderT (Env Name) Fresh)

runElab :: Elab a -> (a, Subst (Partial Type Error))
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

elaborate :: Term Expr -> Elab (Ann Expr (Partial Type Error))
elaborate term = do
  term' <- infer term
  subst <- get
  let In ty tm = substitute subst term'
  pure (In (generalize ty) tm)

infer :: Term Expr -> Elab (Ann Expr (Partial Type Error))
infer (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n t) (infer b)
  pure (In (tvar t .-> ann b') (Abs n b'))
infer (Fix (Var name)) = do
  env <- ask
  pure (In (maybe (Stop (FreeVariable name)) tvar (envLookup name env)) (Var name))
infer (Fix (App f a)) = do
  t <- fresh
  a' <- infer a
  f' <- check f (ann a' .-> tvar t)
  pure (In (tvar t) (App f' a'))
infer (Fix (Rec n b)) = do
  t <- fresh
  local (envExtend n t) (check b (tvar t))
infer (Fix Expr.Unit) = pure (In unitT Expr.Unit)
infer (Fix (Pair fst snd)) = do
  fst' <- infer fst
  snd' <- infer snd
  pure (In (ann fst' .* ann snd') (Pair fst' snd'))
infer (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (In (tvar t1) (Fst pair'))
infer (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (In (tvar t2) (Snd pair'))
infer (Fix (Expr.Bool b)) = pure (In boolT (Expr.Bool b))
infer (Fix (If c t e)) = do
  c' <- check c boolT
  t' <- infer t
  e' <- infer e
  result <- unify (ann t') (ann e')
  pure (In result (If c' t' e'))
infer (Fix (Cons h t)) = do
  a <- fresh
  h' <- check h (tvar a)
  t' <- check t (listT (tvar a))
  pure (In (listT (tvar a)) (Cons h' t'))
infer (Fix Nil) = flip In Nil . listT . tvar <$> fresh
infer (Fix (Unlist empty full list)) = do
  a <- fresh
  empty' <- infer empty
  full' <- check full (tvar a .-> listT (tvar a) .-> ann empty')
  list' <- check list (listT (tvar a))
  pure (In (ann empty') (Unlist empty' full' list'))

check :: Term Expr -> Partial Type Error -> Elab (Ann Expr (Partial Type Error))
check term ty = do
  term' <- infer term
  termTy <- unify (ann term') ty
  pure (In termTy (out term'))


unify :: Partial Type Error -> Partial Type Error -> Elab (Partial Type Error)
unify (Stop e1) _         = pure (Stop e1)
unify _         (Stop e2) = pure (Stop e2)
unify (Continue t1) (Continue t2)
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | ForAll{}   <- t1, ForAll{}   <- t2 = fresh >>= \ n -> makeForAllT n <$> unify (specialize t1 n) (specialize t2 n)
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise = pure (Stop (TypeMismatch t1 t2))

bind :: Name -> Type (Partial Type Error) -> Elab (Partial Type Error)
bind name ty
  | TVar name' <- ty, name == name'        = pure (Continue ty)
  | Set.member name (freeTypeVariables ty) = pure (Stop (InfiniteType name ty))
  | otherwise                              = do
    subst <- get
    let ty' = substitute subst (Continue ty)
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)
