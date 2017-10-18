{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import Control.Comonad.Trans.Cofree (tailF)
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Env
import Data.Expr as Expr
import Data.FreeTypeVariables
import Data.Functor.Foldable (Fix(..), cata)
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab = StateT (Subst PartialType) (ReaderT (Env Name) Fresh)

type PartialElabTerm = Cofree Expr PartialType

runElab :: Elab a -> (a, Subst PartialType)
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

infer :: Term -> Elab PartialElabTerm
infer (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n t) (infer b)
  pure ((tvar t .-> extract b') :< Abs n b')
infer (Fix (Var name)) = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) tvar (envLookup name env) :< Var name)
infer (Fix (App f a)) = do
  t <- fresh
  a' <- infer a
  f' <- check f (extract a' .-> tvar t)
  pure (tvar t :< App f' a')
infer (Fix (Rec n b)) = do
  t <- fresh
  local (envExtend n t) (check b (tvar t))
infer (Fix Expr.Unit) = pure (unitT :< Expr.Unit)
infer (Fix (Pair fst snd)) = do
  fst' <- infer fst
  snd' <- infer snd
  pure (extract fst' .* extract snd' :< Pair fst' snd')
infer (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (tvar t1 :< Fst pair')
infer (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (tvar t2 :< Snd pair')
infer (Fix (Expr.Bool b)) = pure (boolT :< Expr.Bool b)
infer (Fix (If c t e)) = do
  c' <- check c boolT
  t' <- infer t
  e' <- infer e
  result <- unify (extract t') (extract e')
  pure (result :< If c' t' e')
infer (Fix (Cons h t)) = do
  a <- fresh
  h' <- check h (tvar a)
  t' <- check t (listT (tvar a))
  pure (listT (tvar a) :< Cons h' t')
infer (Fix Nil) = (:< Nil) . listT . tvar <$> fresh
infer (Fix (Unlist empty full list)) = do
  a <- fresh
  empty' <- infer empty
  full' <- check full (tvar a .-> listT (tvar a) .-> extract empty')
  list' <- check list (listT (tvar a))
  pure (extract empty' :< Unlist empty' full' list')

check :: Term -> PartialType -> Elab PartialElabTerm
check term ty = do
  term' <- infer term
  termTy <- unify (extract term') ty
  pure (termTy :< unwrap term')


erase :: PartialElabTerm -> Term
erase = cata (Fix . tailF)


unify :: PartialType -> PartialType -> Elab PartialType
unify (Pure e1) _         = pure (Pure e1)
unify _         (Pure e2) = pure (Pure e2)
unify (Free t1) (Free t2)
  | TVar name1 <- t1                       = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | ForAll{}   <- t1, ForAll{}   <- t2 = fresh >>= \ n -> makeForAllT n <$> unify (specialize t1 n) (specialize t2 n)
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Type PartialType -> Elab PartialType
bind name ty
  | TVar name' <- ty, name == name'        = pure (wrap ty)
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = do
    subst <- get
    let ty' = substitute subst (wrap ty)
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)
