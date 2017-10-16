{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Env
import Data.Expr as Expr
import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab = StateT (Subst PartialType) (ReaderT (Env Name) (Fresh Name))

type PartialElabTerm = Cofree Expr PartialType

runElab :: Elab a -> (a, Subst PartialType)
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

elaborate :: Term -> Elab PartialElabTerm
elaborate (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n t) (elaborate b)
  pure ((tvar t .-> extract b') :< Abs n b')
elaborate (Fix (App f a)) = do
  t <- fresh
  a' <- elaborate a
  f' <- check f (extract a' .-> tvar t)
  pure (tvar t :< App f' a')
elaborate (Fix (Var name)) = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) tvar (envLookup name env) :< Var name)
elaborate (Fix (Expr.Bool b)) = pure (boolT :< Expr.Bool b)
elaborate (Fix (If c t e)) = do
  c' <- check c boolT
  t' <- elaborate t
  e' <- elaborate e
  result <- unify (extract t') (extract e')
  pure (result :< If c' t' e')
elaborate (Fix (Pair fst snd)) = do
  fst' <- elaborate fst
  snd' <- elaborate snd
  pure (extract fst' .* extract snd' :< Pair fst' snd')
elaborate (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (tvar t1 :< Fst pair')
elaborate (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (tvar t2 :< Snd pair')

check :: Term -> PartialType -> Elab PartialElabTerm
check term ty = do
  term' <- elaborate term
  termTy <- unify (extract term') ty
  pure (termTy :< unwrap term')


unify :: PartialType -> PartialType -> Elab PartialType
unify (Pure e1) _         = pure (Pure e1)
unify _         (Pure e2) = pure (Pure e2)
unify (Free t1) (Free t2)
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | otherwise = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Type PartialType -> Elab PartialType
bind name ty
  | TVar name' <- ty, name == name'        = pure (wrap ty)
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = do
    subst <- get
    maybe (modify (substExtend name (wrap ty)) >> pure (wrap ty)) (unify (wrap ty)) (substLookup name subst)
