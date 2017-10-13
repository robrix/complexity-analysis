{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import qualified Control.Comonad.Trans.Cofree as F
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Either (fromLeft)
import Data.Env
import Data.Expr
import Data.Functor.Foldable (Recursive(..), Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type

data Error
  = FreeVariable Name
  | TypeMismatch (Type (PartialType Error)) (Type (PartialType Error))
  | InfiniteType Name (Type (PartialType Error))
  deriving (Eq, Ord, Read, Show)

type Elab = StateT (Subst (PartialType Error)) (ReaderT (Env Name) (Fresh Name))

type ElabTerm = Cofree Expr (PartialType Error)

runElab :: Elab a -> (a, Subst (PartialType Error))
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

substElaborated :: ElabTerm -> Subst (PartialType Error) -> ElabTerm
substElaborated = cata (\ (ty F.:< expr) subst -> substitute subst ty :< (($ subst) <$> expr))

instance Binder (PartialType Error) Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))


elaborate :: Term -> Elab ElabTerm
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
elaborate (Fix (Lit b)) = pure (bool :< Lit b)
elaborate (Fix (If c t e)) = do
  c' <- check c bool
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

check :: Term -> PartialType Error -> Elab (Cofree Expr (PartialType Error))
check term ty = do
  term' <- elaborate term
  termTy <- unify (extract term') ty
  pure (termTy :< unwrap term')


unify :: PartialType Error -> PartialType Error -> Elab (PartialType Error)
unify (Pure e1) _         = pure (Pure e1)
unify _         (Pure e2) = pure (Pure e2)
unify (Free t1) (Free t2)
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Bool       <- t1, Bool       <- t2 = pure bool
  | otherwise = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Type (PartialType Error) -> Elab (PartialType Error)
bind name ty
  | TVar name' <- ty, name == name'        = pure (wrap ty)
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = modify (substExtend name (wrap ty)) >> pure (wrap ty)
