module Analysis.Elaboration where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import qualified Control.Comonad.Trans.Cofree as F
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Env
import Data.Expr
import Data.Functor.Foldable (Recursive(..), Fix(..))
import Data.Maybe (fromMaybe)
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type

data Error
  = FreeVariable Name
  | TypeMismatch (Type (Free Type Error)) (Type (Free Type Error))
  | InfiniteType Name (Type (Free Type Error))
  deriving (Eq, Ord, Read, Show)

type Elab = StateT (Subst (Free Type Error)) (ReaderT (Env (Fix Type)) (Fresh Name))

runElab :: Elab a -> (a, Subst (Free Type Error))
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

substElaborated :: Cofree Expr (Free Type Error) -> Subst (Free Type Error) -> Cofree Expr (Free Type Error)
substElaborated = cata (\ (ty F.:< expr) subst -> substitute subst ty :< (($ subst) <$> expr))


elaborate :: Fix Expr -> Elab (Cofree Expr (Free Type Error))
elaborate (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n (Fix (TVar t))) (elaborate b)
  pure ((tvar t .-> extract b') :< Abs n b')
elaborate (Fix (App f a)) = do
  t <- fresh
  f' <- elaborate f
  a' <- elaborate a
  fTy <- unify (extract f') (extract a' .-> tvar t)
  pure (fromMaybe (tvar t) (returnType fTy) :< App f' a')
elaborate (Fix (Var name)) = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) (cata wrap) (envLookup name env) :< Var name)
elaborate (Fix (Lit b)) = pure (bool :< Lit b)
elaborate (Fix (If c t e)) = do
  c' <- elaborate c
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
  pair' <- elaborate pair
  pairTy <- unify (extract pair') (tvar t1 .* tvar t2)
  pure (fromMaybe (tvar t1) (fstType pairTy) :< Fst pair')
elaborate (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elaborate pair
  pairTy <- unify (extract pair') (tvar t1 .* tvar t2)
  pure (fromMaybe (tvar t2) (sndType pairTy) :< Snd pair')

check :: Fix Expr -> Free Type Error -> Elab (Cofree Expr (Free Type Error))
check term ty = do
  term' <- elaborate term
  termTy <- unify (extract term') ty
  pure (termTy :< unwrap term')


unify :: Free Type Error -> Free Type Error -> Elab (Free Type Error)
unify (Pure e1) _         = pure (Pure e1)
unify _         (Pure e2) = pure (Pure e2)
unify (Free t1) (Free t2)
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Bool       <- t1, Bool       <- t2 = pure bool
  | otherwise = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Type (Free Type Error) -> Elab (Free Type Error)
bind name ty
  | TVar name' <- ty, name == name'        = pure (wrap ty)
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = modify (substExtend name (wrap ty)) >> pure (wrap ty)
