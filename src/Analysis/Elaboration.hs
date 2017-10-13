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
  | TypeMismatch (Free Type Error) (Free Type Error)
  | InfiniteType Name (Free Type Error)
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

check :: Fix Expr -> Fix Type -> Elab (Cofree Expr (Free Type Error))
check term ty = do
  term' <- elaborate term
  termTy <- unify (extract term') (cata wrap ty)
  pure (termTy :< unwrap term')


unify :: Free Type Error -> Free Type Error -> Elab (Free Type Error)
unify t1 t2
  | Free (TVar name1) <- t1                        = bind name1 t2
  | Free (TVar name2) <- t2                        = bind name2 t1
  | Free (a1 :-> b1) <- t1, Free (a2 :-> b2) <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | t1 == t2                                       = pure t2
  | otherwise                                      = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Free Type Error -> Elab (Free Type Error)
bind name ty
  | Free (TVar name') <- ty, name == name' = pure ty
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = modify (substExtend name ty) >> pure ty
