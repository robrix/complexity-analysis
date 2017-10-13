{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
module Data.Complexity where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import qualified Control.Comonad.Trans.Cofree as F
import Control.Monad.Free
import qualified Control.Monad.Trans.Free as F
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Expr
import Data.Function (on)
import Data.Functor.Foldable (Recursive(..), Fix(..))
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Name
import Data.Semigroup (Semigroup(..))
import qualified Data.Set as Set
import Data.Type

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)


newtype Env a = Env { getEnv :: [(Name, a)] }
  deriving (Eq, Monoid, Ord, Read, Semigroup, Show)

envLookup :: Name -> Env a -> Maybe a
envLookup name = lookup name . getEnv

envExtend :: Name -> a -> Env a -> Env a
envExtend name value = Env . ((name, value) :) . getEnv

newtype Subst value = Subst { getSubst :: [(Name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance Binder value => Semigroup (Subst value) where
  Subst s1 <> Subst s2 = Subst (List.unionBy ((==) `on` fst) (map (second (substitute (Subst s1))) s2) s1)

instance Binder value => Monoid (Subst value) where
  mempty = Subst []
  mappend = (<>)

substLookup :: Name -> Subst value -> Maybe value
substLookup name = lookup name . getSubst

substDelete :: Name -> Subst value -> Subst value
substDelete name = Subst . filter ((/= name) . fst) . getSubst

substSingleton :: Name -> value -> Subst value
substSingleton name value = Subst [(name, value)]

substExtend :: Binder value => Name -> value -> Subst value -> Subst value
substExtend name value = (substSingleton name value <>)


class Binder value where
  substitute :: Subst value -> value -> value

instance Binder (Free Type Error) where
  substitute = flip (cata (\ ty subst -> case ty of
    F.Free (TVar name)        -> fromMaybe (Free (TVar name)) (substLookup name subst)
    F.Free (ForAll name body) -> Free (ForAll name (body (substDelete name subst)))
    F.Free other              -> Free (($ subst) <$> other)
    F.Pure err                -> Pure err))


data Error
  = FreeVariable Name
  | TypeMismatch (Type (Free Type Error)) (Type (Free Type Error))
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
  pure (Free (Free (TVar t) :-> extract b') :< Abs n b')
elaborate (Fix (App f a)) = do
  t <- fresh
  f' <- elaborate f
  a' <- elaborate a
  fTy <- unify (extract f') (Free (extract a' :-> Free (TVar t)))
  pure (fromMaybe (Free (TVar t)) (returnType fTy) :< App f' a')
elaborate (Fix (Var name)) = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) (cata Free) (envLookup name env) :< Var name)
elaborate (Fix (Lit b)) = pure (Free Bool :< Lit b)
elaborate (Fix (If c t e)) = do
  c' <- elaborate c
  t' <- elaborate t
  e' <- elaborate e
  result <- unify (extract t') (extract e')
  pure (result :< If c' t' e')
elaborate (Fix (Pair fst snd)) = do
  fst' <- elaborate fst
  snd' <- elaborate snd
  pure (Free (extract fst' :* extract snd') :< Pair fst' snd')
elaborate (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elaborate pair
  pairTy <- unify (extract pair') (Free (Free (TVar t1) :* Free (TVar t2)))
  pure (fromMaybe (Free (TVar t1)) (fstType pairTy) :< Fst pair')
elaborate (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elaborate pair
  pairTy <- unify (extract pair') (Free (Free (TVar t1) :* Free (TVar t2)))
  pure (fromMaybe (Free (TVar t2)) (sndType pairTy) :< Snd pair')


unify :: Free Type Error -> Free Type Error -> Elab (Free Type Error)
unify (Pure err1)   _             = pure (Pure err1)
unify _             (Pure err2)   = pure (Pure err2)
unify (Free t1) (Free t2)
  | t1 == t2  = pure (Free t2)
  | otherwise = case (t1, t2) of
    (a1 :-> b1,  a2 :-> b2)  -> (Free .) . (:->) <$> unify a1 a2 <*> unify b1 b2
    (TVar name1, _)          -> bind name1 (Free t2)
    (_,          TVar name2) -> bind name2 (Free t1)
    (t1,         t2)         -> pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Free Type Error -> Elab (Free Type Error)
bind name ty
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = modify (substExtend name ty) >> pure ty
