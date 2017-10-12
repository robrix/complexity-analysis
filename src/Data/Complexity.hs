{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Complexity where

import Control.Arrow ((&&&))
import Control.Monad ((<=<))
import Control.Monad.Reader
import Data.Bifunctor (first)
import Data.Functor.Identity

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)


data Expr a
  = Abs Name a
  | App a a
  | Var Name
  | Lit Bool
  | If a a a
  deriving (Foldable, Functor, Traversable)

newtype TName = TName Int
  deriving (Enum, Eq, Ord, Read, Show)

data Type a
  = TVar TName
  | ForAll TName a
  | a :-> a
  | Bool
  deriving (Foldable, Functor, Traversable)

infixr 0 :->


newtype Term f = In { out :: f (Term f) }

data Attr f a = Attr { attr :: a, hole :: f (Attr f a) }

data CoAttr f a
  = Stop a
  | Continue (f (CoAttr f a))


newtype Env a = Env { getEnv :: [(Name, a)] }
  deriving (Eq, Ord, Read, Show)

envLookup :: Name -> Env a -> Maybe a
envLookup name = lookup name . getEnv

envExtend :: Name -> a -> Env a -> Env a
envExtend name value = Env . ((name, value) :) . getEnv

newtype Subst a = Subst { getSubst :: [(Name, a)] }
  deriving (Eq, Ord, Read, Show)

type Error = String
type Result = Either Error

type Infer = ReaderT (Env (Term Type)) (Fresh TName)


type FAlgebra f a = f a -> a

cata :: Functor f => FAlgebra f a -> Term f -> a
cata algebra = go where go = algebra . fmap go . out

type FCoalgebra f a = a -> f a

ana :: Functor f => FCoalgebra f a -> a -> Term f
ana coalgebra = go where go = In . fmap go . coalgebra

type RAlgebra f a = f (Term f, a) -> a

para :: Functor f => RAlgebra f a -> Term f -> a
para algebra = go where go = algebra . fmap (id &&& go) . out

type RCoalgebra f a = a -> f (Either (Term f) a)

apo :: Functor f => RCoalgebra f a -> a -> Term f
apo coalgebra = go where go = In . fmap (either id go) . coalgebra

type CVAlgebra f a = f (Attr f a) -> a

histo :: Functor f => CVAlgebra f a -> Term f -> a
histo algebra = go
  where go = algebra . fmap worker . out
        worker t = Attr (go t) (worker <$> out t)

type CVCoalgebra f a = a -> f (CoAttr f a)

futu :: Functor f => CVCoalgebra f a -> a -> Term f
futu coalgebra = go
  where go = In . fmap worker . coalgebra
        worker (Stop a)     = go a
        worker (Continue f) = In (fmap worker f)


class Monad m => MonadFresh s m | m -> s where
  fresh :: m s


newtype FreshT s m a = FreshT { runFreshT :: s -> m (a, s) }

type Fresh s = FreshT s Identity

instance Functor m => Functor (FreshT s m) where
  fmap f (FreshT run) = FreshT (fmap (first f) . run)

instance Monad m => Applicative (FreshT s m) where
  pure = FreshT . (pure .) . (,)

  f <*> a = FreshT (\ s -> do
    (f', s') <- runFreshT f s
    (a', s'')<- runFreshT a s'
    pure (f' a', s''))

instance Monad m => Monad (FreshT s m) where
  return = pure

  a >>= f = FreshT (uncurry runFreshT . first f <=< runFreshT a)

instance (Enum s, Monad m) => MonadFresh s (FreshT s m) where
  fresh = FreshT (\ s -> pure (s, succ s))

instance MonadFresh s m => MonadFresh s (ReaderT r m) where
  fresh = lift fresh
