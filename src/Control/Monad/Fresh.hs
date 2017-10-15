{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances #-}
module Control.Monad.Fresh where

import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (first)
import Data.Functor.Identity

class Monad monad => MonadFresh name monad | monad -> name where
  fresh :: monad name


newtype FreshT name monad result = FreshT { runFreshT :: name -> monad (result, name) }

type Fresh name = FreshT name Identity

runFresh :: Fresh name result -> name -> (result, name)
runFresh = fmap runIdentity . runFreshT


instance Functor monad => Functor (FreshT name monad) where
  fmap f (FreshT run) = FreshT (fmap (first f) . run)

instance Monad monad => Applicative (FreshT name monad) where
  pure = FreshT . (pure .) . (,)

  (<*>) = ap

instance Monad monad => Monad (FreshT name monad) where
  return = pure

  a >>= f = FreshT (uncurry runFreshT . first f <=< runFreshT a)

instance (Enum name, Monad monad) => MonadFresh name (FreshT name monad) where
  fresh = FreshT (\ s -> pure (s, succ s))

instance MonadFresh name monad => MonadFresh name (ReaderT read monad) where
  fresh = lift fresh

instance MonadFresh name monad => MonadFresh name (StateT state monad) where
  fresh = lift fresh
