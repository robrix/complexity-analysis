{-# LANGUAGE FlexibleInstances #-}
module Control.Monad.Fresh where

import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (first)
import Data.FreeTypeVariables
import Data.Functor.Identity
import Data.Name
import qualified Data.Set as Set
import Data.Subst

class Monad monad => MonadFresh monad where
  fresh :: monad Name


newtype FreshT monad result = FreshT { runFreshT :: Name -> monad (result, Name) }

type Fresh = FreshT Identity

runFresh :: Fresh result -> Name -> (result, Name)
runFresh = fmap runIdentity . runFreshT


refresh :: (FreeTypeVariables value, Substitutable ty value, MonadFresh monad) => (Name -> ty) -> value -> monad value
refresh tvar value = traverse (\ name -> fresh >>= pure . (,) name . tvar) (Set.toList (freeTypeVariables value)) >>= pure . flip substitute value . Subst


instance Functor monad => Functor (FreshT monad) where
  fmap f (FreshT run) = FreshT (fmap (first f) . run)

instance Monad monad => Applicative (FreshT monad) where
  pure = FreshT . (pure .) . (,)

  (<*>) = ap

instance Monad monad => Monad (FreshT monad) where
  return = pure

  a >>= f = FreshT (uncurry runFreshT . first f <=< runFreshT a)

instance Monad monad => MonadFresh (FreshT monad) where
  fresh = FreshT (\ s -> pure (s, succ s))

instance MonadFresh monad => MonadFresh (ReaderT read monad) where
  fresh = lift fresh

instance MonadFresh monad => MonadFresh (StateT state monad) where
  fresh = lift fresh
