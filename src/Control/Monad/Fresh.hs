{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Control.Monad.Fresh where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (first)
import Data.Functor.Identity
import Data.Name

class Monad monad => MonadFresh monad where
  fresh :: monad Name


newtype FreshT monad result = FreshT { runFreshT :: Name -> monad (result, Name) }

type Fresh = FreshT Identity

runFresh :: Fresh result -> Name -> (result, Name)
runFresh = fmap runIdentity . runFreshT


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

instance MonadTrans FreshT where
  lift m = FreshT (flip fmap m . flip (,))

instance MonadError error monad => MonadError error (FreshT monad) where
  throwError = lift . throwError
  catchError body handler = FreshT (\ s -> catchError (runFreshT body s) (flip runFreshT s . handler))
