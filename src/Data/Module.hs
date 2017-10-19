{-# LANGUAGE DeriveTraversable, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Data.Module where

import Data.Align
import Data.Semigroup
import Data.Semiring
import Data.These

class (Monoid m, Semigroup m, Semiring r) => Module r m where
  (><<) :: r -> m -> m

  infixl 7 ><<

instance Semiring r => Module r [r] where
  (><<) = fmap . (><)


newtype Pointwise a = Pointwise { unPointwise :: [a] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup a => Semigroup (Pointwise a) where
  (<>) = alignWith (mergeThese (<>))

instance Monoid a => Monoid (Pointwise a) where
  mempty = Pointwise []
  mappend = alignWith (mergeThese mappend)

instance Semiring r => Module r (Pointwise r) where
  (><<) = fmap . (><)

instance Align Pointwise where
  nil = Pointwise []
  alignWith f (Pointwise as) (Pointwise bs) = Pointwise (alignWith f as bs)