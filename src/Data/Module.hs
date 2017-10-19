{-# LANGUAGE DeriveTraversable, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Data.Module where

import Data.Align
import Data.Semigroup
import Data.Semiring

class (Monoid m, Semigroup m, Semiring r) => Module r m where
  (><<) :: r -> m -> m

  infixl 7 ><<

instance Semiring r => Module r [r] where
  _ ><< []     = []
  r ><< (x:xs) = r >< x : r ><< xs


newtype Pointwise a = Pointwise { unPointwise :: [a] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Semigroup a => Semigroup (Pointwise a) where
  Pointwise (a : as) <> Pointwise (b : bs) = Pointwise (a <> b : as <> bs)
  Pointwise [] <> Pointwise bs = Pointwise bs
  Pointwise as <> Pointwise [] = Pointwise as

instance Align Pointwise where
  nil = Pointwise []
  alignWith f (Pointwise as) (Pointwise bs) = Pointwise (alignWith f as bs)
