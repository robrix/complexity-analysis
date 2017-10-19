{-# LANGUAGE DeriveTraversable, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Data.Module where

import Data.Align
import Data.Semigroup
import Data.Semiring
import Data.These

-- | A (left) module over some 'Semiring' @r@.
class (Monoid m, Semigroup m, Semiring r) => Module r m where
  -- | Multiply a module by a scalar (on the left).
  --
  --   Laws:
  --
  --   The 'Semigroup' laws (associativity of '(<>)' & equality of '(<>)' and 'mappend'):
  --
  --   > x <> (y <> z) = (x <> y) <> z
  --   > (<>) = mappend
  --
  --   The 'Monoid' laws ('zero' is the left- and right-identity of '(<>)'):
  --
  --   > zero <> x = x
  --   > x <> zero = x
  --
  --   'one' is the left-identity of '(><<)':
  --
  --   > one ><< x = x
  --
  --   '(><<)' is left-distributive over 'Module' '(<>)':
  --
  --   > r ><< (x <> y) = (r ><< x) <> (r ><< y)
  --
  --   '(><<)' is right-distributive over 'Semiring' '(<>)':
  --
  --   > (r <> s) ><< x = (r ><< x) <> (s ><< x)
  --
  --   '(><<)' is right-distributive over 'Semiring' '(><)':
  --
  --   > r >< s ><< x = r ><< (s ><< x)
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
