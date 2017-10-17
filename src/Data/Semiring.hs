module Data.Semiring
( zero
, Semigroup(..)
) where

import Data.Semigroup

zero :: Monoid m => m
zero = mempty
