{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Data.Module where

import Data.Semigroup
import Data.Semiring

class (Monoid m, Semigroup m, Semiring r) => Module r m where
  (><<) :: r -> m -> m

  infixl 7 ><<

instance Semiring r => Module r [r] where
  _ ><< []     = []
  r ><< (x:xs) = r >< x : r ><< xs
