{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Module where

import Data.Semigroup
import Data.Semiring

class (Monoid m, Semigroup m, Semiring r) => Module r m where
