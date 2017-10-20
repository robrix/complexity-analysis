{-# LANGUAGE DeriveGeneric #-}
module Data.Cost where

import Data.Name
import Data.Semigroup
import Data.Semiring (Semiring(..))
import GHC.Generics

data Cost
  = Const Integer
  | CVar Name
  | Plus Cost Cost
  | Times Cost Cost
  deriving (Eq, Generic, Ord, Show)

instance Semigroup Cost where
  (<>) = Plus

instance Monoid Cost where
  mempty = Const 0
  mappend = (<>)

instance Semiring Cost where
  one = Const 1
  a       >< Const 1 = a
  Const 1 >< b       = b
  a       >< b       = Times a b
