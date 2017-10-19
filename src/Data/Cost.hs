{-# LANGUAGE DeriveGeneric #-}
module Data.Cost where

import Data.Name
import Data.Semigroup
import Data.Semiring (Semiring(..))
import GHC.Generics

data Cost
  = Zero
  | One
  | CVar Name
  | Plus Cost Cost
  | Times Cost Cost
  deriving (Eq, Generic, Ord, Show)

instance Semigroup Cost where
  (<>) = Plus

instance Monoid Cost where
  mempty = Zero
  mappend = (<>)

instance Semiring Cost where
  one = One
  (><) = Times
