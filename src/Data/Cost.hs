{-# LANGUAGE DeriveGeneric #-}
module Data.Cost where

import Data.Name
import Data.Semigroup
import GHC.Generics

data Cost
  = Const Int
  | CVar Name
  | Plus Cost Cost
  | Times Cost Cost
  deriving (Eq, Generic, Ord, Show)

instance Semigroup Cost where
  (<>) = Plus
