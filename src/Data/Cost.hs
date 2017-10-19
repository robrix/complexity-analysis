module Data.Cost where

import Data.Name

data Cost
  = Const Int
  | CVar Name
  deriving (Eq, Ord, Read, Show)
