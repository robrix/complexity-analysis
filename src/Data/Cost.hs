module Data.Cost where

import Data.Name

data Cost
  = Const Int
  | CVar Name
  | Plus Cost Cost
  | Times Cost Cost
  deriving (Eq, Ord, Show)
