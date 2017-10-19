module Data.Cost where

data Complexity i
  = Const Int
  deriving (Eq, Ord, Read, Show)
