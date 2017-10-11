module Data.Complexity where

data Complexity
  = Constant !Int
  deriving (Eq, Ord, Read, Show)
