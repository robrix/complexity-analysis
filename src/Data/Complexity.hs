module Data.Complexity where

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)
