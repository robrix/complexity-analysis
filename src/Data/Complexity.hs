module Data.Complexity where

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  | CVar Name
  deriving (Eq, Ord, Read, Show)
