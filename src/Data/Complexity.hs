module Data.Complexity where

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  | CVar Name
  | Complexity i :* Complexity i
  deriving (Eq, Ord, Read, Show)
