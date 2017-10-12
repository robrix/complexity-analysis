module Data.Complexity where

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  | ForAll Name (Complexity i)
  | CVar Name
  | Complexity i :* Complexity i
  | Complexity i :-> Complexity i
  deriving (Eq, Ord, Read, Show)

infixr 9 :->
