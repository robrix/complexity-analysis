{-# LANGUAGE DeriveFoldable, DeriveFunctor #-}
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

infixl 7 :*
infixr 9 :->

data Expr a
  = Abs Name a
  | App a a
  | Var Name
  deriving (Foldable, Functor)

newtype Term = In { out :: Expr Term }

data Attr a = Attr { attribute :: a, hole :: Expr (Attr a) }

cata :: (Expr a -> a) -> Term -> a
cata algebra = go where go = algebra . fmap go . out
