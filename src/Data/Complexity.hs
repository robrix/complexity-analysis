{-# LANGUAGE DeriveFoldable, DeriveFunctor #-}
module Data.Complexity where

import Control.Arrow ((&&&))

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

newtype Term f = In { out :: f (Term f) }

data Attr f a = Attr { attribute :: a, hole :: f (Attr f a) }

type FAlgebra f a = f a -> a
type RAlgebra f a = f (Term f, a) -> a

cata :: Functor f => FAlgebra f a -> Term f -> a
cata algebra = go where go = algebra . fmap go . out

para :: Functor f => RAlgebra f a -> Term f -> a
para algebra = go where go = algebra . fmap (id &&& go) . out
