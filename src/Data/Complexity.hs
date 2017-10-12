{-# LANGUAGE DeriveFoldable, DeriveFunctor #-}
module Data.Complexity where

import Control.Arrow ((&&&))
import Data.Function (fix)

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)


data Expr a
  = Abs Name a
  | App a a
  | Var Name
  | Lit Bool
  | If a a a
  deriving (Foldable, Functor)

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a

infixr 0 :->


newtype Term f = In { out :: f (Term f) }

data Attr f a = Attr { attribute :: a, hole :: f (Attr f a) }


type FAlgebra f a = f a -> a

cata :: Functor f => FAlgebra f a -> Term f -> a
cata algebra = go where go = algebra . fmap go . out

type RAlgebra f a = f (Term f, a) -> a

para :: Functor f => RAlgebra f a -> Term f -> a
para algebra = go where go = algebra . fmap (id &&& go) . out

type CVAlgebra f a = f (Attr f a) -> a

histo :: Functor f => CVAlgebra f a -> Term f -> a
histo algebra = go
  where go = algebra . fmap worker . out
        worker t = Attr (go t) (worker <$> out t)
