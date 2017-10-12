{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Data.Complexity where

import Control.Arrow ((&&&))

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
  deriving (Foldable, Functor, Traversable)

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | Bool
  deriving (Foldable, Functor, Traversable)

infixr 0 :->


newtype Term f = In { out :: f (Term f) }

data Attr f a = Attr { attribute :: a, hole :: f (Attr f a) }

data CoAttr f a
  = Stop a
  | Continue (f (CoAttr f a))


type Env a = [(Name, a)]
type Error = String
type Result = Either Error


type FAlgebra f a = f a -> a

cata :: Functor f => FAlgebra f a -> Term f -> a
cata algebra = go where go = algebra . fmap go . out

type FCoalgebra f a = a -> f a

ana :: Functor f => FCoalgebra f a -> a -> Term f
ana coalgebra = go where go = In . fmap go . coalgebra

type RAlgebra f a = f (Term f, a) -> a

para :: Functor f => RAlgebra f a -> Term f -> a
para algebra = go where go = algebra . fmap (id &&& go) . out

type RCoalgebra f a = a -> f (Either (Term f) a)

apo :: Functor f => RCoalgebra f a -> a -> Term f
apo coalgebra = go where go = In . fmap (either id go) . coalgebra

type CVAlgebra f a = f (Attr f a) -> a

histo :: Functor f => CVAlgebra f a -> Term f -> a
histo algebra = go
  where go = algebra . fmap worker . out
        worker t = Attr (go t) (worker <$> out t)

type CVCoalgebra f a = a -> f (CoAttr f a)

futu :: Functor f => CVCoalgebra f a -> a -> Term f
futu coalgebra = go
  where go = In . fmap worker . coalgebra
        worker (Stop a)     = go a
        worker (Continue f) = In (fmap worker f)
