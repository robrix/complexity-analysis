{-# LANGUAGE FlexibleInstances, FunctionalDependencies, PolyKinds, TypeFamilies #-}
module Data.Rec where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Data.Functor.Foldable (Base, Corecursive(..), Recursive(..), Fix(..))

newtype Rec expr a = Rec (expr a (Rec expr a))

unRec :: Rec expr a -> expr a (Rec expr a)
unRec (Rec expr) = expr


class Embeddable f t | t -> f where
  emb :: f t -> t

  withEmb :: (f t -> b) -> t -> Maybe b

class Embeddable1 f t | t -> f where
  emb1 :: f a -> t a

  withEmb1 :: (f a -> b) -> t a -> Maybe b

instance Embeddable f (Fix f) where
  emb = Fix

  withEmb f (Fix expr) = Just (f expr)

instance Embeddable1 expr (wrap expr a) => Embeddable expr (Rec (wrap expr) a) where
  emb = Rec . emb1

  withEmb f = withEmb1 f . unRec


instance (Eq1 (expr a), Eq a) => Eq (Rec expr a) where
  Rec expr1 == Rec expr2 = liftEq (==) expr1 expr2

instance (Ord1 (expr a), Ord a) => Ord (Rec expr a) where
  compare (Rec expr1) (Rec expr2) = liftCompare compare expr1 expr2

instance (Show1 (expr a), Show a) => Show (Rec expr a) where
  showsPrec d (Rec expr) = showsUnaryWith (liftShowsPrec showsPrec showList) "Rec" d expr

instance Bifunctor expr => Functor (Rec expr) where
  fmap f = go where go = Rec . bimap f go . unRec

instance Bifoldable expr => Foldable (Rec expr) where
  foldMap f = go where go = bifoldMap f go . unRec

instance Bitraversable expr => Traversable (Rec expr) where
  traverse f = go where go = fmap Rec . bitraverse f go . unRec

type instance Base (Rec expr a) = expr a

instance Functor (expr a) => Recursive   (Rec expr a) where project = unRec
instance Functor (expr a) => Corecursive (Rec expr a) where embed   = Rec
