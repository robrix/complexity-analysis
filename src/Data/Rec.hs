module Data.Rec where

import Data.Functor.Classes

newtype Rec expr a = Rec (expr a (Rec expr a))

unRec :: Rec expr a -> expr a (Rec expr a)
unRec (Rec expr) = expr

instance (Eq1 (expr a), Eq a) => Eq (Rec expr a) where
  Rec expr1 == Rec expr2 = liftEq (==) expr1 expr2

instance (Ord1 (expr a), Ord a) => Ord (Rec expr a) where
  compare (Rec expr1) (Rec expr2) = liftCompare compare expr1 expr2

instance (Show1 (expr a), Show a) => Show (Rec expr a) where
  showsPrec d (Rec expr) = showsUnaryWith (liftShowsPrec showsPrec showList) "Rec" d expr
