module Data.Rec where

import Data.Functor.Classes

newtype Rec expr a = Rec (expr a (Rec expr a))

unRec :: Rec expr a -> expr a (Rec expr a)
unRec (Rec expr) = expr

instance (Show1 (expr a), Show a) => Show (Rec expr a) where
  showsPrec d (Rec expr) = showsUnaryWith (liftShowsPrec showsPrec showList) "Rec" d expr
