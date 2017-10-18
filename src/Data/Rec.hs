module Data.Rec where

newtype Rec expr a = Rec (expr a (Rec expr a))

unRec :: Rec expr a -> expr a (Rec expr a)
unRec (Rec expr) = expr
