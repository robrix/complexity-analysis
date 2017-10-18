module Data.Rec where

newtype Rec f a = Rec (f a (Rec f a))
