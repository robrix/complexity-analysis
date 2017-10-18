module Data.Rec where

newtype Rec expr a = Rec (expr a (Rec expr a))
