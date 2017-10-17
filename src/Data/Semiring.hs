module Data.Semiring
( zero
) where

zero :: Monoid m => m
zero = mempty
