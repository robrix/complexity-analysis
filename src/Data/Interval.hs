module Data.Interval where

data Interval a = Interval !a !a
  deriving (Eq, Ord, Read, Show)
