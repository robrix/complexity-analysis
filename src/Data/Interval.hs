module Data.Interval where

data Interval a = Interval {-# UNPACK #-} !a {-# UNPACK #-} !a
  deriving (Eq, Ord, Read, Show)
