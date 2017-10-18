{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Name where

newtype Name = Name Int
  deriving (Enum, Eq, Ord, Show)

unName :: Name -> Int
unName (Name n) = n
