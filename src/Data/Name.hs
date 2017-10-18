{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Name
( Name(..)
, unName
, prettyName
) where

newtype Name = Name Int
  deriving (Enum, Eq, Ord, Show)

unName :: Name -> Int
unName (Name n) = n


prettyName :: Int -> Name -> ShowS
prettyName _ = alpha . unName
  where alpha n | n < 0     = showString ""
                | otherwise = let (next, place) = (n `divMod` alphabetLength) in
                  alpha (pred next) . showChar (alphabet !! place)

alphabet :: String
alphabet = ['a'..'z']

alphabetLength :: Int
alphabetLength = length alphabet
