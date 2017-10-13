{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Env where

import Data.Name
import Data.Semigroup

newtype Env a = Env { getEnv :: [(Name, a)] }
  deriving (Eq, Monoid, Ord, Read, Semigroup, Show)

envLookup :: Name -> Env a -> Maybe a
envLookup name = lookup name . getEnv

envExtend :: Name -> a -> Env a -> Env a
envExtend name value = Env . ((name, value) :) . getEnv
