{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Data.Env where

import Data.Name
import Data.Semigroup

newtype Env a = Env { getEnv :: [(Name, a)] }
  deriving (Eq, Foldable, Functor, Monoid, Ord, Semigroup, Show, Traversable)

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary

-- | Lookup a value in an 'Env' by 'Name'.
--
-- prop> \ name -> envLookup name mempty == Nothing
envLookup :: Name -> Env a -> Maybe a
envLookup name = lookup name . getEnv

envExtend :: Name -> a -> Env a -> Env a
envExtend name value = Env . ((name, value) :) . getEnv
