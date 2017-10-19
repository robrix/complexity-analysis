{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Data.Context where

import Data.Name
import Data.Semigroup

newtype Context a = Context { getContext :: [(Name, a)] }
  deriving (Eq, Foldable, Functor, Monoid, Ord, Semigroup, Show, Traversable)

-- | Lookup a value in an 'Context' by 'Name'.
--
-- prop> \ name -> envLookup name mempty == Nothing
contextLookup :: Name -> Context a -> Maybe a
contextLookup name = lookup name . getContext

contextExtend :: Name -> a -> Context a -> Context a
contextExtend name value = Context . ((name, value) :) . getContext


-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
