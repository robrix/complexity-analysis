{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Data.Context where

import Data.Align
import Data.Name
import Data.Semigroup
import Data.These

newtype Context a = Context { getContext :: [(Name, a)] }
  deriving (Eq, Foldable, Functor, Monoid, Ord, Semigroup, Show, Traversable)

-- | Lookup a value in an 'Context' by 'Name'.
--
-- prop> \ name -> envLookup name mempty == Nothing
contextLookup :: Name -> Context a -> Maybe a
contextLookup name = lookup name . getContext

contextExtend :: Name -> a -> Context a -> Context a
contextExtend name value = Context . ((name, value) :) . getContext

contextFindDelete :: Name -> Context a -> (Maybe a, Context a)
contextFindDelete name = go
  where go (Context ((name', value) : rest))
          | name == name' = (Just value, Context rest)
          | otherwise     = let (found, Context rest') = go (Context rest) in (found, Context ((name', value) : rest'))
        go (Context []) = (Nothing, Context [])

instance Align Context where
  nil = Context []

  alignWith f = go
    where go as bs
            | Context [] <- bs   = f . This <$> as
            | Context [] <- as   = f . That <$> bs
            | Context ((k, a):as') <- as
            , (found, bs') <- contextFindDelete k bs
            = Context ((k, f (maybe (This a) (These a) found)) : getContext (go (Context as') bs'))


-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
