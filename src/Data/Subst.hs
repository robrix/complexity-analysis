{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Subst where

import Data.Bifunctor (second)
import Data.Function (on)
import qualified Data.List as List
import Data.Name
import Data.Semigroup (Semigroup(..))

newtype Subst value = Subst { getSubst :: [(Name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance Binder value value => Semigroup (Subst value) where
  Subst s1 <> Subst s2 = Subst (List.unionBy ((==) `on` fst) (map (second (substitute (Subst s1))) s2) s1)

instance Binder value value => Monoid (Subst value) where
  mempty = Subst []
  mappend = (<>)

substLookup :: Name -> Subst value -> Maybe value
substLookup name = lookup name . getSubst

substDelete :: Name -> Subst value -> Subst value
substDelete name = Subst . filter ((/= name) . fst) . getSubst

substSingleton :: Name -> value -> Subst value
substSingleton name value = Subst [(name, value)]

substExtend :: Binder value value => Name -> value -> Subst value -> Subst value
substExtend name value = (<> substSingleton name value)


class Binder ty value where
  substitute :: Subst ty -> value -> value

instance Binder ty ty => Binder ty (Subst ty) where
  substitute subst = Subst . map (second (substitute subst)) . getSubst
