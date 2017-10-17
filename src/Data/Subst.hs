{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Subst where

import Data.Bifunctor (second)
import Data.Function (on)
import qualified Data.List as List
import Data.Name
import Data.Semigroup (Semigroup(..))

newtype Subst value = Subst { getSubst :: [(Name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance Substitutable value value => Semigroup (Subst value) where
  s1 <> s2 = Subst (List.unionBy ((==) `on` fst) (getSubst (substitute s1 s2)) (getSubst s1))

instance Substitutable value value => Monoid (Subst value) where
  mempty = Subst []
  mappend = (<>)

substLookup :: Name -> Subst value -> Maybe value
substLookup name = lookup name . getSubst

substDelete :: Name -> Subst value -> Subst value
substDelete name = Subst . filter ((/= name) . fst) . getSubst

substSingleton :: Name -> value -> Subst value
substSingleton name value = Subst [(name, value)]

substExtend :: Substitutable value value => Name -> value -> Subst value -> Subst value
substExtend name value = (substSingleton name value <>)


class Substitutable ty value where
  substitute :: Subst ty -> value -> value

instance Substitutable ty ty => Substitutable ty (Subst ty) where
  substitute subst = Subst . map (second (substitute subst)) . getSubst
