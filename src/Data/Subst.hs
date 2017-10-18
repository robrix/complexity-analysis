{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Subst where

import Data.Bifunctor (second)
import Data.Functor.Foldable (Fix(..))
import Data.Name
import Data.Semigroup (Semigroup(..))

newtype Subst value = Subst { getSubst :: [(Name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Substitution composition.
--
-- >>> import Data.Type
-- >>> let s1 = substSingleton (Name 0) (unitT :: Partial Type Error)
-- >>> let s2 = substSingleton (Name 1) boolT
-- >>> let s3 = substSingleton (Name 2) (tvar (Name 0) .* tvar (Name 1))
-- >>> let t = tvar (Name 0) .-> tvar (Name 1) .-> tvar (Name 2) :: Partial Type Error
-- >>> s1 <> (s2 <> s3) == (s1 <> s2) <> s3
-- True
-- >>> substitute (s1 <> s2 <> s3) t == foldr substitute t [ s1, s2, s3 ]
-- True
-- >>> substitute (s1 <> s2 <> s3) t
-- Continue (Continue Unit :-> Continue (Continue Bool :-> Continue (Continue Unit :* Continue Bool)))
instance Substitutable value value => Semigroup (Subst value) where
  s1 <> s2 = Subst (getSubst s1 ++ getSubst (substitute s1 s2))

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

substVars :: Subst a -> [Name]
substVars = map fst . getSubst


class Substitutable ty value where
  substitute :: Subst ty -> value -> value

class Substitutable1 ty value where
  liftSubstitute :: (Subst ty -> recur -> recur) -> Subst ty -> value recur -> value recur

instance Substitutable ty ty => Substitutable ty (Subst ty) where
  substitute subst = Subst . map (second (substitute subst)) . filter (flip notElem vars . fst) . getSubst
    where vars = substVars subst

instance Substitutable1 ty expr => Substitutable ty (Fix expr) where
  substitute subst (Fix expr) = Fix (liftSubstitute substitute subst expr)
