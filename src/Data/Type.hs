{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Data.Type where

import Control.Monad.Free
import Data.Functor.Foldable (Fix)
import Data.Maybe (fromMaybe)
import Data.Name
import qualified Data.Set as Set
import Data.Subst

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | Bool
  | a :* a
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

type PartialType = Free Type
type TotalType = Fix Type

infixr 0 :->
infixl 7 :*

tvar :: Name -> PartialType a
tvar name = wrap (TVar name)

makeForAll :: Name -> PartialType a -> PartialType a
makeForAll name body = wrap (ForAll name body)

(.->) :: PartialType a -> PartialType a -> PartialType a
arg .-> ret = wrap (arg :-> ret)

infixr 0 .->

(.*) :: PartialType a -> PartialType a -> PartialType a
fst .* snd = wrap (fst :* snd)

infixl 7 .*

bool :: PartialType a
bool = wrap Bool


class FreeTypeVariables t where
  freeTypeVariables :: t -> Set.Set Name

instance FreeTypeVariables (PartialType a) where
  freeTypeVariables = iter freeTypeVariables . (Set.empty <$)

instance FreeTypeVariables t => FreeTypeVariables (Type t) where
  freeTypeVariables (TVar name)        = Set.singleton name
  freeTypeVariables (ForAll name body) = Set.delete name (freeTypeVariables body)
  freeTypeVariables ty                 = foldMap freeTypeVariables ty

instance FreeTypeVariables (Set.Set Name) where
  freeTypeVariables = id


instance Binder (PartialType a) where
  substitute subst ty = iter (\ ty subst -> case ty of
    TVar name        -> fromMaybe (Free (TVar name)) (substLookup name subst)
    ForAll name body -> Free (ForAll name (body (substDelete name subst)))
    other            -> Free (($ subst) <$> other)) (const . Pure <$> ty) subst
