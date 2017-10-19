{-# LANGUAGE FlexibleInstances #-}
module Data.FreeVariables where

import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set

class FreeVariables t where
  freeVariables :: t -> Set.Set Name

class FreeVariables1 t where
  liftFreeVariables :: (a -> Set.Set Name) -> t a -> Set.Set Name

freeVariables1 :: (FreeVariables1 f, FreeVariables a) => f a -> Set.Set Name
freeVariables1 = liftFreeVariables freeVariables


instance FreeVariables (Set.Set Name) where
  freeVariables = liftFreeVariables Set.singleton

instance FreeVariables1 Set.Set where
  liftFreeVariables = foldMap

instance FreeVariables1 ty => FreeVariables (Fix ty) where
  freeVariables (Fix ty) = freeVariables1 ty
