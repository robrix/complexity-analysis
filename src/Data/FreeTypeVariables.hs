{-# LANGUAGE FlexibleInstances #-}
module Data.FreeTypeVariables where

import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set

class FreeTypeVariables t where
  freeTypeVariables :: t -> Set.Set Name

class FreeTypeVariables1 t where
  liftFreeTypeVariables :: (a -> Set.Set Name) -> t a -> Set.Set Name

freeTypeVariables1 :: (FreeTypeVariables1 f, FreeTypeVariables a) => f a -> Set.Set Name
freeTypeVariables1 = liftFreeTypeVariables freeTypeVariables


instance FreeTypeVariables (Set.Set Name) where
  freeTypeVariables = liftFreeTypeVariables Set.singleton

instance FreeTypeVariables1 Set.Set where
  liftFreeTypeVariables = foldMap

instance FreeTypeVariables1 ty => FreeTypeVariables (Fix ty) where
  freeTypeVariables (Fix ty) = freeTypeVariables1 ty
