{-# LANGUAGE FlexibleInstances #-}
module Data.FreeTypeVariables where

import Data.Name
import qualified Data.Set as Set

class FreeTypeVariables t where
  freeTypeVariables :: t -> Set.Set Name

instance FreeTypeVariables (Set.Set Name) where
  freeTypeVariables = id
