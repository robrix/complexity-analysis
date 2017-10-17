{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
module Data.FreeTypeVariables where

import qualified Data.Set as Set

class FreeTypeVariables name t | t -> name where
  freeTypeVariables :: t -> Set.Set name

instance FreeTypeVariables name (Set.Set name) where
  freeTypeVariables = id
