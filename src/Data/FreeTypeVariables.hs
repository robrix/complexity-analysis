{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Data.FreeTypeVariables where

import qualified Data.Set as Set

class FreeTypeVariables name t where
  freeTypeVariables :: t -> Set.Set name

instance FreeTypeVariables name (Set.Set name) where
  freeTypeVariables = id
