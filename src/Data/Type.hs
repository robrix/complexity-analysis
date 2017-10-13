{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Data.Type where

import Control.Monad.Free
import qualified Control.Monad.Trans.Free as F
import Data.Foldable (fold)
import Data.Functor.Foldable (Recursive(..))
import Data.Name
import qualified Data.Set as Set

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | Bool
  | a :* a
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

infixr 0 :->
infixl 7 :*

freeTypeVariables :: Free Type a -> Set.Set Name
freeTypeVariables = cata $ \ ty -> case ty of
  F.Free (TVar name)        -> Set.singleton name
  F.Free (ForAll name body) -> Set.delete name body
  _                         -> fold ty

returnType :: Free Type a -> Maybe (Free Type a)
returnType (Free (_ :-> returnTy)) = Just returnTy
returnType (Pure err)              = Just (Pure err)
returnType _                       = Nothing

fstType :: Free Type a -> Maybe (Free Type a)
fstType (Free (fstTy :* _)) = Just fstTy
fstType (Pure err)          = Just (Pure err)
fstType _                   = Nothing

sndType :: Free Type a -> Maybe (Free Type a)
sndType (Free (_ :* sndTy)) = Just sndTy
sndType (Pure err)          = Just (Pure err)
sndType _                   = Nothing
