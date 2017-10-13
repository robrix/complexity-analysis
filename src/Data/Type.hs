{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Data.Type where

import Control.Monad.Free
import qualified Control.Monad.Trans.Free as F
import Data.Foldable (fold)
import Data.Functor.Foldable (Recursive(..))
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


instance Binder (Free Type a) where
  substitute = flip (cata (\ ty subst -> case ty of
    F.Free (TVar name)        -> fromMaybe (Free (TVar name)) (substLookup name subst)
    F.Free (ForAll name body) -> Free (ForAll name (body (substDelete name subst)))
    F.Free other              -> Free (($ subst) <$> other)
    F.Pure err                -> Pure err))
