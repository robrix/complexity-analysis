{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Data.Type where

import Control.Monad.Free
import Data.Foldable (fold)
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
freeTypeVariables = iter (\ ty -> case ty of
  TVar name        -> Set.singleton name
  ForAll name body -> Set.delete name body
  _                -> fold ty) . (Set.empty <$)

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
  substitute subst ty = iter (\ ty subst -> case ty of
    TVar name        -> fromMaybe (Free (TVar name)) (substLookup name subst)
    ForAll name body -> Free (ForAll name (body (substDelete name subst)))
    other            -> Free (($ subst) <$> other)) (const . Pure <$> ty) subst
