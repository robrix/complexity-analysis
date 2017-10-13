{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances #-}
module Data.Type where

import Control.Monad.Free
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

returnType :: PartialType a -> Maybe (PartialType a)
returnType (Free (_ :-> returnTy)) = Just returnTy
returnType (Pure err)              = Just (Pure err)
returnType _                       = Nothing

fstType :: PartialType a -> Maybe (PartialType a)
fstType (Free (fstTy :* _)) = Just fstTy
fstType (Pure err)          = Just (Pure err)
fstType _                   = Nothing

sndType :: PartialType a -> Maybe (PartialType a)
sndType (Free (_ :* sndTy)) = Just sndTy
sndType (Pure err)          = Just (Pure err)
sndType _                   = Nothing


instance Binder (PartialType a) where
  substitute subst ty = iter (\ ty subst -> case ty of
    TVar name        -> fromMaybe (Free (TVar name)) (substLookup name subst)
    ForAll name body -> Free (ForAll name (body (substDelete name subst)))
    other            -> Free (($ subst) <$> other)) (const . Pure <$> ty) subst
