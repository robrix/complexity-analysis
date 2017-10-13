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

tvar :: Name -> Free Type a
tvar name = wrap (TVar name)

makeForAll :: Name -> Free Type a -> Free Type a
makeForAll name body = wrap (ForAll name body)

(.->) :: Free Type a -> Free Type a -> Free Type a
arg .-> ret = wrap (arg :-> ret)

infixr 0 .->

(.*) :: Free Type a -> Free Type a -> Free Type a
fst .* snd = wrap (fst :* snd)

infixl 7 .*

bool :: Free Type a
bool = wrap Bool


class FreeTypeVariables t where
  freeTypeVariables :: t -> Set.Set Name

instance FreeTypeVariables (Free Type a) where
  freeTypeVariables = iter (\ ty -> case ty of
    TVar name        -> Set.singleton name
    ForAll name body -> Set.delete name body
    _                -> fold ty) . (Set.empty <$)

instance FreeTypeVariables t => FreeTypeVariables (Type t) where
  freeTypeVariables (TVar name)        = Set.singleton name
  freeTypeVariables (ForAll name body) = Set.delete name (freeTypeVariables body)
  freeTypeVariables ty                 = foldMap freeTypeVariables ty

instance FreeTypeVariables (Set.Set Name) where
  freeTypeVariables = id

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
