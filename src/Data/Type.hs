{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Type where

import Control.Monad.Free
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import GHC.Generics

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | Bool
  | a :* a
  deriving (Eq, Foldable, Functor, Generic1, Ord, Read, Show, Traversable)

infixr 0 :->
infixl 7 :*

instance Eq1 Type where liftEq = genericLiftEq
instance Ord1 Type where liftCompare = genericLiftCompare
instance Show1 Type where liftShowsPrec = genericLiftShowsPrec

type PartialType = Free Type
type TotalType = Fix Type

partialToTotal :: PartialType a -> Either [a] TotalType
partialToTotal = iter (fmap Fix . sequenceA) . fmap (Left . pure)


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


substType :: Binder a a => Subst a -> Type a -> Either (Type a) a
substType subst (TVar name)        = maybe (Left (TVar name)) Right (substLookup name subst)
substType subst (ForAll name body) = Left (ForAll name (substitute (substDelete name subst) body))
substType subst (arg :-> ret)      = Left (substitute subst arg :-> substitute subst ret)
substType _     Bool               = Left Bool
substType subst (fst :* snd)       = Left (substitute subst fst :* substitute subst snd)

instance Binder (PartialType a) a => Binder (PartialType a) (PartialType a) where
  substitute subst (Free t) = either wrap id (substType subst t)
  substitute subst (Pure a) = Pure (substitute subst a)
