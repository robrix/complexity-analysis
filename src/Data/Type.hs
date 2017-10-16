{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Type where

import Control.Comonad.Cofree
import Control.Monad.Free
import Data.Either (fromLeft)
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Recursive(..), Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import GHC.Generics

data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | a :* a
  | Unit
  | Bool
  deriving (Eq, Foldable, Functor, Generic1, Ord, Read, Show, Traversable)

infixr 0 :->
infixl 7 :*

instance Eq1 Type where liftEq = genericLiftEq
instance Ord1 Type where liftCompare = genericLiftCompare
instance Show1 Type where liftShowsPrec = genericLiftShowsPrec

data Error
  = FreeVariable Name
  | TypeMismatch (Type PartialType) (Type PartialType)
  | InfiniteType Name (Type PartialType)
  deriving (Eq, Ord, Read, Show)

type PartialType = Free Type Error
type TotalType = Fix Type

totalToPartial :: TotalType -> PartialType
totalToPartial = cata wrap

partialToTotal :: PartialType -> Either [Error] TotalType
partialToTotal = iter (fmap Fix . sequenceA) . fmap (Left . pure)


tvar :: Name -> PartialType
tvar name = wrap (TVar name)

makeForAll :: Name -> PartialType -> PartialType
makeForAll name body = wrap (ForAll name body)

forAll :: (PartialType -> PartialType) -> PartialType
forAll hoas = makeForAll n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: PartialType -> Maybe Name
maxBoundVariable = iter (\ expr -> case expr of
  ForAll name _ -> Just name
  _             -> foldr max Nothing expr) . (Nothing <$)

(.->) :: PartialType -> PartialType -> PartialType
arg .-> ret = wrap (arg :-> ret)

infixr 0 .->

(.*) :: PartialType -> PartialType -> PartialType
fst .* snd = wrap (fst :* snd)

infixl 7 .*

unit :: PartialType
unit = wrap Unit

bool :: PartialType
bool = wrap Bool


class FreeTypeVariables t where
  freeTypeVariables :: t -> Set.Set Name

instance FreeTypeVariables PartialType where
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
substType subst (fst :* snd)       = Left (substitute subst fst :* substitute subst snd)
substType _     Unit               = Left Unit
substType _     Bool               = Left Bool

instance Binder PartialType PartialType where
  substitute subst (Free t) = either wrap id (substType subst t)
  substitute subst (Pure a) = Pure (substitute subst a)

instance Binder PartialType Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Functor f => Binder PartialType (Cofree f PartialType) where
  substitute subst (a :< f) = substitute subst a :< fmap (substitute subst) f
