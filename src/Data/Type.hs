{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Type where

import Control.Comonad.Cofree
import Control.Monad.Free
import Data.Either (fromLeft)
import Data.FreeTypeVariables
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
  | Unit
  | a :* a
  | Bool
  | List a
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

forAllT :: (PartialType -> PartialType) -> PartialType
forAllT hoas = makeForAll n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: PartialType -> Maybe Name
maxBoundVariable = iter (\ expr -> case expr of
  ForAll name _ -> Just name
  _             -> foldr max Nothing expr) . (Nothing <$)

-- | Generalize a type by binding its free variables with foralls.
--
-- >>> generalize unitT
-- Free Unit
--
-- prop> \ v -> generalize (tvar v .-> tvar v) == forAllT (\ t -> t .-> t)
generalize :: PartialType -> PartialType
generalize ty = foldr (\ v ty -> forAllT (\ new -> substitute (substSingleton v new) ty)) ty (Set.toList (freeTypeVariables ty))

(.->) :: PartialType -> PartialType -> PartialType
arg .-> ret = wrap (arg :-> ret)

infixr 0 .->

unitT :: PartialType
unitT = wrap Unit

(.*) :: PartialType -> PartialType -> PartialType
fst .* snd = wrap (fst :* snd)

infixl 7 .*

tupleT :: [PartialType] -> PartialType
tupleT = foldr (.*) unitT

boolT :: PartialType
boolT = wrap Bool

listT :: PartialType -> PartialType
listT = wrap . List


instance FreeTypeVariables PartialType where
  freeTypeVariables = iter freeTypeVariables . (Set.empty <$)

instance FreeTypeVariables t => FreeTypeVariables (Type t) where
  freeTypeVariables (TVar name)        = Set.singleton name
  freeTypeVariables (ForAll name body) = Set.delete name (freeTypeVariables body)
  freeTypeVariables ty                 = foldMap freeTypeVariables ty


substType :: Substitutable a a => Subst a -> Type a -> Either (Type a) a
substType subst (TVar name)        = maybe (Left (TVar name)) Right (substLookup name subst)
substType subst (ForAll name body) = Left (ForAll name (substitute (substDelete name subst) body))
substType subst (arg :-> ret)      = Left (substitute subst arg :-> substitute subst ret)
substType _     Unit               = Left Unit
substType subst (fst :* snd)       = Left (substitute subst fst :* substitute subst snd)
substType _     Bool               = Left Bool
substType subst (List a)           = Left (List (substitute subst a))

instance Substitutable PartialType PartialType where
  substitute subst (Free t) = either wrap id (substType subst t)
  substitute subst (Pure a) = Pure (substitute subst a)

instance Substitutable PartialType Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Functor f => Substitutable PartialType (Cofree f PartialType) where
  substitute subst (a :< f) = substitute subst a :< fmap (substitute subst) f

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
