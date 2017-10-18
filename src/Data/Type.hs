{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
module Data.Type where

import Data.Either (fromLeft)
import Data.FreeTypeVariables
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Base, Fix(..), Recursive(..))
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
  | TypeMismatch (Type (Partial Type Error)) (Type (Partial Type Error))
  | InfiniteType Name (Type (Partial Type Error))
  deriving (Eq, Ord, Read, Show)

type Total = Fix


data Partial expr error = Continue (expr (Partial expr error)) | Stop error
deriving instance (Eq   (f (Partial f a)), Eq   a) => Eq   (Partial f a)
deriving instance (Ord  (f (Partial f a)), Ord  a) => Ord  (Partial f a)
deriving instance (Read (f (Partial f a)), Read a) => Read (Partial f a)
deriving instance (Show (f (Partial f a)), Show a) => Show (Partial f a)

data PartialF expr error recur = ContinueF (expr recur) | StopF error
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance (Eq1   expr, Eq   ann) => Eq1   (PartialF expr ann) where liftEq        = genericLiftEq
instance (Ord1  expr, Ord  ann) => Ord1  (PartialF expr ann) where liftCompare   = genericLiftCompare
instance (Show1 expr, Show ann) => Show1 (PartialF expr ann) where liftShowsPrec = genericLiftShowsPrec

type instance Base (Partial expr error) = PartialF expr error

instance Functor expr => Recursive (Partial expr error) where
  project (Continue expr) = ContinueF expr
  project (Stop err)      = StopF err


totalToPartial :: Total Type -> Partial Type error
totalToPartial = cata Continue

partialToTotal :: Partial Type error -> Either [error] (Total Type)
partialToTotal = cata (\ partial -> case partial of
  ContinueF expr -> fmap Fix (sequenceA expr)
  StopF err      -> Left [err])


tvar :: Name -> Partial Type error
tvar name = Continue (TVar name)

makeForAllT :: Name -> Partial Type error -> Partial Type error
makeForAllT name body = Continue (ForAll name body)

forAllT :: (Partial Type error -> Partial Type error) -> Partial Type error
forAllT hoas = makeForAllT n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: Partial Type error -> Maybe Name
maxBoundVariable = cata (\ partial -> case partial of
  ContinueF (ForAll name _) -> Just name
  ContinueF expr            -> foldr max Nothing expr
  StopF _                   -> Nothing)

-- | Generalize a type by binding its free variables with foralls.
--
-- >>> generalize unitT :: Partial Type Error
-- Continue Unit
--
-- prop> \ v -> generalize (tvar v .-> tvar v) == forAllT (\ t -> t .-> t :: Partial Type Error)
generalize :: Substitutable (Partial Type error) error => Partial Type error -> Partial Type error
generalize ty = foldr (\ v ty -> forAllT (\ new -> substitute (substSingleton v new) ty)) ty (Set.toList (freeTypeVariables ty))

specialize :: forall error . Substitutable (Partial Type error) error => Type (Partial Type error) -> Name -> Partial Type error
specialize (ForAll n b) to = substitute (substSingleton n (tvar to) :: Subst (Partial Type error)) b
specialize orig         _  = Continue orig

(.->) :: Partial Type error -> Partial Type error -> Partial Type error
arg .-> ret = Continue (arg :-> ret)

infixr 0 .->

unitT :: Partial Type error
unitT = Continue Unit

(.*) :: Partial Type error -> Partial Type error -> Partial Type error
fst .* snd = Continue (fst :* snd)

infixl 7 .*

tupleT :: [Partial Type error] -> Partial Type error
tupleT = foldr (.*) unitT

boolT :: Partial Type error
boolT = Continue Bool

listT :: Partial Type error -> Partial Type error
listT = Continue . List


instance FreeTypeVariables (Partial Type error) where
  freeTypeVariables = cata freeTypeVariables . ((Set.empty :: Set.Set Name) <$)

instance (FreeTypeVariables (expr recur), FreeTypeVariables error) => FreeTypeVariables (PartialF expr error recur) where
  freeTypeVariables (ContinueF expr) = freeTypeVariables expr
  freeTypeVariables (StopF err)      = freeTypeVariables err

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

instance Substitutable (Partial Type error) error => Substitutable (Partial Type error) (Partial Type error) where
  substitute subst (Continue expr) = either Continue id (substType subst expr)
  substitute subst (Stop err)      = Stop (substitute subst err)

instance Substitutable (Partial Type Error) Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Functor expr => Functor (Partial expr) where
  fmap f = go
    where go (Continue expr) = Continue (fmap go expr)
          go (Stop err)      = Stop (f err)

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
