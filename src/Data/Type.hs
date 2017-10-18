{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, UndecidableInstances #-}
module Data.Type where

import Data.Bifunctor
import Data.Either (fromLeft)
import Data.FreeTypeVariables
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Base, Fix(..), Recursive(..))
import Data.Name
import Data.Rec
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
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

infixr 1 :->
infixl 7 :*

instance Eq1 Type where liftEq = genericLiftEq
instance Ord1 Type where liftCompare = genericLiftCompare
instance Show1 Type where liftShowsPrec = genericLiftShowsPrec

data Error
  = FreeVariable Name
  | TypeMismatch (Type (Rec (Partial Type) Error)) (Type (Rec (Partial Type) Error))
  | InfiniteType Name (Type (Rec (Partial Type) Error))
  deriving (Eq, Ord, Show)

type Total = Fix


data Partial ty error recur = Cont (ty recur) | Fault error
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

fault :: error -> Rec (Partial ty) error
fault = Rec . Fault

instance (Eq1   ty, Eq   ann) => Eq1   (Partial ty ann) where liftEq        = genericLiftEq
instance (Ord1  ty, Ord  ann) => Ord1  (Partial ty ann) where liftCompare   = genericLiftCompare
instance (Show1 ty, Show ann) => Show1 (Partial ty ann) where liftShowsPrec = genericLiftShowsPrec


totalToPartial :: Total Type -> Rec (Partial Type) error
totalToPartial = cata emb

partialToTotal :: Rec (Partial Type) error -> Either [error] (Total Type)
partialToTotal = cata (\ partial -> case partial of
  Cont ty   -> fmap Fix (sequenceA ty)
  Fault err -> Left [err])


tvar :: Embeddable Type t => Name -> t
tvar name = emb (TVar name)

makeForAllT :: Embeddable Type t => Name -> t -> t
makeForAllT name body = emb (ForAll name body)

forAllT :: (Recursive t, Embeddable1 Type (Base t), Embeddable Type t) => (t -> t) -> t
forAllT hoas = makeForAllT n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: (Recursive t, Embeddable1 Type (Base t)) => t -> Maybe Name
maxBoundVariable = cata (maybe Nothing (\ partial -> case partial of
  ForAll name _ -> Just name
  ty            -> foldr max Nothing ty) . unemb1)

-- | Generalize a type by binding its free variables with foralls.
--
-- >>> generalize unitT :: Total Type
-- Fix Unit
--
-- prop> \ v -> generalize (tvar v .-> tvar v) == forAllT (\ t -> t .-> t :: Total Type)
generalize :: (Recursive ty, Embeddable1 Type (Base ty), Embeddable Type ty, FreeTypeVariables ty, Substitutable ty ty) => ty -> ty
generalize ty = foldr (\ v ty -> forAllT (\ new -> substitute (substSingleton v new) ty)) ty (Set.toList (freeTypeVariables ty))

specialize :: forall ty . (Embeddable Type ty, Substitutable ty ty) => Type ty -> Name -> ty
specialize (ForAll n b) to = substitute (substSingleton n (tvar to) :: Subst ty) b
specialize orig         _  = emb orig

(.->) :: Embeddable Type t => t -> t -> t
arg .-> ret = emb (arg :-> ret)

infixr 1 .->

unitT :: Embeddable Type t => t
unitT = emb Unit

(.*) :: Embeddable Type t => t -> t -> t
fst .* snd = emb (fst :* snd)

infixl 7 .*

tupleT :: Embeddable Type t => [t] -> t
tupleT = foldr (.*) unitT

boolT :: Embeddable Type t => t
boolT = emb Bool

listT :: Embeddable Type t => t -> t
listT = emb . List


prettyType :: Int -> Total Type -> ShowS
prettyType d ty = cata (\ ty d -> case ty of
  TVar name        -> prettyName d name
  ForAll name body -> showParen (d > 0) $ showString "∀ " . prettyName 1 name . showString " . " . body 0
  arg :-> ret      -> showParen (d > 1) $ arg 2 . showString " -> " . ret 1
  Unit             -> showString "Unit"
  fst :* snd       -> showParen (d > 7) $ fst 7 . showString " * " . snd 8
  Bool             -> showString "Bool"
  List element     -> showChar '[' . element 0 . showChar ']') ty d


instance FreeTypeVariables (Rec (Partial Type) error) where
  freeTypeVariables = cata (freeTypeVariables . first (const (Set.empty :: Set.Set Name)))

instance (FreeTypeVariables (ty recur), FreeTypeVariables error) => FreeTypeVariables (Partial ty error recur) where
  freeTypeVariables (Cont ty)   = freeTypeVariables ty
  freeTypeVariables (Fault err) = freeTypeVariables err

instance FreeTypeVariables t => FreeTypeVariables (Type t) where
  freeTypeVariables (TVar name)        = Set.singleton name
  freeTypeVariables (ForAll name body) = Set.delete name (freeTypeVariables body)
  freeTypeVariables ty                 = foldMap freeTypeVariables ty

instance FreeTypeVariables (Total Type) where
  freeTypeVariables (Fix ty) = freeTypeVariables ty


substType :: Substitutable ty recur => Subst ty -> Type recur -> Either (Type recur) ty
substType subst (TVar name)        = maybe (Left (TVar name)) Right (substLookup name subst)
substType subst (ForAll name body) = Left (ForAll name (substitute (substDelete name subst) body))
substType subst (arg :-> ret)      = Left (substitute subst arg :-> substitute subst ret)
substType _     Unit               = Left Unit
substType subst (fst :* snd)       = Left (substitute subst fst :* substitute subst snd)
substType _     Bool               = Left Bool
substType subst (List a)           = Left (List (substitute subst a))

instance Substitutable (Total Type) (Total Type) where
  substitute subst (Fix ty) = either emb id (substType subst ty)

instance Substitutable (Rec (Partial Type) error) error => Substitutable (Rec (Partial Type) error) (Rec (Partial Type) error) where
  substitute subst (Rec (Cont ty))   = either emb id (substType subst ty)
  substitute subst (Rec (Fault err)) = fault (substitute subst err)

instance Substitutable (Rec (Partial Type) Error) Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Functor ty => Bifunctor (Partial ty) where
  bimap _ g (Cont ty)   = Cont (fmap g ty)
  bimap f _ (Fault err) = Fault (f err)

instance Embeddable1 ty functor => Embeddable1 ty (Partial functor error) where
  emb1 = Cont . emb1

  unemb1 (Cont ty) = unemb1 ty
  unemb1 _         = Nothing

instance Embeddable1 Type Type where
  emb1 = id

  unemb1 = Just

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
