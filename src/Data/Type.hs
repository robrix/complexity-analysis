{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Data.Type where

import Data.Either (fromLeft)
import Data.FreeTypeVariables
import Data.Functor.Classes
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

instance Eq1   Type where liftEq        = genericLiftEq
instance Ord1  Type where liftCompare   = genericLiftCompare
instance Show1 Type where liftShowsPrec = genericLiftShowsPrec

data Error ty recur
  = FreeVariable Name
  | TypeMismatch (ty recur) (ty recur)
  | InfiniteType Name (ty recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance Eq1   ty => Eq1   (Error ty) where liftEq        = genericLiftEq
instance Ord1  ty => Ord1  (Error ty) where liftCompare   = genericLiftCompare
instance Show1 ty => Show1 (Error ty) where liftShowsPrec = genericLiftShowsPrec


type Total = Fix

data Partial  error ty       = Cont  (ty (Partial error ty)) | Fault  (error ty (Partial error ty))
data PartialF error ty recur = ContF (ty recur)              | FaultF (error ty recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance (Eq1   (error ty), Eq1   ty) => Eq1   (PartialF error ty) where liftEq        = genericLiftEq
instance (Ord1  (error ty), Ord1  ty) => Ord1  (PartialF error ty) where liftCompare   = genericLiftCompare
instance (Show1 (error ty), Show1 ty) => Show1 (PartialF error ty) where liftShowsPrec = genericLiftShowsPrec

type instance Base (Partial error ty) = PartialF error ty

instance (Functor (error ty), Functor ty) => Recursive (Partial error ty) where
  project (Cont t)  = ContF t
  project (Fault e) = FaultF e

instance (Eq1 (error ty), Eq1 ty) => Eq (Partial error ty) where
  Cont t1  == Cont t2  = eq1 t1 t2
  Fault e1 == Fault e2 = eq1 e1 e2
  _        == _        = False

instance (Ord1 (error ty), Ord1 ty) => Ord (Partial error ty) where
  compare (Cont t1)  (Cont t2)  = compare1 t1 t2
  compare (Cont _)   (Fault _)  = LT
  compare (Fault _)  (Cont _)   = GT
  compare (Fault e1) (Fault e2) = compare1 e1 e2

instance (Show1 (error ty), Show1 ty) => Show (Partial error ty) where
  showsPrec d (Cont ty) = showsUnaryWith showsPrec1 "Cont"  d ty
  showsPrec d (Fault e) = showsUnaryWith showsPrec1 "Fault" d e


totalToPartial :: Functor ty => Total ty -> Partial error ty
totalToPartial = cata Cont

partialToTotal :: (Functor (error ty), Traversable ty) => Partial error ty -> Either [error ty (Partial error ty)] (Total ty)
partialToTotal = para (\ partial -> case partial of
  ContF ty   -> fmap Fix (traverse snd ty)
  FaultF err -> Left [fmap fst err])


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


instance (FreeTypeVariables1 (error ty), FreeTypeVariables1 ty, Functor (error ty), Functor ty) => FreeTypeVariables (Partial error ty) where
  freeTypeVariables = cata freeTypeVariables1

instance (FreeTypeVariables1 (error ty), FreeTypeVariables1 ty) => FreeTypeVariables1 (PartialF error ty) where
  liftFreeTypeVariables recur (ContF ty)   = liftFreeTypeVariables recur ty
  liftFreeTypeVariables recur (FaultF err) = liftFreeTypeVariables recur err

instance FreeTypeVariables1 Type where
  liftFreeTypeVariables _     (TVar name)        = Set.singleton name
  liftFreeTypeVariables recur (ForAll name body) = Set.delete name (recur body)
  liftFreeTypeVariables recur ty                 = foldMap recur ty

instance FreeTypeVariables1 ty => FreeTypeVariables1 (Error ty) where
  liftFreeTypeVariables _     (FreeVariable _)     = mempty -- The free variable here is a term variable, not a type variable.
  liftFreeTypeVariables recur (TypeMismatch t1 t2) = liftFreeTypeVariables recur t1 `mappend` liftFreeTypeVariables recur t2
  liftFreeTypeVariables recur (InfiniteType n b)   = Set.insert n (liftFreeTypeVariables recur b)


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

instance Substitutable (Partial Error Type) (Partial Error Type) where
  substitute subst (Cont ty)   = either emb id (substType subst ty)
  substitute subst (Fault err) = Fault (substitute subst err)

instance Substitutable ty recur => Substitutable ty (Error Type recur) where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Embeddable1 ty functor => Embeddable ty (Partial error functor) where
  emb = Cont . emb1

  unemb (Cont ty) = unemb1 ty
  unemb _         = Nothing

instance Embeddable1 ty functor => Embeddable1 ty (PartialF error functor) where
  emb1 = ContF . emb1

  unemb1 (ContF ty) = unemb1 ty
  unemb1 _          = Nothing

instance Embeddable1 Type Type where
  emb1 = id

  unemb1 = Just

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
