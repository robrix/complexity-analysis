{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Data.Type where

import Data.Bifunctor
import Data.FreeVariables
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Base, Fix(..), Recursive(..), unfix)
import Data.Name
import Data.Rec
import qualified Data.Set as Set
import Data.Subst
import GHC.Generics

data Type a
  = ForAll Name a
  | TVar Name
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


type Total = Fix

data Partial  error ty       = Cont  (ty (Partial error ty)) | Fault  error
data PartialF error ty recur = ContF (ty recur)              | FaultF error
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance (Eq   error, Eq1   ty) => Eq1   (PartialF error ty) where liftEq        = genericLiftEq
instance (Ord  error, Ord1  ty) => Ord1  (PartialF error ty) where liftCompare   = genericLiftCompare
instance (Show error, Show1 ty) => Show1 (PartialF error ty) where liftShowsPrec = genericLiftShowsPrec

type instance Base (Partial error ty) = PartialF error ty

instance Functor ty => Recursive (Partial error ty) where
  project (Cont t)  = ContF t
  project (Fault e) = FaultF e

instance (Eq error, Eq1 ty) => Eq (Partial error ty) where
  Cont t1  == Cont t2  = eq1 t1 t2
  Fault e1 == Fault e2 = e1 == e2
  _        == _        = False

instance (Ord error, Ord1 ty) => Ord (Partial error ty) where
  compare (Cont t1)  (Cont t2)  = compare1 t1 t2
  compare (Cont _)   (Fault _)  = LT
  compare (Fault _)  (Cont _)   = GT
  compare (Fault e1) (Fault e2) = compare e1 e2

instance (Show error, Show1 ty) => Show (Partial error ty) where
  showsPrec d (Cont ty) = showsUnaryWith showsPrec1 "Cont"  d ty
  showsPrec d (Fault e) = showsUnaryWith showsPrec  "Fault" d e


data Sized ty size recur = Sized size (ty recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

size :: Sized ty size recur -> size
size (Sized size _) = size

sizedType :: Sized ty size recur -> ty recur
sizedType (Sized _ ty) = ty

eraseSize :: (Recursive t, Base t ~ Sized ty size, Functor ty) => t -> Total ty
eraseSize = cata (Fix . sizedType)

instance (Eq1   ty, Eq   size) => Eq1   (Sized ty size) where liftEq        = genericLiftEq
instance (Ord1  ty, Ord  size) => Ord1  (Sized ty size) where liftCompare   = genericLiftCompare
instance (Show1 ty, Show size) => Show1 (Sized ty size) where liftShowsPrec = genericLiftShowsPrec

instance Functor ty => Bifunctor (Sized ty) where
  bimap f g (Sized size ty) = Sized (f size) (fmap g ty)


modifySize :: Functor ty => (size -> size) -> Partial error (Sized ty size) -> Partial error (Sized ty size)
modifySize f (Cont sized) = Cont (first f sized)
modifySize _ other        = other


totalToPartial :: Typical1 ty => Total Type -> Partial error ty
totalToPartial = cata fromType

partialToTotal :: Traversable ty => Partial error ty -> Either [error] (Total ty)
partialToTotal = para (\ partial -> case partial of
  ContF ty   -> fmap Fix (traverse snd ty)
  FaultF err -> Left [err])


class Typical t where
  makeForAllT :: Name -> t -> t
  makeForAllT name body = fromType (ForAll name body)

  tvar :: Name -> t
  tvar name = fromType (TVar name)


  (.->) :: t -> t -> t
  a .-> b = fromType (a :-> b)

  infixr 1 .->


  unitT :: t
  unitT = fromType Unit

  (.*) :: t -> t -> t
  l .* r = fromType (l :* r)

  infixl 7 .*


  boolT :: t
  boolT = fromType Bool


  listT :: t -> t
  listT element = fromType (List element)


  fromType :: Type t -> t
  toType :: t -> Maybe (Type t)

class Typical1 t where
  fromType1 :: Type a -> t a
  toType1 :: t a -> Maybe (Type a)

instance Typical1 Type where
  fromType1 = id
  toType1 = Just

instance Monoid size => Typical1 (Sized Type size) where
  fromType1 = Sized mempty
  toType1 = Just . sizedType


instance Typical1 (ty size) => Typical (Rec ty size) where
  fromType = Rec . fromType1
  toType = toType1 . unRec

instance Typical1 ty => Typical (Total ty) where
  fromType = Fix . fromType1
  toType = toType1 . unfix

instance Typical1 ty => Typical (Partial error ty) where
  fromType = Cont . fromType1
  toType (Cont ty) = toType1 ty
  toType _         = Nothing

instance Typical1 ty => Typical1 (PartialF error ty) where
  fromType1 = ContF . fromType1
  toType1 (ContF ty) = toType1 ty
  toType1 _          = Nothing


forAllT :: (Recursive t, Typical1 (Base t), Typical t) => (t -> t) -> t
forAllT hoas = makeForAllT n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: (Recursive t, Typical1 (Base t)) => t -> Maybe Name
maxBoundVariable = cata (maybe Nothing (\ partial -> case partial of
  ForAll name _ -> Just name
  ty            -> foldr max Nothing ty) . toType1)

-- | Generalize a type by binding its free variables with foralls.
--
-- >>> generalize unitT :: Total Type
-- Fix Unit
--
-- prop> \ v -> generalize (tvar v .-> tvar v) == forAllT (\ t -> t .-> t :: Total Type)
generalize :: (Recursive ty, Typical1 (Base ty), Typical ty, FreeVariables ty, Substitutable ty ty) => ty -> ty
generalize ty = foldr (\ v ty -> forAllT (\ new -> substitute (substSingleton v new) ty)) ty (Set.toList (freeVariables ty))

specialize :: forall ty . (Typical ty, Substitutable ty ty) => Type ty -> Name -> ty
specialize (ForAll n b) to = substitute (substSingleton n (tvar to) :: Subst ty) b
specialize orig         _  = fromType orig

tupleT :: Typical t => [t] -> t
tupleT = foldr (.*) unitT


prettyType :: Int -> Total Type -> ShowS
prettyType d ty = cata (\ ty d -> case ty of
  TVar name        -> prettyName d name
  ForAll name body -> showParen (d > 0) $ showString "∀ " . prettyName 1 name . showString " . " . body 0
  arg :-> ret      -> showParen (d > 1) $ arg 2 . showString " -> " . ret 1
  Unit             -> showString "Unit"
  fst :* snd       -> showParen (d > 7) $ fst 7 . showString " * " . snd 8
  Bool             -> showString "Bool"
  List element     -> showChar '[' . element 0 . showChar ']') ty d


instance (FreeVariables1 ty, Functor ty) => FreeVariables (Partial error ty) where
  freeVariables = cata freeVariables1

instance FreeVariables1 ty => FreeVariables1 (PartialF error ty) where
  liftFreeVariables recur (ContF ty) = liftFreeVariables recur ty
  liftFreeVariables _     (FaultF _) = mempty

instance FreeVariables1 Type where
  liftFreeVariables _     (TVar name)        = Set.singleton name
  liftFreeVariables recur (ForAll name body) = Set.delete name (recur body)
  liftFreeVariables recur ty                 = foldMap recur ty

instance FreeVariables1 ty => FreeVariables1 (Sized ty size) where
  liftFreeVariables recur (Sized _ ty) = liftFreeVariables recur ty


instance Substitutable1 ty Type where
  liftSubstitute _     subst (TVar name)        = maybe (Left (TVar name)) Right (substLookup name subst)
  liftSubstitute recur subst (ForAll name body) = Left (ForAll name (recur (substDelete name subst) body))
  liftSubstitute recur subst (arg :-> ret)      = Left (recur subst arg :-> recur subst ret)
  liftSubstitute _     _     Unit               = Left Unit
  liftSubstitute recur subst (fst :* snd)       = Left (recur subst fst :* recur subst snd)
  liftSubstitute _     _     Bool               = Left Bool
  liftSubstitute recur subst (List a)           = Left (List (recur subst a))

instance Substitutable1 (Partial error ty) ty => Substitutable (Partial error ty) (Partial error ty) where
  substitute subst (Cont ty)   = either Cont  id (liftSubstitute substitute subst ty)
  substitute _     (Fault err) = Fault err

instance Substitutable1 ty functor => Substitutable1 ty (Sized functor size) where
  liftSubstitute recur subst (Sized size ty) = first (Sized size) (liftSubstitute recur subst ty)

instance Substitutable1 (Rec (Sized ty) size) ty => Substitutable (Rec (Sized ty) size) (Rec (Sized ty) size) where
  substitute subst (Rec (Sized size ty)) = either (const (Rec (Sized size ty))) id (liftSubstitute substitute subst ty)


-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
