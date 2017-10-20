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

data Sized ty size recur = Sized size (ty recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

size :: Sized ty size recur -> size
size (Sized size _) = size

sizedType :: Rec (Sized ty) size -> ty (Rec (Sized ty) size)
sizedType = sizedTypeF . unRec

sizedTypeF :: Sized ty size recur -> ty recur
sizedTypeF (Sized _ ty) = ty

eraseSize :: (Recursive t, Base t ~ Sized ty size, Functor ty) => t -> Total ty
eraseSize = cata (Fix . sizedTypeF)

instance (Eq1   ty, Eq   size) => Eq1   (Sized ty size) where liftEq        = genericLiftEq
instance (Ord1  ty, Ord  size) => Ord1  (Sized ty size) where liftCompare   = genericLiftCompare
instance (Show1 ty, Show size) => Show1 (Sized ty size) where liftShowsPrec = genericLiftShowsPrec

instance Functor ty => Bifunctor (Sized ty) where
  bimap f g (Sized size ty) = Sized (f size) (fmap g ty)


modifySize :: Functor ty => (size -> size) -> Rec (Sized ty) size -> Rec (Sized ty) size
modifySize f (Rec sized) = Rec (first f sized)


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
  toType1 = Just . sizedTypeF


instance Typical1 (ty size) => Typical (Rec ty size) where
  fromType = Rec . fromType1
  toType = toType1 . unRec

instance Typical1 ty => Typical (Total ty) where
  fromType = Fix . fromType1
  toType = toType1 . unfix


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

instance Substitutable1 ty functor => Substitutable1 ty (Sized functor size) where
  liftSubstitute recur subst (Sized size ty) = first (Sized size) (liftSubstitute recur subst ty)

instance Substitutable1 (Rec (Sized ty) size) ty => Substitutable (Rec (Sized ty) size) (Rec (Sized ty) size) where
  substitute subst (Rec (Sized size ty)) = either (Rec . Sized size) id (liftSubstitute substitute subst ty)


-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
