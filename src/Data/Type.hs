{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
module Data.Type where

import Data.Bifunctor
import Data.Either (fromLeft)
import Data.FreeTypeVariables
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
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


data Partial expr error recur = Cont (expr recur) | Stop error
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

cont :: expr (Rec (Partial expr) error) -> Rec (Partial expr) error
cont = Rec . Cont

stop :: error -> Rec (Partial expr) error
stop = Rec . Stop

instance (Eq1   expr, Eq   ann) => Eq1   (Partial expr ann) where liftEq        = genericLiftEq
instance (Ord1  expr, Ord  ann) => Ord1  (Partial expr ann) where liftCompare   = genericLiftCompare
instance (Show1 expr, Show ann) => Show1 (Partial expr ann) where liftShowsPrec = genericLiftShowsPrec


totalToPartial :: Total Type -> Rec (Partial Type) error
totalToPartial = cata cont

partialToTotal :: Rec (Partial Type) error -> Either [error] (Total Type)
partialToTotal = cata (\ partial -> case partial of
  Cont expr -> fmap Fix (sequenceA expr)
  Stop err  -> Left [err])


tvar :: Name -> Rec (Partial Type) error
tvar name = cont (TVar name)

makeForAllT :: Name -> Rec (Partial Type) error -> Rec (Partial Type) error
makeForAllT name body = cont (ForAll name body)

forAllT :: (Rec (Partial Type) error -> Rec (Partial Type) error) -> Rec (Partial Type) error
forAllT hoas = makeForAllT n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (tvar n)

maxBoundVariable :: Rec (Partial Type) error -> Maybe Name
maxBoundVariable = cata (\ partial -> case partial of
  Cont (ForAll name _) -> Just name
  Cont expr            -> foldr max Nothing expr
  Stop _               -> Nothing)

-- | Generalize a type by binding its free variables with foralls.
--
-- >>> generalize unitT :: Partial Type Error
-- Cont Unit
--
-- prop> \ v -> generalize (tvar v .-> tvar v) == forAllT (\ t -> t .-> t :: Partial Type Error)
generalize :: Substitutable (Rec (Partial Type) error) error => Rec (Partial Type) error -> Rec (Partial Type) error
generalize ty = foldr (\ v ty -> forAllT (\ new -> substitute (substSingleton v new) ty)) ty (Set.toList (freeTypeVariables ty))

specialize :: forall error . Substitutable (Rec (Partial Type) error) error => Type (Rec (Partial Type) error) -> Name -> Rec (Partial Type) error
specialize (ForAll n b) to = substitute (substSingleton n (tvar to) :: Subst (Rec (Partial Type) error)) b
specialize orig         _  = cont orig

(.->) :: Rec (Partial Type) error -> Rec (Partial Type) error -> Rec (Partial Type) error
arg .-> ret = cont (arg :-> ret)

infixr 1 .->

unitT :: Rec (Partial Type) error
unitT = cont Unit

(.*) :: Rec (Partial Type) error -> Rec (Partial Type) error -> Rec (Partial Type) error
fst .* snd = cont (fst :* snd)

infixl 7 .*

tupleT :: [Rec (Partial Type) error] -> Rec (Partial Type) error
tupleT = foldr (.*) unitT

boolT :: Rec (Partial Type) error
boolT = cont Bool

listT :: Rec (Partial Type) error -> Rec (Partial Type) error
listT = cont . List


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

instance (FreeTypeVariables (expr recur), FreeTypeVariables error) => FreeTypeVariables (Partial expr error recur) where
  freeTypeVariables (Cont expr) = freeTypeVariables expr
  freeTypeVariables (Stop err)  = freeTypeVariables err

instance FreeTypeVariables t => FreeTypeVariables (Type t) where
  freeTypeVariables (TVar name)        = Set.singleton name
  freeTypeVariables (ForAll name body) = Set.delete name (freeTypeVariables body)
  freeTypeVariables ty                 = foldMap freeTypeVariables ty


substType :: Substitutable ty recur => Subst ty -> Type recur -> Either (Type recur) ty
substType subst (TVar name)        = maybe (Left (TVar name)) Right (substLookup name subst)
substType subst (ForAll name body) = Left (ForAll name (substitute (substDelete name subst) body))
substType subst (arg :-> ret)      = Left (substitute subst arg :-> substitute subst ret)
substType _     Unit               = Left Unit
substType subst (fst :* snd)       = Left (substitute subst fst :* substitute subst snd)
substType _     Bool               = Left Bool
substType subst (List a)           = Left (List (substitute subst a))

instance Substitutable (Rec (Partial Type) error) error => Substitutable (Rec (Partial Type) error) (Rec (Partial Type) error) where
  substitute subst (Rec (Cont expr)) = either cont id (substType subst expr)
  substitute subst (Rec (Stop err))  = stop (substitute subst err)

instance Substitutable (Rec (Partial Type) Error) Error where
  substitute _     (FreeVariable name)    = FreeVariable name
  substitute subst (TypeMismatch t1 t2)   = TypeMismatch (fromLeft t1 (substType subst t1)) (fromLeft t2 (substType subst t2))
  substitute subst (InfiniteType name ty) = InfiniteType name (fromLeft ty (substType (substDelete name subst) ty))

instance Functor expr => Bifunctor (Partial expr) where
  bimap _ g (Cont expr) = Cont (fmap g expr)
  bimap f _ (Stop err)  = Stop (f err)

instance Embeddable1 expr (Partial expr error) where
  emb1 = Cont

-- $setup
-- >>> import Test.QuickCheck
-- >>> instance Arbitrary Name where arbitrary = Name <$> arbitrary
