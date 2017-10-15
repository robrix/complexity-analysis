{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeOperators #-}
module Data.Functor.Classes.Generic
( Eq1(..)
, genericLiftEq
, Ord1(..)
, genericLiftCompare
, Show1(..)
, genericLiftShowsPrec
) where

import Data.Functor.Classes
import Data.Semigroup
import GHC.Generics
import Text.Show

-- $setup
-- >>> :set -XFlexibleContexts
-- >>> :set -XDeriveGeneric
-- >>> import Test.QuickCheck
-- >>> data Tree a = Tree a :$: Tree a | Leaf a | Empty deriving (Eq, Generic1, Ord, Show)
-- >>> instance Eq1 Tree where liftEq = genericLiftEq
-- >>> instance Ord1 Tree where liftCompare = genericLiftCompare
-- >>> instance Show1 Tree where liftShowsPrec = genericLiftShowsPrec
-- >>> instance Arbitrary a => Arbitrary (Tree a) where arbitrary = oneof [ pure Empty, Leaf <$> arbitrary, (:$:) <$> arbitrary <*> arbitrary ]
-- >>> let asTree tree = case tree of { _ :$: _ -> tree ; _ -> tree }
-- >>> data Triple a = Triple { one :: a, two :: a, three :: a } deriving (Eq, Generic1, Ord, Show)
-- >>> instance Arbitrary a => Arbitrary (Triple a) where arbitrary = Triple <$> arbitrary <*> arbitrary <*> arbitrary

-- | Generically-derivable lifting of the 'Eq' class to unary type constructors.
class GEq1 f where
  -- | Lift an equality test through the type constructor.
  --
  --   The function will usually be applied to an equality function, but the more general type ensures that the implementation uses it to compare elements of the first container with elements of the second.
  gliftEq :: (a -> b -> Bool) -> f a -> f b -> Bool

-- | A suitable implementation of Eq1’s liftEq for Generic1 types.
--
-- prop> \ a b -> genericLiftEq (==) a b == (a == asTree b)
-- prop> \ a b@Triple{} -> genericLiftEq (==) a b == (a == b)
genericLiftEq :: (Generic1 f, GEq1 (Rep1 f)) => (a -> b -> Bool) -> f a -> f b -> Bool
genericLiftEq f a b = gliftEq f (from1 a) (from1 b)


-- | Generically-derivable lifting of the 'Ord' class to unary type constructors.
class GOrd1 f where
  -- | Lift a comparison function through the type constructor.
  --
  --   The function will usually be applied to a comparison function, but the more general type ensures that the implementation uses it to compare elements of the first container with elements of the second.
  gliftCompare :: (a -> b -> Ordering) -> f a -> f b -> Ordering

-- | A suitable implementation of Ord1’s liftCompare for Generic1 types.
--
-- prop> \ a b -> genericLiftCompare compare a b == compare a (asTree b)
-- prop> \ a b@Triple{} -> genericLiftCompare compare a b == compare a b
genericLiftCompare :: (Generic1 f, GOrd1 (Rep1 f)) => (a -> b -> Ordering) -> f a -> f b -> Ordering
genericLiftCompare f a b = gliftCompare f (from1 a) (from1 b)


-- | Generically-derivable lifting of the 'Show' class to unary type constructors.
class GShow1 f where
  -- | showsPrec function for an application of the type constructor based on showsPrec and showList functions for the argument type.
  gliftShowsPrec :: (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> f a -> ShowS

class GShow1Body f where
  -- | showsPrec function for the body of an application of the type constructor based on showsPrec and showList functions for the argument type.
  gliftShowsPrecBody :: Fixity -> String -> (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> f a -> ShowS

-- | showList function for an application of the type constructor based on showsPrec and showList functions for the argument type. The default implementation using standard list syntax is correct for most types.
gliftShowList :: GShow1 f => (Int -> a -> ShowS) -> ([a] -> ShowS) -> [f a] -> ShowS
gliftShowList sp sl = showListWith (gliftShowsPrec sp sl 0)

-- | A suitable implementation of Show1’s liftShowsPrec for Generic1 types.
--
-- prop> \ a -> genericLiftShowsPrec showsPrec showList 0 a "" == showsPrec 0 (asTree a) ""
genericLiftShowsPrec :: (Generic1 f, GShow1 (Rep1 f)) => (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> f a -> ShowS
genericLiftShowsPrec sp sl d = gliftShowsPrec sp sl d . from1


-- Generics

instance GEq1 U1 where
  gliftEq _ _ _ = True

instance GEq1 Par1 where
  gliftEq f (Par1 a) (Par1 b) = f a b

instance Eq c => GEq1 (K1 i c) where
  gliftEq _ (K1 a) (K1 b) = a == b

instance Eq1 f => GEq1 (Rec1 f) where
  gliftEq f (Rec1 a) (Rec1 b) = liftEq f a b

instance GEq1 f => GEq1 (M1 i c f) where
  gliftEq f (M1 a) (M1 b) = gliftEq f a b

instance (GEq1 f, GEq1 g) => GEq1 (f :+: g) where
  gliftEq f a b = case (a, b) of
    (L1 a, L1 b) -> gliftEq f a b
    (R1 a, R1 b) -> gliftEq f a b
    _ -> False

instance (GEq1 f, GEq1 g) => GEq1 (f :*: g) where
  gliftEq f (a1 :*: b1) (a2 :*: b2) = gliftEq f a1 a2 && gliftEq f b1 b2

instance (Eq1 f, GEq1 g) => GEq1 (f :.: g) where
  gliftEq f (Comp1 a) (Comp1 b) = liftEq (gliftEq f) a b


instance GOrd1 U1 where
  gliftCompare _ _ _ = EQ

instance GOrd1 Par1 where
  gliftCompare f (Par1 a) (Par1 b) = f a b

instance Ord c => GOrd1 (K1 i c) where
  gliftCompare _ (K1 a) (K1 b) = compare a b

instance Ord1 f => GOrd1 (Rec1 f) where
  gliftCompare f (Rec1 a) (Rec1 b) = liftCompare f a b

instance GOrd1 f => GOrd1 (M1 i c f) where
  gliftCompare f (M1 a) (M1 b) = gliftCompare f a b

instance (GOrd1 f, GOrd1 g) => GOrd1 (f :+: g) where
  gliftCompare f a b = case (a, b) of
    (L1 a, L1 b) -> gliftCompare f a b
    (R1 a, R1 b) -> gliftCompare f a b
    (L1 _, R1 _) -> LT
    (R1 _, L1 _) -> GT

instance (GOrd1 f, GOrd1 g) => GOrd1 (f :*: g) where
  gliftCompare f (a1 :*: b1) (a2 :*: b2) = gliftCompare f a1 a2 <> gliftCompare f b1 b2

instance (Ord1 f, GOrd1 g) => GOrd1 (f :.: g) where
  gliftCompare f (Comp1 a) (Comp1 b) = liftCompare (gliftCompare f) a b


instance GShow1 Par1 where
  gliftShowsPrec sp _ d (Par1 a) = sp d a

instance Show c => GShow1 (K1 i c) where
  gliftShowsPrec _ _ d (K1 a) = showsPrec d a

instance Show1 f => GShow1 (Rec1 f) where
  gliftShowsPrec sp sl d (Rec1 a) = liftShowsPrec sp sl d a

instance GShow1 f => GShow1 (M1 D c f) where
  gliftShowsPrec sp sl d (M1 a) = gliftShowsPrec sp sl d a

instance (Constructor c, GShow1Body f) => GShow1 (M1 C c f) where
  gliftShowsPrec sp sl d m = gliftShowsPrecBody (conFixity m) (conName m) sp sl d (unM1 m)

instance GShow1Body U1 where
  gliftShowsPrecBody _ conName _ _ _ _ = showString conName

instance GShow1 f => GShow1Body (M1 S c f) where
  gliftShowsPrecBody _ conName sp sl d (M1 a) = showsUnaryWith (gliftShowsPrec sp sl) conName d a

instance (GShow1 f, GShow1 g) => GShow1Body (f :*: g) where
  gliftShowsPrecBody fixity conName sp sl d (a :*: b) = case fixity of
    Prefix       -> showsBinaryWith (gliftShowsPrec sp sl) (gliftShowsPrec sp sl) conName d a b
    Infix _ prec -> showParen (d > prec) $ gliftShowsPrec sp sl (succ prec) a . showChar ' ' . showString conName . showChar ' ' . gliftShowsPrec sp sl (succ prec) b

instance GShow1 f => GShow1 (M1 S c f) where
  gliftShowsPrec sp sl d (M1 a) = gliftShowsPrec sp sl d a

instance (GShow1 f, GShow1 g) => GShow1 (f :+: g) where
  gliftShowsPrec sp sl d (L1 l) = gliftShowsPrec sp sl d l
  gliftShowsPrec sp sl d (R1 r) = gliftShowsPrec sp sl d r

instance (GShow1 f, GShow1 g) => GShow1 (f :*: g) where
  gliftShowsPrec sp sl d (a :*: b) = gliftShowsPrec sp sl d a . showChar ' ' . gliftShowsPrec sp sl d b

instance (Show1 f, GShow1 g) => GShow1 (f :.: g) where
  gliftShowsPrec sp sl d (Comp1 a) = liftShowsPrec (gliftShowsPrec sp sl) (gliftShowList sp sl) d a
