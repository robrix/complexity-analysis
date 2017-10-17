{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Semiring
( zero
, Semiring(..)
, Semigroup(..)
-- Instances
, Arith(..)
, Mult(..)
) where

import Data.Semigroup

-- | The identity element of some 'Monoid' @m@.
--
--   If @m@ is additionally a 'Semiring', this is the additive identity of the 'Semiring'.
zero :: Monoid m => m
zero = mempty

-- | A 'Semiring' is an abstract algebraic structure consisting of two associative operations, '(<>)' and '(><)', and their identities, 'zero' and 'one' respectively, with the additional constraints that '(><)' distributes over '(<>)' and that 'zero' is the annihilator for '(><)'.
--
--   Laws:
--
--   The 'Semigroup' laws (associativity of '(<>)' & equality of '(<>)' and 'mappend'):
--
--   > a <> (b <> c) = (a <> b) <> c
--   > (<>) = mappend
--
--   The 'Monoid' laws ('zero' is the left- and right-identity of '(<>)'):
--
--   > zero <> a = a
--   > a <> zero = a
--
--   'one' is the left- and right-identity of '(><)':
--
--   > one >< a = a
--   > a >< one = a
--
--   '(><)' is associative:
--
--   > a >< (b >< c) = (a >< b) >< c
--
--   '(><)' is left- and right-distributive over '(<>)':
--
--   > a >< (b <> c) = (a >< b) <> (a >< c)
--   > (a <> b) >< c = (a >< c) <> (b >< c)
--
--   'zero' is the left- and right-annihilator of '(><)':
--
--   > zero >< a = zero
--   > a >< zero = zero
class (Semigroup m, Monoid m) => Semiring m where
  one :: m

  infixr 7 ><
  (><) :: m -> m -> m


-- Instances

instance Semiring () where
  one = ()
  (><) = (<>)


instance Monoid a => Semiring [a] where
  one = [zero]
  as >< bs = mappend <$> as <*> bs


-- | A 'Semiring' over a 'Num' instance.
newtype Arith a = Arith { getArith :: a }
  deriving (Bounded, Eq, Num, Ord, Read, Show)

instance Num a => Semigroup (Arith a) where
  (<>) = (+)

instance Num a => Monoid (Arith a) where
  mempty = 0
  mappend = (+)

instance Num a => Semiring (Arith a) where
  one = 1
  (><) = (*)


-- | The multiplicative 'Monoid' taken from a 'Semiring'
newtype Mult a = Mult { getMult :: a }
  deriving (Bounded, Eq, Ord, Read, Show)

instance Semiring a => Semigroup (Mult a) where
  Mult a <> Mult b = Mult (a >< b)

instance Semiring a => Monoid (Mult a) where
  mempty = Mult one
  mappend = (<>)
