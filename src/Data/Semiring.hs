module Data.Semiring
( zero
, Semiring(..)
, Semigroup(..)
) where

import Data.Semigroup

-- | The identity element of some 'Monoid' @m@.
--
--   If @m@ is additionally a 'Semiring', this is the additive identity of the 'Semiring'.
zero :: Monoid m => m
zero = mempty

class (Semigroup m, Monoid m) => Semiring m where
  one :: m

  infixr 7 ><
  (><) :: m -> m -> m


-- Instances

instance Semiring () where
  one = ()
  (><) = (<>)
