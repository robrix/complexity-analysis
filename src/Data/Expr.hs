{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable #-}
module Data.Expr where

import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Recursive(..), Fix(..))
import Data.Name
import GHC.Generics

data Expr a
  = Abs Name a
  | App a a
  | Var Name
  | Lit Bool
  | If a a a
  | Pair a a
  | Fst a
  | Snd a
  deriving (Eq, Foldable, Functor, Generic1, Ord, Read, Show, Traversable)

instance Eq1 Expr where liftEq = genericLiftEq
instance Ord1 Expr where liftCompare = genericLiftCompare
instance Show1 Expr where liftShowsPrec = genericLiftShowsPrec

type Term = Fix Expr

makeAbs :: Name -> Term -> Term
makeAbs name body = Fix (Abs name body)

-- | Construct a 'Term' for a function using the supplied function to construct the body.
--
--   This uses the approach described in _Using Circular Programs for Higher-Order Syntax_, Emil Axelsson, Koen Claessen: http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf
--
--   >>> lam id
--   Fix (Abs (Name 0) (Fix (Var (Name 0))))
--   >>> lam (\ x -> lam (const x))
--   Fix (Abs (Name 1) (Fix (Abs (Name 0) (Fix (Var (Name 1))))))
lam :: (Term -> Term) -> Term
lam hoas = makeAbs n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)

maxBoundVariable :: Term -> Maybe Name
maxBoundVariable = cata $ \ expr -> case expr of
  Abs name _ -> Just name
  _          -> foldr max Nothing expr

(#) :: Term -> Term -> Term
func # arg = Fix (App func arg)

infixl 9 #

var :: Name -> Term
var name = Fix (Var name)

bool :: Bool -> Term
bool b = Fix (Lit b)

iff :: Term -> Term -> Term -> Term
iff c t e = Fix (If c t e)

pair :: Term -> Term -> Term
pair fst snd = Fix (Pair fst snd)

pfst :: Term -> Term
pfst pair = Fix (Fst pair)

psnd :: Term -> Term
psnd pair = Fix (Snd pair)
