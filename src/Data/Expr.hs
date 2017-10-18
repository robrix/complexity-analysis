{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable #-}
module Data.Expr where

import Control.Comonad.Cofree
import Control.Comonad.Trans.Cofree (tailF)
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import Data.Name
import GHC.Generics

data Expr a
  = Abs Name a
  | Var Name
  | App a a
  | Rec Name a
  | Unit
  | Pair a a
  | Fst a
  | Snd a
  | Bool Bool
  | If a a a
  | Cons a a
  | Nil
  | Unlist a a a
  deriving (Eq, Foldable, Functor, Generic1, Ord, Read, Show, Traversable)

instance Eq1 Expr where liftEq = genericLiftEq
instance Ord1 Expr where liftCompare = genericLiftCompare
instance Show1 Expr where liftShowsPrec = genericLiftShowsPrec

type Term = Fix Expr
type AnnotatedTerm = Cofree Expr

erase :: AnnotatedTerm a -> Term
erase = cata (Fix . tailF)


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

var :: Name -> Term
var name = Fix (Var name)

(#) :: Term -> Term -> Term
func # arg = Fix (App func arg)

infixl 9 #


makeRec :: Name -> Term -> Term
makeRec name body = Fix (Rec name body)

rec :: (Term -> Term) -> Term
rec hoas = makeRec n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)


unit :: Term
unit = Fix Unit

pair :: Term -> Term -> Term
pair fst snd = Fix (Pair fst snd)

tuple :: [Term] -> Term
tuple = foldr pair unit

pfst :: Term -> Term
pfst pair = Fix (Fst pair)

psnd :: Term -> Term
psnd pair = Fix (Snd pair)

bool :: Bool -> Term
bool b = Fix (Bool b)

iff :: Term -> Term -> Term -> Term
iff c t e = Fix (If c t e)

cons :: Term -> Term -> Term
cons head tail = Fix (Cons head tail)

nil :: Term
nil = Fix Nil

list :: [Term] -> Term
list = foldr cons nil

unlist :: Term -> Term -> Term -> Term
unlist empty full list = Fix (Unlist empty full list)
