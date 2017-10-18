{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
module Data.Expr where

import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Base, Fix(..), Recursive(..))
import Data.Name
import Data.Subst
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

data Ann expr ann = In ann (expr (Ann expr ann))
deriving instance (Eq   (expr (Ann expr ann)), Eq   ann) => Eq   (Ann expr ann)
deriving instance (Ord  (expr (Ann expr ann)), Ord  ann) => Ord  (Ann expr ann)
deriving instance (Show (expr (Ann expr ann)), Show ann) => Show (Ann expr ann)

ann :: Ann expr ann -> ann
ann (In ann _) = ann

out :: Ann expr ann -> expr (Ann expr ann)
out (In _ expr) = expr

data AnnF expr ann recur = InF ann (expr recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance (Eq1   expr, Eq   ann) => Eq1   (AnnF expr ann) where liftEq        = genericLiftEq
instance (Ord1  expr, Ord  ann) => Ord1  (AnnF expr ann) where liftCompare   = genericLiftCompare
instance (Show1 expr, Show ann) => Show1 (AnnF expr ann) where liftShowsPrec = genericLiftShowsPrec

annF :: AnnF expr ann recur -> ann
annF (InF ann _) = ann

outF :: AnnF expr ann recur -> expr recur
outF (InF _ expr) = expr

type instance Base (Ann expr ann) = AnnF expr ann

instance Functor expr => Recursive (Ann expr ann) where project (In a o) = InF a o

erase :: Functor expr => Ann expr ann -> Fix expr
erase = cata (Fix . outF)


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


instance (Substitutable ann ann, Functor expr) => Substitutable ann (Ann expr ann) where
  substitute subst (In ann expr) = In (substitute subst ann) (fmap (substitute subst) expr)

instance Functor expr => Functor (Ann expr) where
  fmap f = go where go (In ann expr) = In (f ann) (fmap go expr)
