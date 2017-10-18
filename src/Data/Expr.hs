{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Expr where

import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import Data.Name
import Data.Rec
import Data.Subst
import GHC.Generics

data Expr a
  = Abs Name a
  | Var Name
  | App a a
  | LetRec Name a
  | Unit
  | Pair a a
  | Fst a
  | Snd a
  | Bool Bool
  | If a a a
  | Cons a a
  | Nil
  | Unlist a a a
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance Eq1 Expr where liftEq = genericLiftEq
instance Ord1 Expr where liftCompare = genericLiftCompare
instance Show1 Expr where liftShowsPrec = genericLiftShowsPrec

type Term = Fix

data Ann expr ann recur = In ann (expr recur)
  deriving (Eq, Foldable, Functor, Generic1, Ord, Show, Traversable)

instance (Eq1   expr, Eq   ann) => Eq1   (Ann expr ann) where liftEq        = genericLiftEq
instance (Ord1  expr, Ord  ann) => Ord1  (Ann expr ann) where liftCompare   = genericLiftCompare
instance (Show1 expr, Show ann) => Show1 (Ann expr ann) where liftShowsPrec = genericLiftShowsPrec

ann :: Rec (Ann expr) ann -> ann
ann (Rec (In ann _)) = ann

expr :: Rec (Ann expr) ann -> expr (Rec (Ann expr) ann)
expr (Rec (In _ expr)) = expr

annF :: Ann expr ann recur -> ann
annF (In ann _) = ann

exprF :: Ann expr ann recur -> expr recur
exprF (In _ expr) = expr


erase :: Functor expr => Rec (Ann expr) ann -> Term expr
erase = cata (Fix . exprF)


makeAbs :: Name -> Term Expr -> Term Expr
makeAbs name body = Fix (Abs name body)

-- | Construct a 'Term' for a function using the supplied function to construct the body.
--
--   This uses the approach described in _Using Circular Programs for Higher-Order Syntax_, Emil Axelsson, Koen Claessen: http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf
--
--   >>> lam id
--   Fix (Abs (Name 0) (Fix (Var (Name 0))))
--   >>> lam (\ x -> lam (const x))
--   Fix (Abs (Name 1) (Fix (Abs (Name 0) (Fix (Var (Name 1))))))
lam :: (Term Expr -> Term Expr) -> Term Expr
lam hoas = makeAbs n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)

maxBoundVariable :: Term Expr -> Maybe Name
maxBoundVariable = cata $ \ expr -> case expr of
  Abs name _ -> Just name
  _          -> foldr max Nothing expr

var :: Name -> Term Expr
var name = Fix (Var name)

(#) :: Term Expr -> Term Expr -> Term Expr
func # arg = Fix (App func arg)

infixl 9 #


makeLetRec :: Name -> Term Expr -> Term Expr
makeLetRec name body = Fix (LetRec name body)

letRec :: (Term Expr -> Term Expr) -> Term Expr
letRec hoas = makeLetRec n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)


unit :: Term Expr
unit = Fix Unit

pair :: Term Expr -> Term Expr -> Term Expr
pair fst snd = Fix (Pair fst snd)

tuple :: [Term Expr] -> Term Expr
tuple = foldr pair unit

pfst :: Term Expr -> Term Expr
pfst pair = Fix (Fst pair)

psnd :: Term Expr -> Term Expr
psnd pair = Fix (Snd pair)

bool :: Bool -> Term Expr
bool b = Fix (Bool b)

iff :: Term Expr -> Term Expr -> Term Expr -> Term Expr
iff c t e = Fix (If c t e)

cons :: Term Expr -> Term Expr -> Term Expr
cons head tail = Fix (Cons head tail)

nil :: Term Expr
nil = Fix Nil

list :: [Term Expr] -> Term Expr
list = foldr cons nil

unlist :: Term Expr -> Term Expr -> Term Expr -> Term Expr
unlist empty full list = Fix (Unlist empty full list)


instance (Substitutable ty ann, Functor expr) => Substitutable ty (Rec (Ann expr) ann) where
  substitute subst (Rec (In ann expr)) = Rec (In (substitute subst ann) (fmap (substitute subst) expr))

instance Monoid ann => Embeddable1 expr (Ann expr ann) where
  emb1 = In mempty

  unemb1 = Just . exprF
