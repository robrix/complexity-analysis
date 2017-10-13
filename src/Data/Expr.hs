{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Data.Expr where

import Data.Functor.Foldable (Recursive(..), Fix(..))
import Data.Name

data Expr a
  = Abs Name a
  | App a a
  | Var Name
  | Lit Bool
  | If a a a
  | Pair a a
  | Fst a
  | Snd a
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

type Term = Fix Expr

makeAbs :: Name -> Term -> Term
makeAbs name body = Fix (Abs name body)

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

lit :: Bool -> Term
lit b = Fix (Lit b)

iff :: Term -> Term -> Term -> Term
iff c t e = Fix (If c t e)

pair :: Term -> Term -> Term
pair fst snd = Fix (Pair fst snd)

pfst :: Term -> Term
pfst pair = Fix (Fst pair)

psnd :: Term -> Term
psnd pair = Fix (Snd pair)
