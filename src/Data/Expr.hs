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

makeAbs :: Name -> Fix Expr -> Fix Expr
makeAbs name body = Fix (Abs name body)

lam :: (Fix Expr -> Fix Expr) -> Fix Expr
lam hoas = makeAbs n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)

maxBoundVariable :: Fix Expr -> Maybe Name
maxBoundVariable = cata $ \ expr -> case expr of
  Abs name _ -> Just name
  _          -> foldr max Nothing expr

(#) :: Fix Expr -> Fix Expr -> Fix Expr
func # arg = Fix (App func arg)

infixl 9 #

var :: Name -> Fix Expr
var name = Fix (Var name)

bool :: Bool -> Fix Expr
bool b = Fix (Lit b)

iff :: Fix Expr -> Fix Expr -> Fix Expr -> Fix Expr
iff c t e = Fix (If c t e)

pair :: Fix Expr -> Fix Expr -> Fix Expr
pair fst snd = Fix (Pair fst snd)

pfst :: Fix Expr -> Fix Expr
pfst pair = Fix (Fst pair)

psnd :: Fix Expr -> Fix Expr
psnd pair = Fix (Snd pair)
