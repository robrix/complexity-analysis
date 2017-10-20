{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Context
import Data.Expr as Expr
import Data.FreeVariables
import Data.Functor.Foldable (Fix(..))
import Data.Name
import Data.Rec
import Data.Semiring
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab size = StateT (Subst (Rec (Sized Type) size))
               ( ReaderT (Context (Rec (Sized Type) size))
               ( FreshT
               ( Except (Error (Rec (Sized Type) size)))))

data Error ty
  = FreeVariable Name
  | TypeMismatch ty ty
  | InfiniteType Name ty
  deriving (Eq, Ord, Show)

runElab :: Elab size a -> Either (Error (Rec (Sized Type) size)) (a, Subst (Rec (Sized Type) size))
runElab = fmap fst . runExcept . flip runFreshT (Name 0) . flip runReaderT (Context []) . flip runStateT mempty

elaborate :: Semiring size => Term Expr -> Elab size (Rec (Ann Expr) (Rec (Sized Type) size))
elaborate term = do
  term' <- infer term
  subst <- get
  let Rec (Ann ty tm) = substitute subst term'
  pure (Rec (Ann (generalize ty) tm))

infer :: Semiring size => Term Expr -> Elab size (Rec (Ann Expr) (Rec (Sized Type) size))
infer (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (contextExtend n (tvar t)) (infer b)
  pure (Rec (Ann (tvar t .-> ann b') (Abs n b')))
infer (Fix (Var name)) = do
  context <- ask
  case contextLookup name context of
    Just ty -> pure (Rec (Ann ty (Var name)))
    Nothing -> throwError (FreeVariable name)
infer (Fix (App f a)) = do
  t <- fresh
  a' <- infer a
  f' <- check f ((one <>) `modifySize` (ann a' .-> tvar t))
  pure (Rec (Ann (tvar t) (App f' a')))
infer (Fix (LetRec n b)) = do
  t <- fresh
  local (contextExtend n (tvar t)) (check b (tvar t))
infer (Fix Expr.Unit) = pure (Rec (Ann unitT Expr.Unit))
infer (Fix (Pair fst snd)) = do
  fst' <- infer fst
  snd' <- infer snd
  pure (Rec (Ann (ann fst' .* ann snd') (Pair fst' snd')))
infer (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (Rec (Ann (tvar t1) (Fst pair')))
infer (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- check pair (tvar t1 .* tvar t2)
  pure (Rec (Ann (tvar t2) (Snd pair')))
infer (Fix (Expr.Bool b)) = pure (Rec (Ann boolT (Expr.Bool b)))
infer (Fix (If c t e)) = do
  c' <- check c boolT
  t' <- infer t
  e' <- infer e
  result <- unify (ann t') (ann e')
  pure (Rec (Ann result (If c' t' e')))
infer (Fix (Cons h t)) = do
  a <- fresh
  h' <- check h (tvar a)
  t' <- check t (listT (tvar a))
  pure (Rec (Ann (listT (tvar a)) (Cons h' t')))
infer (Fix Nil) = Rec . flip Ann Nil . listT . tvar <$> fresh
infer (Fix (Unlist empty full list)) = do
  a <- fresh
  empty' <- infer empty
  full' <- check full (tvar a .-> listT (tvar a) .-> ann empty')
  list' <- check list (listT (tvar a))
  pure (Rec (Ann (ann empty') (Unlist empty' full' list')))

check :: Semiring size => Term Expr -> Rec (Sized Type) size -> Elab size (Rec (Ann Expr) (Rec (Sized Type) size))
check term ty = do
  term' <- infer term
  termTy <- unify (ann term') ty
  pure (Rec (Ann termTy (expr term')))


unify :: Monoid size => Rec (Sized Type) size -> Rec (Sized Type) size -> Elab size (Rec (Sized Type) size)
unify (Rec (Sized s1 t1)) (Rec (Sized s2 t2))
  | TVar name1 <- t1                   = bind name1 (Rec (Sized s2 t2))
  |                   TVar name2 <- t2 = bind name2 (Rec (Sized s1 t1))
  | ForAll{}   <- t1, ForAll{}   <- t2 = fresh >>= \ n -> makeForAllT n <$> unify (specialize t1 n) (specialize t2 n)
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise                          = throwError (TypeMismatch (Rec (Sized s1 t1)) (Rec (Sized s2 t2)))

bind :: Monoid size => Name -> Rec (Sized Type) size -> Elab size (Rec (Sized Type) size)
bind name ty
  | TVar name' <- sizedType (unRec ty)
  , name == name'                      = pure ty
  | Set.member name (freeVariables ty) = throwError (InfiniteType name ty)
  | otherwise                          = do
    subst <- get
    let ty' = substitute subst ty
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)

instance FreeVariables ty => FreeVariables (Error ty) where
  freeVariables (FreeVariable _)     = mempty -- The free variable here is a term variable, not a type variable.
  freeVariables (TypeMismatch t1 t2) = freeVariables t1 `mappend` freeVariables t2
  freeVariables (InfiniteType n b)   = Set.insert n (freeVariables b)
