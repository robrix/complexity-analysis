{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Context
import Data.Expr as Expr
import Data.FreeVariables
import Data.Functor.Foldable (Fix(..))
import Data.Maybe (fromMaybe)
import Data.Name
import Data.Rec
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab ann = StateT (Subst (Partial Error (Ann Type ann))) (ReaderT (Context (Partial Error (Ann Type ann))) Fresh)

runElab :: Elab ann a -> (a, Subst (Partial Error (Ann Type ann)))
runElab = fst . flip runFresh (Name 0) . flip runReaderT (Context []) . flip runStateT mempty

elaborate :: Monoid ann => Term Expr -> Elab ann (Rec (Ann Expr) (Partial Error (Ann Type ann)))
elaborate term = do
  term' <- infer term
  subst <- get
  let Rec (Ann ty tm) = substitute subst term'
  pure (Rec (Ann (generalize ty) tm))

infer :: Monoid ann => Term Expr -> Elab ann (Rec (Ann Expr) (Partial Error (Ann Type ann)))
infer (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (contextExtend n (tvar t)) (infer b)
  pure (Rec (Ann (tvar t .-> ann b') (Abs n b')))
infer (Fix (Var name)) = do
  context <- ask
  pure (Rec (Ann (fromMaybe (Fault (FreeVariable name)) (contextLookup name context)) (Var name)))
infer (Fix (App f a)) = do
  t <- fresh
  a' <- infer a
  f' <- check f (ann a' .-> tvar t)
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

check :: Monoid ann => Term Expr -> Partial Error (Ann Type ann) -> Elab ann (Rec (Ann Expr) (Partial Error (Ann Type ann)))
check term ty = do
  term' <- infer term
  termTy <- unify (ann term') ty
  pure (Rec (Ann termTy (expr term')))


unify :: Monoid ann => Partial Error (Ann Type ann) -> Partial Error (Ann Type ann) -> Elab ann (Partial Error (Ann Type ann))
unify (Fault e) _         = pure (Fault e)
unify _         (Fault e) = pure (Fault e)
unify (Cont (Ann a1 t1)) (Cont (Ann a2 t2))
  | TVar name1 <- t1                   = bind name1 (Ann a2 t2)
  |                   TVar name2 <- t2 = bind name2 (Ann a1 t1)
  | ForAll{}   <- t1, ForAll{}   <- t2 = fresh >>= \ n -> makeForAllT n <$> unify (specialize t1 n) (specialize t2 n)
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise                          = pure (Fault (TypeMismatch (Ann a1 t1) (Ann a2 t2)))

bind :: Monoid ann => Name -> Ann Type ann (Partial Error (Ann Type ann)) -> Elab ann (Partial Error (Ann Type ann))
bind name (Ann ann ty)
  | TVar name' <- ty, name == name'         = pure (emb ty)
  | Set.member name (freeVariables1 ty) = pure (Fault (InfiniteType name (Ann ann ty)))
  | otherwise                               = do
    subst <- get
    let ty' = substitute subst (emb ty)
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)
