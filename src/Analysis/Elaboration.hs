{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Analysis.Elaboration where

import Control.Comonad (extract)
import Control.Comonad.Cofree
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Env
import Data.Expr as Expr
import Data.Functor.Foldable (Fix(..))
import Data.Name
import qualified Data.Set as Set
import Data.Subst
import Data.Type as Type

type Elab = StateT (Subst PartialType) (ReaderT (Env Name) (Fresh Name))

type PartialElabTerm = Cofree Expr PartialType

runElab :: Elab a -> (a, Subst PartialType)
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

elaborate :: Term -> Elab PartialElabTerm
elaborate (Fix (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n t) (elaborate b)
  pure ((tvar t .-> extract b') :< Abs n b')
elaborate (Fix (App f a)) = do
  t <- fresh
  a' <- elaborate a
  f' <- elabCheck f (extract a' .-> tvar t)
  pure (tvar t :< App f' a')
elaborate (Fix (Var name)) = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) tvar (envLookup name env) :< Var name)
elaborate (Fix Expr.Unit) = pure (unitT :< Expr.Unit)
elaborate (Fix (Pair fst snd)) = do
  fst' <- elaborate fst
  snd' <- elaborate snd
  pure (extract fst' .* extract snd' :< Pair fst' snd')
elaborate (Fix (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elabCheck pair (tvar t1 .* tvar t2)
  pure (tvar t1 :< Fst pair')
elaborate (Fix (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elabCheck pair (tvar t1 .* tvar t2)
  pure (tvar t2 :< Snd pair')
elaborate (Fix (Expr.Bool b)) = pure (boolT :< Expr.Bool b)
elaborate (Fix (If c t e)) = do
  c' <- elabCheck c boolT
  t' <- elaborate t
  e' <- elaborate e
  result <- unify (extract t') (extract e')
  pure (result :< If c' t' e')
elaborate (Fix (Cons h t)) = do
  a <- fresh
  h' <- elabCheck h (tvar a)
  t' <- elabCheck t (listT (tvar a))
  pure (listT (tvar a) :< Cons h' t')
elaborate (Fix Nil) = (:< Nil) . listT . tvar <$> fresh
elaborate (Fix (Unlist empty full list)) = do
  a <- fresh
  empty' <- elaborate empty
  full' <- elabCheck full (tvar a .-> listT (tvar a) .-> extract empty')
  list' <- elabCheck list (listT (tvar a))
  pure (extract empty' :< Unlist empty' full' list')

elabCheck :: Term -> PartialType -> Elab PartialElabTerm
elabCheck term ty = do
  term' <- elaborate term
  termTy <- unify (extract term') ty
  pure (termTy :< unwrap term')

check :: Term -> Maybe PartialType -> Elab PartialType
check term (Just ty) = check term Nothing >>= unify ty
check (Fix (Abs n b)) Nothing = do
  t <- fresh
  b' <- local (envExtend n t) (check b Nothing)
  pure (tvar t .-> b')
check (Fix (App f a)) Nothing = do
  t <- fresh
  a' <- check a Nothing
  _ <- check f (Just (a' .-> tvar t))
  pure (tvar t)
check (Fix (Var name)) Nothing = do
  env <- ask
  pure (maybe (Pure (FreeVariable name)) tvar (envLookup name env))
check (Fix Expr.Unit) Nothing = pure unitT
check (Fix (Pair fst snd)) Nothing = do
  fst' <- check fst Nothing
  snd' <- check snd Nothing
  pure (fst' .* snd')
check (Fix (Fst pair)) Nothing = do
  t1 <- fresh
  t2 <- fresh
  _ <- check pair (Just (tvar t1 .* tvar t2))
  pure (tvar t1)
check (Fix (Snd pair)) Nothing = do
  t1 <- fresh
  t2 <- fresh
  _ <- check pair (Just (tvar t1 .* tvar t2))
  pure (tvar t2)
check (Fix (Expr.Bool _)) Nothing = pure boolT
check (Fix (If c t e)) Nothing = do
  _ <- check c (Just boolT)
  t' <- check t Nothing
  e' <- check e Nothing
  unify t' e'
check (Fix (Cons h t)) Nothing = do
  a <- fresh
  _ <- check h (Just (tvar a))
  _ <- check t (Just (listT (tvar a)))
  pure (listT (tvar a))
check (Fix Nil) Nothing = listT . tvar <$> fresh
check (Fix (Unlist empty full list)) Nothing = do
  a <- fresh
  empty' <- check empty Nothing
  _ <- check full (Just (tvar a .-> listT (tvar a) .-> empty'))
  _ <- check list (Just (listT (tvar a)))
  pure empty'


unify :: PartialType -> PartialType -> Elab PartialType
unify (Pure e1) _         = pure (Pure e1)
unify _         (Pure e2) = pure (Pure e2)
unify (Free t1) (Free t2)
  | TVar name1 <- t1                   = bind name1 t2
  |                   TVar name2 <- t2 = bind name2 t1
  | a1 :-> b1  <- t1, a2 :-> b2  <- t2 = (.->) <$> unify a1 a2 <*> unify b1 b2
  | a1 :*  b1  <- t1, a2 :*  b2  <- t2 = (.*)  <$> unify a1 a2 <*> unify b1 b2
  | Type.Unit  <- t1, Type.Unit  <- t2 = pure unitT
  | Type.Bool  <- t1, Type.Bool  <- t2 = pure boolT
  | List a1    <- t1, List a2    <- t2 = listT <$> unify a1 a2
  | otherwise = pure (Pure (TypeMismatch t1 t2))

bind :: Name -> Type PartialType -> Elab PartialType
bind name ty
  | TVar name' <- ty, name == name'        = pure (wrap ty)
  | Set.member name (freeTypeVariables ty) = pure (Pure (InfiniteType name ty))
  | otherwise                              = do
    subst <- get
    let ty' = substitute subst (wrap ty)
    maybe (put (substExtend name ty' subst) >> pure ty') (unify ty') (substLookup name subst)
