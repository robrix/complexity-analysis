{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
module Data.Complexity where

import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Foldable (fold)
import Data.Function (on)
import Data.Functor.Foldable (Recursive(..), Base)
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Semigroup (Semigroup(..))
import qualified Data.Set as Set

newtype Name = Name Int
  deriving (Enum, Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)


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

makeAbs :: Name -> Term Expr -> Term Expr
makeAbs name body = In (Abs name body)

lam :: (Term Expr -> Term Expr) -> Term Expr
lam hoas = makeAbs n body
  where n = maybe (Name 0) succ (maxBoundVariable body)
        body = hoas (var n)

maxBoundVariable :: Term Expr -> Maybe Name
maxBoundVariable = cata $ \ expr -> case expr of
  Abs name _ -> Just name
  _          -> foldr max Nothing expr

(#) :: Term Expr -> Term Expr -> Term Expr
func # arg = In (App func arg)

infixl 9 #

var :: Name -> Term Expr
var name = In (Var name)

bool :: Bool -> Term Expr
bool b = In (Lit b)

iff :: Term Expr -> Term Expr -> Term Expr -> Term Expr
iff c t e = In (If c t e)

pair :: Term Expr -> Term Expr -> Term Expr
pair fst snd = In (Pair fst snd)

pfst :: Term Expr -> Term Expr
pfst pair = In (Fst pair)

psnd :: Term Expr -> Term Expr
psnd pair = In (Snd pair)


data Type a
  = TVar Name
  | ForAll Name a
  | a :-> a
  | Bool
  | a :* a
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

infixr 0 :->
infixl 7 :*

freeTypeVariables :: CoAttr Type a -> Set.Set Name
freeTypeVariables = cata $ \ ty -> case ty of
  ContinueF (TVar name)        -> Set.singleton name
  ContinueF (ForAll name body) -> Set.delete name body
  _                            -> fold ty

returnType :: CoAttr Type a -> Maybe (CoAttr Type a)
returnType (Continue (_ :-> returnTy)) = Just returnTy
returnType (Stop err)                  = Just (Stop err)
returnType _                           = Nothing

fstType :: CoAttr Type a -> Maybe (CoAttr Type a)
fstType (Continue (fstTy :* _)) = Just fstTy
fstType (Stop err)              = Just (Stop err)
fstType _                       = Nothing

sndType :: CoAttr Type a -> Maybe (CoAttr Type a)
sndType (Continue (_ :* sndTy)) = Just sndTy
sndType (Stop err)              = Just (Stop err)
sndType _                       = Nothing


newtype Term f = In { out :: f (Term f) }

type instance Base (Term f) = f

instance Functor f => Recursive (Term f) where project = out

deriving instance Eq (f (Term f)) => Eq (Term f)
deriving instance Ord (f (Term f)) => Ord (Term f)
deriving instance Read (f (Term f)) => Read (Term f)
deriving instance Show (f (Term f)) => Show (Term f)

data Attr f a = Attr { attr :: a, hole :: f (Attr f a) }

data AttrF f a b = AttrF { attrF :: a, holeF :: f b }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

type instance Base (Attr f a) = AttrF f a

instance Functor f => Recursive (Attr f a) where project (Attr a f) = AttrF a f

deriving instance (Eq (f (Attr f a)), Eq a) => Eq (Attr f a)
deriving instance (Ord (f (Attr f a)), Ord a) => Ord (Attr f a)
deriving instance (Read (f (Attr f a)), Read a) => Read (Attr f a)
deriving instance (Show (f (Attr f a)), Show a) => Show (Attr f a)

data CoAttr f a
  = Stop a
  | Continue (f (CoAttr f a))

data CoAttrF f a b
  = StopF a
  | ContinueF (f b)
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

type instance Base (CoAttr f a) = CoAttrF f a

instance Functor f => Recursive (CoAttr f a) where
  project (Stop a)     = StopF a
  project (Continue f) = ContinueF f

deriving instance (Eq (f (CoAttr f a)), Eq a) => Eq (CoAttr f a)
deriving instance (Ord (f (CoAttr f a)), Ord a) => Ord (CoAttr f a)
deriving instance (Read (f (CoAttr f a)), Read a) => Read (CoAttr f a)
deriving instance (Show (f (CoAttr f a)), Show a) => Show (CoAttr f a)


newtype Env a = Env { getEnv :: [(Name, a)] }
  deriving (Eq, Monoid, Ord, Read, Semigroup, Show)

envLookup :: Name -> Env a -> Maybe a
envLookup name = lookup name . getEnv

envExtend :: Name -> a -> Env a -> Env a
envExtend name value = Env . ((name, value) :) . getEnv

newtype Subst value = Subst { getSubst :: [(Name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance Binder value => Semigroup (Subst value) where
  Subst s1 <> Subst s2 = Subst (List.unionBy ((==) `on` fst) (map (second (substitute (Subst s1))) s2) s1)

instance Binder value => Monoid (Subst value) where
  mempty = Subst []
  mappend = (<>)

substLookup :: Name -> Subst value -> Maybe value
substLookup name = lookup name . getSubst

substDelete :: Name -> Subst value -> Subst value
substDelete name = Subst . filter ((/= name) . fst) . getSubst

substSingleton :: Name -> value -> Subst value
substSingleton name value = Subst [(name, value)]

substExtend :: Binder value => Name -> value -> Subst value -> Subst value
substExtend name value = (substSingleton name value <>)


class Binder value where
  substitute :: Subst value -> value -> value

instance Binder (CoAttr Type Error) where
  substitute = flip (cata (\ ty subst -> case ty of
    ContinueF (TVar name)        -> fromMaybe (Continue (TVar name)) (substLookup name subst)
    ContinueF (ForAll name body) -> Continue (ForAll name (body (substDelete name subst)))
    ContinueF other              -> Continue (($ subst) <$> other)
    StopF err                    -> Stop err))


data Error
  = FreeVariable Name
  | TypeMismatch (Type (CoAttr Type Error)) (Type (CoAttr Type Error))
  | InfiniteType Name (CoAttr Type Error)
  deriving (Eq, Ord, Read, Show)

type Elab = StateT (Subst (CoAttr Type Error)) (ReaderT (Env (Term Type)) (Fresh Name))

runElab :: Elab a -> (a, Subst (CoAttr Type Error))
runElab = fst . flip runFresh (Name 0) . flip runReaderT mempty . flip runStateT mempty

substElaborated :: Attr Expr (CoAttr Type Error) -> Subst (CoAttr Type Error) -> Attr Expr (CoAttr Type Error)
substElaborated = cata (\ (AttrF ty expr) subst -> Attr (substitute subst ty) (($ subst) <$> expr))


elaborate :: Term Expr -> Elab (Attr Expr (CoAttr Type Error))
elaborate (In (Abs n b)) = do
  t <- fresh
  b' <- local (envExtend n (In (TVar t))) (elaborate b)
  pure (Attr (Continue (Continue (TVar t) :-> attr b')) (Abs n b'))
elaborate (In (App f a)) = do
  t <- fresh
  f' <- elaborate f
  a' <- elaborate a
  fTy <- unify (attr f') (Continue (attr a' :-> Continue (TVar t)))
  pure (Attr (fromMaybe (Continue (TVar t)) (returnType fTy)) (App f' a'))
elaborate (In (Var name)) = do
  env <- ask
  pure (Attr (maybe (Stop (FreeVariable name)) (cata Continue) (envLookup name env)) (Var name))
elaborate (In (Lit b)) = pure (Attr (Continue Bool) (Lit b))
elaborate (In (If c t e)) = do
  c' <- elaborate c
  t' <- elaborate t
  e' <- elaborate e
  result <- unify (attr t') (attr e')
  pure (Attr result (If c' t' e'))
elaborate (In (Pair fst snd)) = do
  fst' <- elaborate fst
  snd' <- elaborate snd
  pure (Attr (Continue (attr fst' :* attr snd')) (Pair fst' snd'))
elaborate (In (Fst pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elaborate pair
  pairTy <- unify (attr pair') (Continue (Continue (TVar t1) :* Continue (TVar t2)))
  pure (Attr (fromMaybe (Continue (TVar t1)) (fstType pairTy)) (Fst pair'))
elaborate (In (Snd pair)) = do
  t1 <- fresh
  t2 <- fresh
  pair' <- elaborate pair
  pairTy <- unify (attr pair') (Continue (Continue (TVar t1) :* Continue (TVar t2)))
  pure (Attr (fromMaybe (Continue (TVar t2)) (sndType pairTy)) (Fst pair'))


unify :: CoAttr Type Error -> CoAttr Type Error -> Elab (CoAttr Type Error)
unify (Stop err1)   _             = pure (Stop err1)
unify _             (Stop err2)   = pure (Stop err2)
unify (Continue t1) (Continue t2)
  | t1 == t2  = pure (Continue t2)
  | otherwise = case (t1, t2) of
    (a1 :-> b1,  a2 :-> b2)  -> (Continue .) . (:->) <$> unify a1 a2 <*> unify b1 b2
    (TVar name1, _)          -> bind name1 (Continue t2)
    (_,          TVar name2) -> bind name2 (Continue t1)
    (t1,         t2)         -> pure (Stop (TypeMismatch t1 t2))

bind :: Name -> CoAttr Type Error -> Elab (CoAttr Type Error)
bind name ty
  | Set.member name (freeTypeVariables ty) = pure (Stop (InfiniteType name ty))
  | otherwise                              = modify (substExtend name ty) >> pure ty
