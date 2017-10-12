{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
module Data.Complexity where

import Control.Monad ((<=<))
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (first, second)
import Data.Foldable (fold)
import Data.Function (on)
import Data.Functor.Foldable (Recursive(..), Base)
import Data.Functor.Identity
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Semigroup (Semigroup(..))
import qualified Data.Set as Set

newtype Name = Name String
  deriving (Eq, Ord, Read, Show)

data Complexity i
  = Constant i
  deriving (Eq, Ord, Read, Show)


data Expr a
  = Abs Name a
  | App a a
  | Var Name
  | Lit Bool
  | If a a a
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

newtype TName = TName Int
  deriving (Enum, Eq, Ord, Read, Show)

data Type a
  = TVar TName
  | ForAll TName a
  | a :-> a
  | Bool
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

infixr 0 :->

freeTypeVariables :: CoAttr Type a -> Set.Set TName
freeTypeVariables = cata $ \ ty -> case ty of
  ContinueF (TVar name)        -> Set.singleton name
  ContinueF (ForAll name body) -> Set.delete name body
  _                            -> fold ty


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

newtype Subst name value = Subst { getSubst :: [(name, value)] }
  deriving (Eq, Foldable, Functor, Ord, Read, Show, Traversable)

instance Binder name value => Semigroup (Subst name value) where
  Subst s1 <> Subst s2 = Subst (List.unionBy ((==) `on` fst) (map (second (substitute (Subst s1))) s2) s1)

instance Binder name value => Monoid (Subst name value) where
  mempty = Subst []
  mappend = (<>)

substLookup :: Eq name => name -> Subst name value -> Maybe value
substLookup name = lookup name . getSubst

substDelete :: Eq name => name -> Subst name value -> Subst name value
substDelete name = Subst . filter ((/= name) . fst) . getSubst

substSingleton :: name -> value -> Subst name value
substSingleton name value = Subst [(name, value)]

substExtend :: Binder name value => name -> value -> Subst name value -> Subst name value
substExtend name value = (substSingleton name value <>)


class Eq name => Binder name value where
  substitute :: Subst name value -> value -> value

instance Binder TName (CoAttr Type Error) where
  substitute = flip (cata (\ ty s -> case ty of
    ContinueF (TVar name)        -> fromMaybe (Continue (TVar name)) (substLookup name s)
    ContinueF (ForAll name body) -> Continue (ForAll name (body (substDelete name s)))
    ContinueF other              -> Continue (($ s) <$> other)
    StopF err                    -> Stop err))


type Error = String

type Elab = StateT (Subst TName (CoAttr Type Error)) (ReaderT (Env (Term Type)) (Fresh TName))

runElab :: Elab (Attr Expr (CoAttr Type Error)) -> Attr Expr (CoAttr Type Error)
runElab = uncurry substituteIn . fst . runIdentity . flip runFreshT (TName 0) . flip runReaderT mempty . flip runStateT mempty
  where substituteIn = cata (\ (AttrF ty expr) subst -> Attr (substitute subst ty) (($ subst) <$> expr))


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
  case fTy of
    Continue (_ :-> returnTy) -> pure (Attr returnTy            (App f' a'))
    _                         -> pure (Attr (Continue (TVar t)) (App f' a'))
elaborate (In (Var n)) = do
  env <- ask
  pure (Attr (maybe (Stop ("undefined variable: " ++ show n)) (cata Continue) (envLookup n env)) (Var n))
elaborate (In (Lit b)) = pure (Attr (Continue Bool) (Lit b))
elaborate (In (If c t e)) = do
  c' <- elaborate c
  t' <- elaborate t
  e' <- elaborate e
  result <- unify (attr t') (attr e')
  pure (Attr result (If c' t' e'))


unify :: CoAttr Type Error -> CoAttr Type Error -> Elab (CoAttr Type Error)
unify (Stop err1)   (Stop err2)   = pure (Stop (err1 ++ err2))
unify (Stop err1)   _             = pure (Stop err1)
unify _             (Stop err2)   = pure (Stop err2)
unify (Continue t1) (Continue t2)
  | t1 == t2  = pure (Continue t2)
  | otherwise = case (t1, t2) of
    (a1 :-> b1,  a2 :-> b2)  -> (Continue .) . (:->) <$> unify a1 a2 <*> unify b1 b2
    (TVar name1, _)          -> bind name1 (Continue t2)
    (_,          TVar name2) -> bind name2 (Continue t1)
    (t1,         t2)         -> pure (Stop ("Cannot unify incompatible types " ++ show t1 ++ " and " ++ show t2))

bind :: TName -> CoAttr Type Error -> Elab (CoAttr Type Error)
bind name ty
  | Set.member name (freeTypeVariables ty) = pure (Stop ("Cannot construct the infinite type " ++ show name ++ " = " ++ show ty))
  | otherwise                              = modify (substExtend name ty) >> pure ty


class Monad monad => MonadFresh name monad | monad -> name where
  fresh :: monad name


newtype FreshT name monad result = FreshT { runFreshT :: name -> monad (result, name) }

type Fresh name = FreshT name Identity

instance Functor monad => Functor (FreshT name monad) where
  fmap f (FreshT run) = FreshT (fmap (first f) . run)

instance Monad monad => Applicative (FreshT name monad) where
  pure = FreshT . (pure .) . (,)

  f <*> a = FreshT (\ s -> do
    (f', s') <- runFreshT f s
    (a', s'')<- runFreshT a s'
    pure (f' a', s''))

instance Monad monad => Monad (FreshT name monad) where
  return = pure

  a >>= f = FreshT (uncurry runFreshT . first f <=< runFreshT a)

instance (Enum name, Monad monad) => MonadFresh name (FreshT name monad) where
  fresh = FreshT (\ s -> pure (s, succ s))

instance MonadFresh name monad => MonadFresh name (ReaderT read monad) where
  fresh = lift fresh

instance MonadFresh name monad => MonadFresh name (StateT state monad) where
  fresh = lift fresh
