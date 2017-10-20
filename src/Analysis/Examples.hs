{-# LANGUAGE FlexibleContexts #-}
module Analysis.Examples where

import Data.Expr as Expr
import Data.Functor.Foldable (Base, Recursive)
import Data.Type as Type

foldr :: Term Expr
foldr = letRec (\ recur -> lam (\ combine -> lam (\ seed -> lam (\ list -> unlist seed (lam (\ a -> lam (\ as -> combine # a # (recur # combine # seed # as)))) list))))

foldrT :: (Typical t, Typical1 (Base t), Recursive t) => t
foldrT = forAllT (\ each -> forAllT (\ result -> (each .-> result .-> result) .-> result .-> listT each .-> result))

-- $
-- >>> () <$ partialToTotal (fst (runElab (elaborate Analysis.Examples.foldr >>= unify (totalToPartial Analysis.Examples.foldrT) . ann)))
-- Right ()


map :: Term Expr
map = letRec (\ recur -> lam (\ f -> lam (\ list -> unlist nil (lam (\ a -> lam (\ as -> cons (f # a) (recur # f # as)))) list)))

mapT :: (Typical t, Typical1 (Base t), Recursive t) => t
mapT = forAllT (\ element -> forAllT (\ mapped -> (element .-> mapped) .-> listT element .-> listT mapped))

-- $
-- >>> () <$ partialToTotal (fst (runElab (elaborate Analysis.Examples.map >>= unify (totalToPartial Analysis.Examples.mapT) . ann)))
-- Right ()


-- $setup
-- >>> import Analysis.Elaboration
