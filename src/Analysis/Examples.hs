module Analysis.Examples where

import Data.Expr as Expr
import Data.Type as Type

foldr :: Term Expr
foldr = rec (\ foldr -> lam (\ combine -> lam (\ seed -> lam (\ list -> unlist seed (lam (\ a -> lam (\ as -> combine # a # (foldr # combine # seed # as)))) list))))

foldrT :: Partial Type Error
foldrT = forAllT (\ each -> forAllT (\ result -> (each .-> result .-> result) .-> result .-> listT each .-> result))

-- $
-- >>> () <$ partialToTotal (fst (runElab (elaborate Analysis.Examples.foldr >>= unify Analysis.Examples.foldrT . ann)))
-- Right ()


map :: Term Expr
map = rec (\ map -> lam (\ f -> lam (\ list -> unlist nil (lam (\ a -> lam (\ as -> cons (f # a) (map # f # as)))) list)))

mapT :: Partial Type Error
mapT = forAllT (\ element -> forAllT (\ mapped -> (element .-> mapped) .-> listT element .-> listT mapped))

-- $
-- >>> () <$ partialToTotal (fst (runElab (elaborate Analysis.Examples.map >>= unify Analysis.Examples.mapT . ann)))
-- Right ()


-- $setup
-- >>> import Analysis.Elaboration
