module Analysis.Examples where

import Data.Expr as Expr
import Data.Type as Type

foldr :: Term
foldr = rec (\ foldr -> lam (\ combine -> lam (\ seed -> lam (\ list -> unlist seed (lam (\ a -> lam (\ as -> combine # a # (foldr # combine # seed # as)))) list))))

foldrT :: PartialType
foldrT = forAllT (\ each -> forAllT (\ result -> (each .-> result .-> result) .-> result .-> listT each .-> result))

-- $
-- >>> import Analysis.Elaboration
-- >>> import Control.Comonad (extract)
-- >>> () <$ partialToTotal (fst (runElab (elaborate Analysis.Examples.foldr >>= unify Analysis.Examples.foldrT . extract)))
-- Right ()
