module Analysis.Examples where

import Data.Expr as Expr
import Data.Name
import Data.Type as Type

foldr :: Term
foldr = rec (\ foldr -> lam (\ combine -> lam (\ seed -> lam (\ list -> unlist seed (lam (\ a -> lam (\ as -> combine # a # (foldr # combine # seed # as)))) list))))

foldrT :: PartialType
foldrT = (tvar (Name 0) .-> tvar (Name 1) .-> tvar (Name 1)) .-> tvar (Name 1) .-> listT (tvar (Name 0)) .-> tvar (Name 1)
