module Analysis.Examples where

import Data.Expr as Expr

foldr :: Term
foldr = rec (\ foldr -> lam (\ combine -> lam (\ seed -> lam (\ list -> unlist seed (lam (\ a -> lam (\ as -> combine # a # (foldr # combine # seed # as)))) list))))
