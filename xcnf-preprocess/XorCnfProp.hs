module XorCnfProp (propagate) where

import XorCnf
import Data.Maybe
import Data.List
import ClauseSet

partialPropagate :: (Clause -> Maybe Clause) -> ClauseSet -> [Var] -> ClauseSet
partialPropagate prop cs vars = updateClauses cs (clausesOfVars cs vars) prop       

propagate :: (Clause -> Maybe Clause) -> ClauseSet -> [Var] -> Maybe ClauseSet
propagate prop cs vars = simplify $! partialPropagate prop cs vars
    where
        simplify cs
            | isUnsat cs = Nothing
            | otherwise = Just cs

