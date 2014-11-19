module XorCnfUnit (unitPropagate, unitProp) where

import XorCnf
import Data.Maybe
import XorCnfProp
import ClauseSet
import qualified Data.Set as Set

unitProp :: Lit -> Clause -> Maybe Clause
unitProp lit (Or lits) 
        | lit `Set.member` lits = Nothing
        | otherwise =  Just $! Or $! Set.delete (neg lit) lits

unitProp lit@(Lit sign var) (Xor parity vars) = newVars `seq` newParity `seq` Just $! Xor newParity newVars
    where             
        newVars = Set.delete var vars
        newParity
            | (var `Set.member` vars) && (sign == Pos) = inv parity
            | otherwise = parity

unitPropLits :: [Lit] -> Clause -> Maybe Clause
unitPropLits (lit:lits) clause = case (unitProp lit clause) of
                    (Just clause') -> clause' `seq` (Just clause') `seq` unitPropLits lits clause'
                    Nothing -> Nothing
unitPropLits [] clause = Just clause

unitPropagate :: [Lit] -> ClauseSet -> Maybe ClauseSet
unitPropagate (lit@(Lit _ v):lits) cs = do
                                cs' <- propagate (unitProp lit) cs [ v ]
                                unitPropagate lits cs'
unitPropagate _ cs = Just cs
