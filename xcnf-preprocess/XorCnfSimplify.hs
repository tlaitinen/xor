module XorCnfSimplify (simplify, Sub(..)) where

import XorCnf
import qualified Data.Set as Set
import Data.List
import Generic
data Sub = SubLit Var Lit 
         | SubDef Var Clause
         | SubConst Var Bool deriving (Read,Show)

simplify :: Clause -> Maybe Clause
simplify (Or lits)
        | isTautology = Nothing
        | otherwise = Just $ Or lits
        where
            isTautology = True `elem` (map hasNegLit (Set.toList lits))
            hasNegLit lit = neg lit `Set.member` lits
simplify (Xor parity vars) 
    | parity == Even && (Set.size vars == 0) = Nothing
    | otherwise = Just (Xor parity vars)

