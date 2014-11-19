module XorTernary (combineTernaryXors, tests) where
import XorCnf
--import XorGauss
import XorCnfSimplify
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Test.HUnit
import qualified Data.Set as Set

key :: Var -> Var -> (Var,Var)
key x y 
    | x < y = (x,y)
    | otherwise = (y,x)

addXor :: Clause -> Clause -> Maybe Clause             
addXor (Xor p vs) (Xor p' vs') = simplify $ newXor (addParity p p') (Set.toList (union `Set.difference` intersect))
    where intersect = vs `Set.intersection` vs'
          union = vs `Set.union` vs'

addXor _ _ = error "One of the operands is not a xor-clause"   

   
combineTernaryXors :: [Clause] -> [Clause]
combineTernaryXors clauses = binXors
    where
        triXors = [ c | c <- clauses, isXor c, length (getVars c) == 3 ]

        xorGroups = map (map snd) (xorPairGroups triXors)
        xorGroups' = [ (head xg, tail xg) | xg <- xorGroups,
                                             length xg > 1 ]
        binXors = catMaybes [ (addXor xor xor') | (xor, xors) <- xorGroups',
                                                 xor' <- xors ]

varPairs :: Clause -> [((Var, Var), Clause)]                                                 
varPairs xor@(Xor _ vars) = [ (key v1 v2,xor), 
                                    (key v1 v3,xor),
                                    (key v2 v3,xor) ]
    where [v1,v2,v3] = Set.toList vars                                        

xorPairGroups :: [Clause] -> [[((Var, Var), Clause)]]    
xorPairGroups triXors = groupBy sameGroup $ sortBy cmpGroup 
                                                   (concatMap varPairs triXors)
    where
        sameGroup (k1,_) (k2,_) = k1 == k2
        cmpGroup (k1,_) (k2,_) = compare k1 k2











tests = test [
        "test1" ~: "varPairs" ~: varPairs (newXor Even [Var 4, Var 3, Var 8])
                       ~=? [ ((Var 3, Var 4), newXor Even [Var 4, Var 3, Var 8]),
                             ((Var 4, Var 8), newXor Even [Var 4, Var 3, Var 8]),
                             ((Var 3, Var 8), newXor Even [Var 4, Var 3, Var 8]) ],
        "test2" ~: "xorPairGroups" ~:  
            xorPairGroups [newXor Even [Var 1, Var 2, Var 3],
                           newXor Odd [Var 1, Var 2, Var 4]]
                        ~=?  
                          [[((Var 1, Var 2), newXor Even [Var 1, Var 2, Var 3]),
                          ((Var 1, Var 2), newXor Odd [Var 1, Var 2, Var 4])],
                          [((Var 1, Var 3), newXor Even [Var 1, Var 2, Var 3])],
                          [((Var 1, Var 4), newXor Odd [Var 1, Var 2, Var 4])],
                          [((Var 2, Var 3), newXor Even [Var 1, Var 2, Var 3])],
                          [((Var 2, Var 4), newXor Odd [Var 1, Var 2, Var 4])]]
    ]
