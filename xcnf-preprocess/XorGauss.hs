module XorGauss (gaussEliminate,
                 gauss,
                 leastOccurrencesVar,
                 xorInternalVars,
                 smallestFormulaClause,
                 VarHeuristic,
                 ClauseHeuristic, 
                 substitute,
                 Sub(..),
                 addXor,
                 ) where

import XorCnf
import XorCnfSimplify
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Generic
import Test.HUnit
import Data.Set



type Row = Int
type VarHeuristic    = [Clause] -> [Var]
type ClauseHeuristic = Var -> [Clause] -> Maybe Clause

gaussEliminate :: VarHeuristic -> ClauseHeuristic -> [Clause] -> [Clause]
gaussEliminate varH clauseH clauses = gauss varOrder clauseH xors ++ cnf
    where
        varOrder = varH clauses
        xors = filter isXor clauses
        cnf = filter (not . isXor) clauses



varOccurrences :: [Clause] -> [(Var, Int)]
varOccurrences clauses = Map.toList $ Map.unionsWith (+) occMaps
    where
        occMaps = map (Map.fromList . occurrences . getVars) clauses

varCount :: [Clause] -> Int
varCount clauses = sum $ map (length . getVars) clauses

leastFirst :: (Ord a, Ord b) => (a,b) -> (a,b) -> Ordering
leastFirst (v,c) (v',c') 
    | cmp /= EQ = cmp
    | otherwise = compare v v' 
    where cmp = compare c c'


xorInternalVars :: VarHeuristic
xorInternalVars clauses = (map fst varCounts) \\ (map fst cnfOcc)
    where
        occs = (varOccurrences $ clauses)
        varCounts = sortBy leastFirst occs
        cnf       = filter (not . isXor) clauses
        cnfOcc    = occurrences (concatMap getVars cnf)

leastOccurrencesVar :: VarHeuristic
leastOccurrencesVar clauses = (map fst varCounts)
    where
        occs = (varOccurrences $ clauses)
        varCounts = sortBy leastFirst occs
        cnf       = filter (not . isXor) clauses
        cnfOcc    = occurrences (concatMap getVars cnf)


smallestFormulaClause :: ClauseHeuristic
smallestFormulaClause var clauses = find (\c -> var `Set.member` (getVars) c) clauses
-- $ fst $ minimumBy leastFirst ranking
--    where
--        potential = filter (\c -> var `elem` (getVars c)) clauses
--        ranking :: [(Clause, Int)]
--        ranking = [ (c, varCount (substitute var c clauses)) | c <- potential ]


gauss :: [Var] -> ClauseHeuristic -> [Clause] -> [Clause]
gauss (var:vars) clauseH clauses 
    | isJust c = jc : binXors ++ gauss vars clauseH clauses''
    | otherwise = gauss vars clauseH clauses
    where
        c         = clauseH var clauses
        jc        = fromJust c
        clauses'  = substitute var jc $ delete jc clauses
        shorter n c = (length . getVars) c < n
        binXors   = filter (shorter 3) clauses'
        clauses'' 
            | (not . null) binXors = filter (not . (shorter 3)) clauses'
            | otherwise = clauses'
gauss [] _ clauses = clauses       

substitute :: Var -> Clause -> [Clause] -> [Clause]
substitute var c clauses = catMaybes $ map add clauses
    where
        add c'@(Xor _ vars)
            | var `Set.member` vars = addXor c c'
            | otherwise = Just c'
        add (Or _) = error "Cannot substitute a literal in an or-clause"

addXor :: Clause -> Clause -> Maybe Clause             
addXor (Xor p vs) (Xor p' vs') = simplify $ Xor (addParity p p') (vs ++ vs')
addXor _ _ = error "One of the operands is not a xor-clause"   


tests = test [ 
    "test1" ~: "addXor" ~: 
        addXor (Xor Even [Var 1, Var 2])
                (Xor Odd [Var 2, Var 3])
                ~=?   Just (Xor Odd [Var 1, Var 3]),

    "test2" ~: "leastOccurrencesVar 1" ~: 
        leastOccurrencesVar [Or [Lit Pos (Var 1), Lit Neg (Var 2)],
                              Xor Even [Var 1, Var 2, Var 4],
                              Xor Odd [Var 2, Var 3, Var 5]]
            ~=? [Var 1, Var 2, Var 3, Var 4, Var 5],

    "test3" ~: "leastOccurrencesVar 2" ~:
        leastOccurrencesVar [] ~=? [],

    "test4" ~: "substitute" ~:
        substitute (Var 1) (Xor Odd [Var 1, Var 2, Var 3])
                   [Xor Even [Var 1, Var 2, Var 5],
                    Xor Odd [Var 2, Var 3, Var 4],
                    Xor Odd [Var 1, Var 5, Var 6]]
                    ~=? [Xor Odd [Var 3, Var 5],
                         Xor Odd [Var 2, Var 3, Var 4],
                         Xor Even [Var 2, Var 3, Var 5, Var 6]],

    "test5" ~: "gauss" ~:
        gauss [Var 1] smallestFormulaClause 
              [Xor Odd [Var 1, Var 2, Var 3],
               Xor Even [Var 1, Var 4, Var 5],
               Xor Odd [Var 1, Var 2, Var 4]]
           ~=?
                [Xor Odd [Var 1, Var 2, Var 3],
                 Xor Even [Var 3, Var 4],
                 Xor Odd [Var 2,Var 3, Var 4,Var 5]]

            
    ]
