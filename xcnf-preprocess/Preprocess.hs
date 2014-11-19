module Preprocess (preprocess, removeDuplicates, simplifyClauses, Sub(..)) where

import XorCnf
import XorCnfUnit
import XorCnfEqv
import XorCnfSimplify
import System.IO
import XorTernary
-- import XorInternal
-- import XorGauss
import ShowXorCnf
import Data.Maybe
import Data.List
import ClauseSet
import qualified Data.Set as Set
findLits :: ClauseSet -> [Lit]
findLits cs = catMaybes $ map matchLit (allClauses cs)

matchLit :: Clause -> Maybe Lit
matchLit (Or lits) 
    | Set.size lits == 1 = Just (head $ Set.toList lits)
matchLit (Xor parity vars) 
    | Set.size vars == 1 = Just $ Lit (sign parity) (head $ Set.toList vars)
    where
        sign :: Parity -> Sign
        sign Odd = Pos
        sign Even = Neg
matchLit _ = Nothing

findEqv :: [Clause] -> [(Var, Lit)]
findEqv clauses = catMaybes $ map matchEqv clauses


matchEqv :: Clause -> Maybe (Var, Lit)
matchEqv (Xor parity vars) 
    | Set.size vars == 2 = Just (var1, (Lit sign var2))
        where            
            (var1:var2:_) = Set.toList vars
            sign 
                | parity == Odd = Neg
                | parity == Even = Pos

matchEqv _ = Nothing    


step :: (Maybe ClauseSet, [Sub]) -> IO (Maybe ClauseSet, [Sub])
step inst@((Just clauseSet), subs) = do
    if not (null lits)
        then do
            hPutStrLn stderr $ "Propagating " ++ show (length lits) ++ " literals"
            step $! (upStep lits)
        else do
            if not (null eqvs)
                then do
                    
                    hPutStrLn stderr $ "Propagating " ++ show (length eqvs) ++ " equivalences"
                    step $! (eqvStep eqvs)
                else do
                    if not (null binXors) && False
                        then do
                            hPutStrLn stderr $ show (length binXors) ++ " new equivalences by combining ternary xors"
                            step $! binXorStep
                        else do
                            hPutStrLn stderr $ "Propagation saturated"
                            return $! inst
    where
        lits = findLits clauseSet
        eqvs = findEqv (allClauses clauseSet)
        upStep lits = (unitPropagate lits clauseSet,
                       upStepSubs lits subs)
        upStepSubs ((Lit sign var):lits) subs = SubConst var (sign2bool sign):upStepSubs lits subs
        upStepSubs [] subs = subs                                                                              
                                                                       
        sign2bool Pos = True
        sign2bool Neg = False
        eqvStep eqvs  = (eqvPropagate eqvs clauseSet,
                         eqvStepSubs eqvs subs)
        eqvStepSubs :: [(Var,Lit)] -> [Sub] -> [Sub]
        eqvStepSubs ((v,l):eqvs) subs = (SubLit v l):(eqvStepSubs eqvs subs)
        eqvStepSubs [] subs = subs                                              
--        clauses' = gaussEliminate leastOccurrencesVar 
--                                  smallestFormulaClause 
--                                  clauses
        binXors = combineTernaryXors (allClauses clauseSet)
                                                          
        binXorStep = eqvStep (findEqv binXors)
--        newBinXors = length binXors > 0
--        canGauss  = isJust (findLits clauses') || isJust (findEqv clauses')
--        gaussStep = (Just clauses', subs)                                       
step a@(Nothing, _) = return a



preprocess :: [Clause] -> IO (Maybe ClauseSet, [Sub])
preprocess clauses = cs `seq` step $ (Just cs, [])
        where cs = makeClauseSet clauses

--eliminateXorInternalVars :: [Clause] -> ([Clause], [Sub])
--eliminateXorInternalVars = (eliminateXorInternal .
--                                (gaussEliminate xorInternalVars
--                                                smallestFormulaClause))

removeDuplicates :: [Clause] -> [Clause]
removeDuplicates = fmap head.group.sort

simplifyClauses :: [Clause] -> [Clause]
simplifyClauses clauses = catMaybes $ map simplify clauses
