module XorInternal (eliminateXorInternal) where
import XorCnf
import XorGauss
import Generic
import Data.List
import Data.Maybe
eliminate :: [Clause] -> ([Clause], [Sub])
eliminate clauses = (clauses', subs)
    where
        cnf       = filter (not . isXor) clauses
        cnfVars   = nub (concatMap getVars cnf)
        xors      = filter isXor clauses
        xorOcc    = occurrences (concatMap getVars xors)
        potential = map fst $ filter (\(_,c) -> c == 1) xorOcc
        internal  = potential \\ cnfVars
        defs      = map findDef internal
        clauses'  = clauses \\ map snd defs
        subs      = [ SubDef v (removeVar v def) | (v,def) <- defs ]
        removeVar var (Xor p vars) = Xor p (vars \\ [var])
        findDef var = (var, fromJust def)
            where
                def = find (\c -> var `elem` getVars c) clauses


eliminateXorInternal :: [Clause] -> ([Clause], [Sub])
eliminateXorInternal clauses 
    | length clauses' < length clauses = again
    | otherwise = (clauses', subs)
    where
        (clauses', subs) = eliminate clauses
        (clauses'', subs') = eliminate clauses'
        again = (clauses'', subs' ++ subs)
