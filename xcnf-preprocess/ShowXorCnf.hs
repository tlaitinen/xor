module ShowXorCnf (showClause) where

import XorCnf
import qualified Data.Set as Set
showClause :: Clause -> String
showClause (Xor parity vars) = "x" ++ xorContent parity (Set.toList vars) ++ " 0"
    where
        xorContent :: Parity -> [Var] -> String
        xorContent Odd vars = concat $ map (\(Var x) -> " " ++ show x) vars
        xorContent Even ((Var v):vars) = " -" ++ show v ++ xorContent Odd vars
        xorContent Even _ = ""                                 
showClause (Or lits) = unwords (map showLit (Set.toList lits)) ++ " 0"
    where
        showLit (Lit Pos (Var v)) = show v
        showLit (Lit Neg (Var v)) = '-':show v
