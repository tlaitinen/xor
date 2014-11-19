module XorCnfEqv (eqvPropagate) where
import XorCnf
import XorCnfProp
import qualified Data.Set as Set
import ClauseSet
import Test.HUnit



eqvProp :: Var -> Lit -> Clause -> Maybe Clause

eqvProp var (Lit sign var') xor@(Xor parity vars) 
    | hasVar = newVars `seq` newParity `seq` Just $! Xor newParity newVars
    | otherwise = Just xor
    where
        hasVar = var `Set.member` vars
        newParity 
            | sign == Neg && hasVar = inv parity
            | otherwise = parity
        newVars 
            | var' `Set.member` vars = vars `Set.difference` (Set.fromList [var,var'])
            | otherwise = Set.delete var $ Set.insert var' vars
 
eqvProp var lit (Or lits) = Just $ Or $! lits'
    where
        lits' = lits'' `seq` sub (Lit Pos var) lits''
        lits'' = lits `seq` sub (Lit Neg var) lits
        sub :: Lit -> Set.Set Lit -> Set.Set Lit
        sub l lits 
            | l `Set.member` lits = Set.insert (subLit l lit) $! Set.delete l lits
            | otherwise = lits
        subLit (Lit sign' var') (Lit sign with) = Lit (mulSign sign sign') with
eqvPropagate :: [(Var,Lit)] -> ClauseSet -> Maybe ClauseSet
eqvPropagate (eqv@(v,l):eqvs) cs = do
                              cs' <- propagate (eqvProp v l) cs (vars eqv)
--                            let cs' = updateClauses cs cids (eqvProp v l)
                              eqvPropagate eqvs $! cs'

--                            eqvPropagate eqvs $! cs `seq` cids `seq` updateClauses cs cids (\c -> Just c) -- (eqvProp v l)
    where vars (v1,Lit _ v2) = [v1,v2] 
          cids = clausesOfVars cs (vars eqv)
eqvPropagate _ cs = Just cs


tests = test [ 
    "test1" ~: "eqvProp" ~: 
        eqvProp (Var 4) (Lit Neg (Var 5)) (newOr [Lit Pos (Var 5), Lit Neg (Var 6)])
                ~=?   Just (newOr  [Lit Pos (Var 5), Lit Neg (Var 6)]),
    "test2" ~: "eqvProp" ~: 
        eqvProp (Var 4) (Lit Neg (Var 5)) (newOr [Lit Pos (Var 4), Lit Neg (Var 6)])
                ~=?   Just (newOr  [Lit Neg (Var 5), Lit Neg (Var 6)]),
    "test3" ~: "eqvProp" ~: 
        eqvProp (Var 4) (Lit Neg (Var 5)) (newXor Even [Var 4, Var 6])
                ~=?   Just (newXor Odd [Var 5, Var 6]),
    "test4" ~: "eqvProp" ~: 
       eqvProp (Var 4) (Lit Neg (Var 5)) (newXor Even [Var 4, Var 5])
                ~=?   Just (newXor Odd []),
    "test5" ~: "eqvProp" ~: 
       eqvProp (Var 4) (Lit Neg (Var 5)) (newXor Even [Var 4, Var 5, Var 6])
                ~=?   Just (newXor Odd [Var 6])


    ]



