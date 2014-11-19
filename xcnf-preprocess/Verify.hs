module Verify (readModel,
               totalModel,
               verifyModel,
               tests) where
import XorCnf
import XorCnfUnit
import Data.Maybe
import Preprocess
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.HUnit hiding (State)
import Data.List
import Control.Monad.State

readModel :: String -> [Lit]
readModel lits 
    | lastZero == "0" = [ mkLit n | n <- nums ]
    | otherwise = error "Expected '0' as the last digit"
    where
        tokens = words lits
        nums = [ read x :: Int | x <- init tokens ]
        lastZero = last tokens
        mkLit num = Lit (sign num) (Var (abs num))
        sign num 
            | num < 0 = Neg
            | num > 0 = Pos
            | otherwise = error "Invalid literal: '0'"

subToLit :: [Sub] -> State (Map.Map Var Sign) [Lit]            
subToLit ((SubLit v (Lit sign v')):subs) = do
    vMap <- get
    let sign' = Map.lookup v' vMap
    put $ Map.insert v (newSign sign') vMap
    rest <- subToLit subs
    return $ (Lit (newSign sign') v) : rest
    where
        newSign :: Maybe Sign -> Sign
        newSign (Just sign') = mulSign sign' sign
        newSign Nothing = error $ "Missing value for " ++ show v'
subToLit ((SubConst v b):subs) = do
    vMap <- get
    let sign = boolToSign b
    put $ Map.insert v sign vMap
    rest <- subToLit subs                         
    return $ (Lit sign v) : rest                 
subToLit ((SubDef v xor@(Xor parity vars)):subs) = do
    vMap <- get
    let varsTrue = map (\v -> Map.findWithDefault 
                                 (error $ "Missing value for " ++ show v)
                                 v vMap)
                       (getVars xor) 
    let numTrue = length $ filter (==Pos) varsTrue
    let satisfied = isSatisfied numTrue
    let sign = getSign satisfied
    put $ Map.insert v sign vMap
    rest <- subToLit subs
    return $ (Lit sign v) : rest
    where
        isSatisfied numTrue
            | parity == Even = numTrue `mod` 2 == 0
            | parity == Odd = numTrue `mod` 2 == 1
        getSign satisfied                
            | satisfied = Neg
            | otherwise = Pos
                           


subToLit [] = return []
subVar (SubLit var _) = var
subVar (SubDef var _) = var                           
subVar (SubConst var _) = var

totalModel :: [Lit] -> [Sub] -> [Lit]
totalModel lits subs = knownLits ++ extraLits
    where
        subVars = map subVar subs
        knownVars = [ v | (Lit _ v) <- lits ] \\ subVars
        knownLits = [ lit | lit@(Lit _ v) <- lits, v `elem` knownVars ]
        valueMap = Map.fromList [ (v, sign) | (Lit sign v) <- knownLits ]

        extraLits = evalState (subToLit subs) valueMap


verifyModel :: [Lit] -> [Clause] -> Bool
verifyModel lits clauses = verify lits  clauses

verify :: [Lit] -> [Clause] -> Bool
verify lits clauses = all (==True) (map testClause clauses)
    where
        testClause :: Clause -> Bool
        testClause clause = agree (Just clause) (clauseLits clause)
        valueMap = Map.fromList [ (v, sign) | (Lit sign v) <- lits ]

        mkLit v 
            | isJust sign = Just $ Lit (fromJust sign) v
            | otherwise = Nothing
            where
                sign = Map.lookup v valueMap
        clauseLits :: Clause -> [Lit]
        clauseLits c = catMaybes $ map mkLit (getVars c)

agree :: Maybe Clause -> [Lit] -> Bool    
agree Nothing _ = True
agree (Just clause) (l:ls) = agree (unitProp l clause) ls
agree (Just clause) [] = isSatisfiable clause
isSatisfiable (Or lits)
        | Set.size lits == 0 = False
isSatisfiable (Xor Odd vars) 
        | Set.size vars == 0 = False
isSatisfiable _ = True


tests = test [
        "test1" ~: "verify" ~: 
            verify [(Lit Pos (Var 1))] [newOr [Lit Pos (Var 1)]]
                ~=? True,
        "test2" ~: "verify" ~: 
            verify [(Lit Pos (Var 1))] [newOr [Lit Neg (Var 1)]]
                ~=? False,
        "test3" ~: "verify" ~:               
            verify [Lit Pos (Var 1),Lit Neg (Var 2)] 
                   [newOr [Lit Pos (Var 1), Lit Pos (Var 2)],
                    newOr [Lit Neg (Var 1), Lit Neg (Var 2)],
                    newOr [Lit Pos (Var 1), Lit Neg (Var 2)]]
                ~=? True,
        "test4" ~: "verify" ~:               
            verify [Lit Neg (Var 1),Lit Neg (Var 2)] 
                   [newOr [Lit Pos (Var 1), Lit Pos (Var 2)],
                    newOr [Lit Neg (Var 1), Lit Neg (Var 2)],
                    newOr [Lit Pos (Var 1), Lit Neg (Var 2)]]
                ~=? False,
        "test5" ~: "verify" ~:               
            verify [Lit Pos (Var 1),Lit Neg (Var 2)] 
                   [newOr [Lit Pos (Var 1), Lit Pos (Var 2)],
                    newOr [Lit Neg (Var 1), Lit Neg (Var 2)],
                    newOr [Lit Pos (Var 1), Lit Neg (Var 2)],
                    newXor Even [],
                    newXor Odd [Var 1],
                    newXor Odd [Var 1, Var 2]]
                ~=? True,
        "test6" ~: "agree" ~:
            agree Nothing [Lit Pos (Var 1)] ~=? True,
        "test7" ~: "agree" ~:            
            agree (Just (newOr [Lit Neg (Var 1), Lit Pos (Var 2)])) 
                  [Lit Pos (Var 1), Lit Neg (Var 2)] ~=? False

    ]
    
    
