module ClauseSet (ClauseSet,
                  ClauseId,
                  emptyClauseSet,                 
                  makeClauseSet,
                  addClause,
                  removeClause,
                  updateClauses,                  
                  lookupClause,
                  clausesOfVars,
                  allClauses,
                  isUnsat
        ) where

import qualified Data.IntMap as Map
import qualified Data.IntSet as Set
import qualified Data.Set as RSet
import Data.Maybe
import XorCnf
import Data.List
import Data.Int

type ClauseId = Int
type ClauseIdMap = Map.IntMap Set.IntSet
type ClauseMap = Map.IntMap Clause 
data ClauseSet = ClauseSet {
    clauses       :: !ClauseMap,
    clausesOf     :: !ClauseIdMap,
    unsat         :: !Bool

    } deriving (Show)

emptyClauseSet :: ClauseSet
emptyClauseSet = ClauseSet {
        clauses = Map.empty,
        clausesOf = Map.empty,
        unsat = False
    }

clauseIdMapOfClause :: ClauseId -> Clause -> ClauseIdMap
clauseIdMapOfClause cid c = Map.fromList $! list
    where list = [ (fromIntegral v, Set.singleton cid) | (Var v) <- getVars c ]

makeClauseSet :: [Clause] -> ClauseSet
makeClauseSet clauses = foldl' addClause emptyClauseSet clauses

maxClauseId :: ClauseSet -> ClauseId
maxClauseId cs 
    | Map.null (clauses cs) = 0
    | otherwise              = fst $ Map.findMax (clauses cs)


isUnsatClause :: Clause -> Bool
isUnsatClause (Or lits) = RSet.null lits
isUnsatClause (Xor p vars) = RSet.null vars && p == Odd

addClause :: ClauseSet -> Clause -> ClauseSet
addClause cs c = cs `seq` c `seq` cidMap `seq` clausesOf' `seq` unsat' `seq` clauses' `seq` cs {
        clauses   = clauses',
        clausesOf = clausesOf',
        unsat = unsat'
    } where cid = 1 + maxClauseId cs
            cidMap = (clauseIdMapOfClause cid c)
            clauses' = c `seq` Map.insert cid c (clauses cs)
            clausesOf' =  Map.unionWith Set.union 
                                       (clausesOf cs) 
                                       cidMap 
            unsat' = unsat cs || isUnsatClause c





removeClause :: ClauseSet -> ClauseId -> ClauseSet
removeClause cs cid = cs {
        clauses   = Map.delete cid (clauses cs),
        clausesOf = Map.unionWith Set.difference
                                  (clausesOf cs)
                                  (clauseIdMapOfClause cid c)
    } where c = Map.findWithDefault (Or (RSet.fromList [])) cid (clauses cs)

clauseDiff :: Clause -> Clause -> (Set.IntSet, Set.IntSet)
clauseDiff c1 c2 = (Set.difference vars1 vars2, Set.difference vars2 vars1)
        where vars1 = Set.fromList $ [ v | (Var v) <- getVars c1 ]
              vars2 = Set.fromList $ [ v | (Var v) <- getVars c2 ]


updateClausesOf :: ClauseIdMap -> ClauseId -> Clause -> Clause -> ClauseIdMap
updateClausesOf cidMap cid prev current = cidMap'
    where
        cidMap' = cidMap'' `seq` Map.unionWith Set.difference cidMap'' removedCidmap
        cidMap'' = Map.unionWith Set.union cidMap addedCidmap
        (removed, added) = clauseDiff prev current
        cidSet = Set.singleton cid
        removedCidmap = Map.fromList [ (v, cidSet) | v <- Set.toList removed ]
        addedCidmap = Map.fromList [ (v, cidSet) | v <- Set.toList added ]


updateClauses :: ClauseSet -> [ClauseId] -> (Clause -> Maybe Clause) -> ClauseSet
updateClauses cs (cid:cids) f = updateClauses cs' cids f 
    where c' = f current
          c | isJust c' = fromJust c'
            | otherwise = Or (RSet.fromList [])
          current = lookupClause cs cid
          cs' = cs {
                clauses = Map.update f cid (clauses cs),
                clausesOf = updateClausesOf (clausesOf cs) cid current c,
                unsat = unsat'
          }
          unsat' = unsat cs || (isUnsatClause c && isJust c')
updateClauses cs _ _ = cs


lookupClause :: ClauseSet -> ClauseId -> Clause
lookupClause cs cid = Map.findWithDefault (Or (RSet.fromList [])) cid (clauses cs)

clausesOfVars :: ClauseSet -> [Var] -> [ClauseId]
clausesOfVars cs vars = Set.toList $ Set.unions $ 
                        [ Map.findWithDefault Set.empty (fromIntegral v) (clausesOf cs)
                          | (Var v) <- vars ]

allClauses :: ClauseSet -> [Clause]
allClauses cs = Map.elems (clauses cs)

isUnsat :: ClauseSet -> Bool
isUnsat cs = unsat cs

