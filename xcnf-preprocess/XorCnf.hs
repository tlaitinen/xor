module XorCnf (
    Var(..),
    VarId,
    Sign(..),
    Lit(..),
    Parity(..),
    Clause(..),
    mulSign, -- Sign -> Sign -> Sign
    addParity, -- Parity -> Parity -> Parity
    neg, -- Lit -> Lit
    inv, -- Parity -> Parity
    getVars, -- :: Clause -> [Var]
    isXor, -- :: Clause -> Bool
    boolToSign, -- Bool -> Sign
    newXor,
    newOr
) where
import qualified Data.Set as Set



type VarId = Int
data Var = Var !VarId
           deriving (Show, Eq, Ord, Read)

data Sign = Pos | Neg 
          deriving (Show, Eq, Ord, Read)    
    
data Lit = Lit Sign Var
         deriving (Show, Eq, Read)

data Parity = Even | Odd
            deriving (Show, Eq, Ord, Read)

type LitSet = Set.Set Lit
type VarSet = Set.Set Var

data Clause = Or !LitSet | Xor !Parity !VarSet
            deriving (Show, Eq, Read)

instance Ord Clause where
    compare (Xor _ _) (Or _) = LT
    compare (Or _) (Xor _ _) = GT
    compare (Or x) (Or y)    = compare x y
    compare (Xor p1 x) (Xor p2 y) 
        | x == y = compare p1 p2
        | otherwise = compare x y

instance Ord Lit where 
    compare (Lit s1 v1) (Lit s2 v2) 
        | v1 == v2 = compare s1 s2
        | otherwise = compare v1 v2

mulSign :: Sign -> Sign -> Sign
mulSign Pos Pos = Pos
mulSign Pos Neg = Neg
mulSign Neg Pos = Neg
mulSign Neg Neg = Pos

addParity :: Parity -> Parity -> Parity
addParity Even Even = Even
addParity Even Odd = Odd
addParity Odd Even = Odd
addParity Odd Odd = Even

neg :: Lit -> Lit
neg (Lit Pos a) = Lit Neg a
neg (Lit Neg a) = Lit Pos a

inv :: Parity -> Parity
inv Even = Odd
inv Odd = Even

getVars :: Clause -> [Var]
getVars (Or lits) = [ v | (Lit _ v) <- Set.toList lits ]
getVars (Xor _ vars) = Set.toList vars

isXor :: Clause -> Bool
isXor (Xor _ _) = True
isXor _ = False

boolToSign :: Bool -> Sign
boolToSign True = Pos
boolToSign False = Neg

newXor :: Parity -> [Var] -> Clause
newXor p vars = Xor p $! (Set.fromList vars)

newOr :: [Lit] -> Clause
newOr lits = Or $! (Set.fromList lits)
