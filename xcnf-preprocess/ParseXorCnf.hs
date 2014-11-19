module ParseXorCnf (readClause, readClauses) where
import qualified Data.ByteString.Char8 as BS
--import qualified Data.ByteString.Internal as BSI
import XorCnf
import Data.Maybe
import Data.List
import Data.Int

readClause :: BS.ByteString -> Clause
readClause s
    | BS.length s == 0 = error "Empty string"
    | (lastDigit s) /= 0 = error "Expected '0' as the last number"
    | ch == 'x' = readXorClause (nums s')
    | otherwise = readOrClause (nums s)
    where
        ch = BS.head s
        s' = BS.tail s
        maybeInts sx = catMaybes [  BS.readInt x | x <- BS.words sx ]      
        dimacs sx = [ x | (x,_) <- maybeInts sx ]
        nums sx = init (dimacs sx)
        lastDigit sx = last (dimacs sx)

readXorClause :: [Int] -> Clause
readXorClause nums = vars `seq` product `seq` newXor parity vars
    where       
        product = foldl' (*) 1 signs
        vars = [ Var (abs x) | x <- nums ]
        signs = [ sign x | x <- nums ]
        sign x 
            | x > 0 = 1
            | x < 0 = -1
            | otherwise = 0
        parity
            | product > 0  = Odd
            | otherwise = Even

readOrClause :: [Int] -> Clause
readOrClause nums = lits `seq` newOr lits
    where
        lits = [ lit x | x <- nums ]
        lit x 
            | x < 0 = Lit Neg (Var (abs x))
            | x > 0 = Lit Pos (Var x)
            | otherwise = error "Invalid literal '0'"



readClauses :: BS.ByteString -> [Clause]
readClauses text = clauses
    where
        dimacs = BS.lines text
        ignore s
            | BS.length s == 0 = True
            | x == 'p' || x == 'c' = True
            | otherwise            = False
            where x = BS.head s
        clauses = [ readClause line | line <- dimacs, not $ ignore line ]            

