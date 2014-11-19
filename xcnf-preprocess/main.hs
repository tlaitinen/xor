import XorCnf
import ParseXorCnf
import ShowXorCnf
import Preprocess
import Generic
import System.Console.GetOpt
import System.IO
import System.Environment
import Data.Maybe
import Data.List
import qualified Data.ByteString.Char8 as BS
import Verify
import ClauseSet

data Flag = Verbose | SolFile String | SubFile String | ElimXorInternal
          deriving (Show,Eq)
options :: [OptDescr Flag]
options = [ 
--    Option ['v'] ["verbose"] (NoArg Verbose)  "chatty output on stderr",
    Option ['t'] ["test"] (ReqArg SolFile "FILE") "solution FILE",
    Option ['s'] ["sub"] (ReqArg SubFile "FILE") "substitutions FILE"
--    Option ['e'] ["eliminate"] (NoArg ElimXorInternal) 
--                               "eliminate xor-internal variables"
    ]
    
preprocessOpts :: [String] -> IO ([Flag], FilePath)
preprocessOpts argv = 
    case getOpt RequireOrder options argv of
        (o,path:args,[]  ) -> return (o,path)
        (_,_,errs) -> error ((concat errs ++ usageInfo header options))
    where header = "Usage: preprocess [OPTION...] file"

printInstance :: FilePath -> (Maybe [Clause], [Sub]) -> IO()
printInstance subFile (Just clauses, subs) = do
    putStrLn $ "p cnf " ++ show varCount ++ " " ++ show clauseCount
    putStr $ unlines $ map showClause clauses'
    hPutStrLn stderr $ "Writing file " ++ subFile
    -- writeFile (subFile ++ ".xcnf") $ unlines $ map subToClause subs
    writeFile subFile $ show subs
    where
        subToClause (SubConst (Var v) const) 
            | const == True = show v ++ " 0"
            | const == False = "-" ++ show v ++ " 0"
        subToClause (SubLit (Var v) (Lit sign (Var v')))
            | sign == Pos = "-" ++ show v ++ " " ++ show v' ++ " 0"
            | sign == Neg = show v ++ " " ++ show v' ++ " 0"
        subtToClause _ = ""

        showSubPair sub = "  " ++ showSub sub
        showSub (SubLit (Var v) 
                        (Lit sign (Var v'))) = show v ++ " : " 
                                                      ++ showSign sign 
                                                      ++ show v'
        showSub (SubConst (Var v) const) = show v ++ " : " 
                                                  ++ (take 1 $ show const)
        showSign Pos = " "
        showSign Neg = "-"

        allVars = concat [ getVars c | c <- clauses ]
        (Var varCount) 
            | null allVars = (Var 0)
            | otherwise = maximum $ allVars
        clauses' = removeDuplicates (simplifyClauses clauses)
        clauseCount = length clauses'

printInstance _ (Nothing, _) = putStrLn "Unsatisfiable"    

isSolFile (SolFile _) = True
isSolFile _ = False
isSubFile (SubFile _) = True
isSubFile _ = False
getSubFilePath (SubFile path) = path
getSubFilePath _ = ""

testSolution :: Flag -> FilePath -> FilePath -> BS.ByteString -> IO()
testSolution (SolFile path) subFilePath path2 content = do
    modelFile <- readFile path
    let clauses = readClauses content
    subFile <- readFile subFilePath
    let subs = read subFile :: [Sub]
    putStrLn modelFile
    let preModel = (readModel . last . lines) modelFile    
    let model = totalModel preModel subs
    if verifyModel model clauses 
        then putStrLn $ unlines $ map showClause [ newOr [lit] | lit <- model ]
        else putStrLn "ERROR"

doPreprocess :: [Flag] -> [Clause] -> IO (Maybe [Clause], [Sub])
doPreprocess flags clauses = clauses `seq` do
    inst <- preprocess clauses
    return $ finish inst
    where 
        finish inst@(Just cs, subs) 
--            | ElimXorInternal `elem` flags = (Just clauses', subs' ++ subs)
--            | otherwise = (Just clauses, subs)
            = (Just clauses, subs)
            where
                clauses = allClauses cs
--                (clauses', subs') = eliminateXorInternalVars clauses
        finish inst@(Nothing, subs) = (Nothing, subs)


main = do

    args <- getArgs
    (flags, path) <- preprocessOpts args
    content <- BS.readFile path
    let solFile = find isSolFile flags
    let subFile = maybe (path ++ ".sub") getSubFilePath (find isSubFile flags)
    if isJust solFile 
        then testSolution (fromJust solFile) subFile path content
        else do
            let clauses = readClauses content
            inst <- doPreprocess flags clauses

        --    print $ instances  
            printInstance subFile inst
        --    mapM_ (printInstance $ path ++ ".sub") instances
