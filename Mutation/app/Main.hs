{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Boogie.AST
import Boogie.TypeChecker
import Boogie.Position
import qualified Boogie.Tokens as T
import Transformations
import Interface
import Pretty
import qualified Boogie.Parser as BoogieParser
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import System.Exit
import System.Environment
import System.Directory
import Data.Maybe
import Data.Aeson
import Data.List (unionBy, inits, nub) 
import qualified Data.ByteString.Lazy as B
import Control.Lens
import Control.Monad
import Control.Monad.State
import System.Random

{- rewrite -}
data Mutant = Mutant {
    prog       :: [Program] -- Each mutant can contain multiple fragments
  , sourcePath :: String    -- source program filePath
  , source     :: Program   -- source program 
  , mutation   :: [Trans]   -- chain of mutations 
  }

numOfFrags :: Mutant -> Int
numOfFrags = length . prog 

instance Eq Mutant where
  a == b = prog a == prog b -- TODO* fix equality on lists 

instance Pretty Mutant where
  pretty mutant
    | numOfFrags mutant == 1 = header $+$ pretty (head $ prog mutant)
    | otherwise = header   -- multiple fragments 
    where header = vsep $ map text [T.commentStart,
                                    "SOURCE  : " ++ sourcePath mutant,
                                    "MUChain : " ++ (show $ pretty (mutation mutant)),
                                    T.commentEnd]

writeToFile :: String -> (Int, Mutant) -> IO ()
writeToFile prefix (index, m) = do
  createDirectory dirName 
  writeOut (dirName ++ "/" ++ prefix ++ "_" ++ show index) m
  where dirName = concat ["./" ++ prefix ++ "_", show index]


writeOut :: FilePath -> Mutant -> IO ()
writeOut filePath mutant
  | numOfFrags mutant == 1 = writeFile (filePath ++ ".bpl") (show $ pretty mutant)
  | otherwise = mapM_ (\(part, frag) -> writeFile (filePath ++ show part ++ ".bpl") frag) 
    $ zip [1..] [ show $ header $+$ pretty frag | frag <- prog mutant]
    where header = pretty mutant

-- TODO fix this clumsyness (with proper handles) ...
showOut :: Mutant -> IO ()
showOut mutant
  | numOfFrags mutant == 1 = print $ pretty mutant
  | otherwise = mapM_ (\(part, frag) -> print frag) 
    $ zip [1..] [ header $+$ pretty frag | frag <- prog mutant]
    where header = pretty mutant

parseAndTypecheck f = do 
  res <- parseFromFile BoogieParser.program f
  case res of
    Left parseErr -> print parseErr >> exitFailure
    Right prog -> case typeCheckProgram prog of
      Left typeCheckErr -> print (typeErrorsDoc typeCheckErr) >> exitFailure
      Right ctx -> return (prog, ctx) 

readConfig confF = do
  config <- B.readFile confF
  case (decode config :: Maybe Config) of
    Nothing -> error "Failed to decode config.json"
    Just cof -> return cof 

generateMutations :: Program -> Int -> WeightedList String -> IO [Trans]
generateMutations prog n wlist = do 
  let list = jitter wlist
  names <- randomSelect n list []
  -- print $ inits names
  muts <- mapM (getMut prog) names
  -- print muts 
  return $ muts 

randomSelect :: Int -> [String] -> [String] -> IO [String]
randomSelect i list pool = 
  if i == 0 
  then return pool
  else do 
    p <- randomPick (length list - 1)
    let picked = list !! p 
    randomSelect (i-1) list $ pool ++ [picked]

-- core logic for random mutations 
getMut :: Program -> String -> IO Trans
getMut (Program decls _) "S1" = do
  from <- randomPick (length decls - 1)
  to <- randomPick (length decls - 1)  
  -- return $ Trans (concat ["S1_", show from, "_", show to]) (\p -> [swapDecl p (from, to)])
  return $ Trans "S1" (\p -> [swapDecl p (from, to)])
getMut (Program decls _) "S5" = do
  return $ s5
getMut (Program decls _) "S6" = do
  splitAt <- randomPick (length decls - 1)
  return $ s6 splitAt
getMut (Program decls _) "S7" = do
  from <- randomPick (length decls - 1)
  to <- randomPick (length decls - 1)  
  return $ s7 (from, to)
getMut (Program decls _) "G2" = do
  r <- randomPick (length decls - 1)
  return $ g2 r
getMut (Program decls _) "G10" = do
  r <- randomPick (length decls - 1)
  return $ g10 r
getMut (Program decls _) "L1" = do
  from <- randomPick (length decls - 1)
  -- to <- randomPick (length decls - 1)
  r <- randomPick (length decls - 1)  
  return $ l1 r (from, from + 1)
getMut (Program decls _) "L2" = do
  r <- randomPick (length decls - 1)  
  return $ l2 r 
getMut (Program decls _) "L4" = do
  r <- randomPick (length decls - 1)  
  return $ l4 r 
getMut (Program decls _) "L5" = do
  r <- randomPick (length decls - 1)  
  return $ l5 r 
getMut (Program decls _) "L6" = do
  from <- randomPick (length decls - 1)
  to <- randomPick (length decls - 1)  
  return $ l6 (from, to)
getMut (Program decls _) "L8" = do
  r <- randomPick (length decls - 1)  
  return $ l8 r 




xrayLoop :: Int -> [Trans] -> [Mutant] -> IO [Mutant]
xrayLoop 0 _ mutantPool = return mutantPool
xrayLoop numberOfMutants tranPool mutantPool = do
  index <- randomPick (length tranPool - 1)
  index2 <- randomPick (length mutantPool - 1)
  let mu = tranPool !! index
      mo = mutantPool !! index2 --(index `mod` (length mutantPool))
      origin = head mutantPool
      intake = if length mutantPool == 1
               then origin { prog = (trans mu) $ source origin, mutation = [mu] }
               else mo { prog = (trans mu) $ source mo, mutation = (mutation mo) ++ [mu] }
  if intake `elem` mutantPool
    then xrayLoop numberOfMutants tranPool $ mutantPool
    else do 
    nextPool <- xrayLoop (numberOfMutants - 1) tranPool $ mutantPool ++ [intake]
    putStrLn "-----"
    showOut intake
    putStrLn "-----"
    return nextPool


xrayLoop2 :: Int -> Int -> [Trans] -> [Mutant] -> IO [Mutant]
xrayLoop2 0 _ _ mutantPool = do
  putStrLn "attempts exhausted"
  putStrLn ("with #mutants = " ++ (show $ length mutantPool))
  return mutantPool
xrayLoop2 _ 0 _ mutantPool = do
  putStrLn "goal of mutants reached" 
  return $ nub mutantPool
xrayLoop2 att numberOfMutants tranPool mutantPool = do
  index <- randomPick (length tranPool - 1)
  index2 <- randomPick (length mutantPool - 1)
  let mu = tranPool !! index
      mo = mutantPool !! index2 --(index `mod` (length mutantPool))
      origin = head mutantPool
      intake = if length (prog mo) == 1 
               then Mutant ((trans mu) $ (head (prog mo))) (sourcePath mo) (source mo) ((mutation mo) ++ [mu])
               else Mutant ((trans mu) $ (source mo)) (sourcePath mo) (source mo) ((mutation mo) ++ [mu])  
  if intake `elem` mutantPool
    then do
    --putStrLn $ "failed with: " ++ show mu
    xrayLoop2 (att - 1) numberOfMutants (tranPool) $ mutantPool
    else do
    -- putStrLn $ "added with: " ++ show mu    
    nextPool <- xrayLoop2 att (numberOfMutants - 1) (tranPool) $ mutantPool ++ [intake]
    -- putStrLn "-----"
    -- showOut intake
    -- putStrLn "-----"
    return nextPool



validName :: Int -> IO String
validName r = do
  n <- randomName r
  return n 

-- NOTE ration must be higher than 2:1 
mainWithConfig f_config = do
  config <- readConfig f_config
  (sourceProg, ctx) <- parseAndTypecheck $ sourceBoogie config
  --print $ allGlobalIDs sourceProg -- tested 
  muts <- generateMutations sourceProg (mutationLevels config) (mutationRatio config)
  let origin = Mutant [sourceProg] (sourceBoogie config) sourceProg [] 
  mutants <- xrayLoop2 (mutationAttempts config) (numberOfMutants config) muts [origin]
  if (outputToFile config)
    then do
    mapM_ (writeToFile (prefix config)) (zip [1..] mutants)
    else do
    print $ length mutants
  if (verbose config)
    then do
    prettyPrint mutants
    else do 
    return ()
  

main = do
  args <- getArgs 
  mainWithConfig (head args)


{- frequency fiddling -}
type WeightedList a = [(a, Int)]

jitter :: WeightedList a -> [a]
jitter wlist = concat [ replicate i a | (a, i) <- wlist ]

{- end -}



t_config = "./config.json"


prettyPrint p = print $ pretty p 


testJSONRead confJ = do
  config <- B.readFile confJ
  case (decode config :: Maybe Config) of
    Nothing -> error "Failed to decode config.json"
    Just cof -> do
      let list = jitter $ mutationRatio cof
      mutations <- ranPool list []
      -- print mutations
      (prog, ctx) <- parseAndTypecheck (sourceBoogie cof)
      pool <- mutationGenLoop 10 mutations prog []
      prettyPrint pool


mutationGenLoop i mutations prog pool =
  if length pool == i
  then return pool
  else do 
    let transformation = getMutation (head mutations) prog
        progs' = trans transformation prog
        newseed = if length progs' > 1
                  then prog
                  else head progs' 
    mutationGenLoop i (tail mutations) newseed (unionBy (==) pool progs') -- (progs' : pool) -- 


randomName r = do
  old <- getStdGen
  let (result, newS) = runState (getRandName r) old
  setStdGen newS
  return result


randomPick range = do
  old <- getStdGen
  let (result, newS) = runState (getRandInRange range) old
  setStdGen newS
  return result 


ranPool :: [String] -> [(String, Int)] -> IO [(String, Int)]
ranPool list pool = 
  if length pool >= 100
  then return pool
  else do 
    p <- randomPick (length list - 1)
    let picked = list !! p 
    ranPool list $ pool ++ [(picked, p)]



type RandStat a = State StdGen a

getRandInRange :: Int -> RandStat Int
getRandInRange range = do
  gen <- get
  let (val, gen') = randomR (0, range) gen in do
    put gen'
    return val

-- TODO not finished! 
getRandName :: Int -> RandStat String
getRandName r = do
  gen <- get
  return $ take r (randomRs ('a', 'z') gen)

getRandom :: Random a => RandStat a
getRandom = do
  gen <- get
  let (val, gen') = random gen in do  
    put gen'
    return val


getTwoRandoms :: Random a => RandStat (a, a)
getTwoRandoms = liftM2 (,) getRandom getRandom

runTwoRandoms :: IO (Int, Int)
runTwoRandoms = do
  oldState <- getStdGen 
  let (result, newState) = runState getTwoRandoms oldState
  setStdGen newState
  return result


getMutation :: (String, Int) -> Program -> Trans
getMutation ("S1", i) (Program prog com) = s1 (from, to)
  where from = i `mod` (length prog)
        to = (from + i + 1) `mod` (length prog)
getMutation ("S5", i) (Program prog com) = s5 
getMutation ("S6", i) (Program prog com) = s6 split 
  where split = i `mod` (length prog)
getMutation ("S7", i) (Program prog com) = s7 (from, to)
  where from = i `mod` (length prog)
        to = (from + i) `mod` (length prog)



