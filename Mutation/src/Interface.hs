{-# LANGUAGE DeriveGeneric #-}

module Interface where
import Data.Aeson 
import GHC.Generics
import qualified Data.ByteString.Lazy as B

data Config = Config {
    sourceBoogie :: String -- single Boogie source
  , mutationRatio :: [(String, Int)]
  , mutationLevels :: Int
  , numberOfMutants :: Int -- # of mutants per level
  , mutationAttempts :: Int -- # of attempts
  , outputToFile  :: Bool
  , verbose       :: Bool
  , prefix        :: String
  } deriving (Generic, Show)

instance ToJSON Config where
   toEncoding = genericToEncoding defaultOptions

instance FromJSON Config 


blankConfig = Config "" defaultMuOps 1000 100 1000 True True ""

defaultMuOps = [
  ("S1",0),
  ("S5",0),
  ("S6",0),
  ("S7",0),
  ("G2",0),
  ("G10",0),
  ("L1",0),
  ("L2",0),
  ("L4",0),
  ("L5",0),
  ("L6",0),
  ("L8",1)
  ]

createBlankConfig = B.writeFile "./config.json" $ encode blankConfig
