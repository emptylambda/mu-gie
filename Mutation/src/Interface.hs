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


-- blankConfig = Config "" defaultMutations (1) (1)

-- defaultMutations = [("S1", 1),
--                     ("S5", 1)
--                    ]

-- createBlankConfig = B.writeFile "./config.json" $ encode blankConfig
