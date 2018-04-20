{-
  Testing basic infrastructure for Boogie (Parsing / Typechecking ...)
-}
module BoogieTesting where

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

import Control.Lens
import Control.Lens.Tuple
import Control.Applicative


parseAndTypecheck f = do 
  res <- parseFromFile BoogieParser.program f
  case res of
    Left parseErr -> print parseErr >> exitFailure
    Right prog -> case typeCheckProgram prog of
      Left typeCheckErr -> print (typeErrorsDoc typeCheckErr) >> exitFailure
      Right ctx -> do
        -- prettyPrint prog
        return (prog, ctx)

prettyPrint p = print $ pretty p 
