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

parseAndTypecheck f = do 
  res <- parseFromFile BoogieParser.program f
  case res of
    Left parseErr -> print parseErr >> exitFailure
    Right prog -> case typeCheckProgram prog of
      Left typeCheckErr -> print (typeErrorsDoc typeCheckErr) >> exitFailure
      Right ctx -> prettyPrint prog

prettyPrint p = print $ pretty p 
