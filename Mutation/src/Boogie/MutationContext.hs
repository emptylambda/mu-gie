-- | construct the required context for mutations 

module Boogie.MutationContext where 

import Boogie.AST
import Boogie.Position
import Control.Monad.State
import Data.Map (Map, (!))
import qualified Data.Map as M


buildMuContext :: Program -> MuContext
buildMuContext prog = snd $ runState (readProgram prog) emptyC

data MuContext = MuContext
  {
    gVars :: Map Id Type,
    gAxioms :: [Expression],
    gFuncs :: [Decl], 
    localVars :: Map Id (Map Id Type)  -- localVar maps indexed by procedureName
    
  }

emptyC :: MuContext
emptyC = MuContext
  {
    gVars = M.empty,
    gAxioms = [],
    gFuncs = [],
    localVars = M.empty
  }

type Mutating a =  State MuContext a

readProgram :: Program -> Mutating ()
readProgram (Program decls _) = do
  mapM_ getGlobals decls 


getGlobals :: Decl -> Mutating ()
getGlobals (Pos pos bareD) = do
  case bareD of
    ConstantDecl _ ids tp _ _ -> mapM_ (insertNewGVar tp) ids
    AxiomDecl e -> modify $ \mc -> mc { gAxioms = (gAxioms mc) ++ [e] }
    otherwise -> return () 
  
insertNewGVar :: Type -> Id -> Mutating ()
insertNewGVar t id = do
  gvars <- gets gVars
  modify $ \mc -> mc { gVars = M.insert id t gvars }

