-- | Splitting a Boogie program into multiple verification paths.
-- This module is intentionally placed under src/Boogie, for it
-- shouldn't tied to FOOL at this point
module Boogie.Paths where

import Boogie.AST
import Boogie.Position
import Boogie.TypeChecker
import Boogie.Util
import Control.Monad.State 
import qualified Data.Map as M 
import Data.Maybe (maybeToList) 


data Proc = Proc {
  pid :: Id,
  -- one procedure can have multiple implementations;
  -- each implementation can have their own local var decls 
  implementations :: [Body], -- body = ([[idtw]], block)
  modifies :: [Id],
  requires :: [Contract],
  ensures :: [Contract]
  }

data Env = Env {
  ctx :: Context, 
  procs :: M.Map Id Proc,
  -- Mathmatical part of Declarations; shared by all proof paths   
  globalDecls :: [Decl]
  }

addGlobal decl s = s { globalDecls = globalDecls s ++ [decl] } 

addProc pid p s = s { procs = M.insert pid p (procs s) } 

type P a = State Env a

emptyEnv ctx = Env ctx M.empty []

buildProcs :: Program -> Context -> Env 
buildProcs p ctx = snd $ runState (build p) (emptyEnv ctx)
  where build (Program decls _) = do 
          mapM_ buildGlobals decls
          procs <- gets procs
          return ()

buildGlobals :: Decl -> P ()
buildGlobals decl = case node decl of
  TypeDecl _ -> modify $ addGlobal decl
  ConstantDecl _ _ _ _ _ -> modify $ addGlobal decl
  FunctionDecl _ _ _ _ _ _ -> modify $ addGlobal decl
  AxiomDecl _ -> modify $ addGlobal decl
  VarDecl _ -> modify $ addGlobal decl
  ProcedureDecl pid typArgs formals rets contracts body -> do
    modify $ addProc pid p
      where p = Proc pid implementations modifies requires ensures
            implementations = maybeToList body 
            modifies = concat [ ids | Modifies free ids <- contracts]
            requires = [ r | r@(Requires _ _) <- contracts]
            ensures = [ e | e@(Ensures _ _) <- contracts]
  ImplementationDecl pid typArgs formals rets body -> do
    procs <- gets procs 
    case M.lookup pid procs of
      Nothing -> error $ "Implementation comes before declaration of procedure: " ++ pid 
      Just p  -> modify $ addProc pid p'
        where p' = p { implementations = implementations p ++ body }
    return ()
   
---- 
appendLocals :: Body -> [(Block, Contract)] -> [(Body, Contract)]
appendLocals (idtws, _) pairs = map (\(block, c) -> ((idtws, block), c)) pairs 

split :: Context -> Id -> Block -> Woogie 
split ctx pid block = foldr f (W [] []) block
  where f lst w = case (node . snd . node) lst of
          Predicate attrs spec -> w { base = (base w) ++ [lst] }
          Havoc ids -> w { base = (base w) ++ [lst] }
          Assign _ _ -> w { base = (base w) ++ [lst] }
          Return -> w { proofObs = (proofObs w) ++ [(base w, contract)] }
            where contract = case M.lookup pid (ctxProcedures ctx) of
                    Nothing -> error $ pid ++ " signature not found in context"
                    Just psig -> psigContracts psig 
          Call lhss p' args -> w { base = (base w) ++ [lst], proofObs = (proofObs w) ++ precall}
            where precall = [((base w), precondCall)]
                  precondCall = case M.lookup p' (ctxProcedures ctx) of
                    Nothing -> error $ "failed to find signature of " ++ p'
                    Just psig -> [cond | cond@(Requires _ _ ) <- (psigContracts psig)]
          While _c spec b -> w { base = (base w) ++ [lst], proofObs = (proofObs w) ++ pre ++ whilebody }
            where pre = []
                  whilebody = []
          _ -> error $ "Unsupported statement during path split" 

data Woogie = W {
    base :: Block
  , proofObs :: [(Block, [Contract])]          
  }

woogieConcat w1 w2 = W (base w1 ++ base w2) (proofObs w1 ++ proofObs w2)


          -- If c tb Nothing -> split ctx pid tb -- if will disappear!
          -- If c tb (Just eb) -> thenWoogie `woogieConcat` elseWoogie
          --   where thenWoogie = split ctx pid tb
          --         elseWoogie = split ctx pid eb 
