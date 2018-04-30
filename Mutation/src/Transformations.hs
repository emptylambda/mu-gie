{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
{-| 
Module      : μgie Transformations
Description : collection of transformations, no randomness 
  

-}

module Transformations where
import Boogie.AST
import Boogie.TypeChecker
import Boogie.Position
import Data.List
import Control.Lens
import Control.Lens.Tuple
import Control.Applicative
import Data.Maybe
import Pretty 
import Renaming

data Trans = Trans {
  transName :: String,
  trans     :: Program -> [Program]
  } 

instance Pretty Trans where
  pretty t = text $ show t

instance Show Trans where
  show = transName

{- global ones -}
s1 (from, to) = Trans "S1" (\p -> [swapDecl p (from, to)])
-- s2 -- renaming occurances of ids 
-- s3 -- renaming occurances of types
s5 = Trans "S5" (\p -> [decoupleProcedures p])
s6 i = Trans "S6" (\p -> let (a, b) = (splitProgram i p) in [a, b])
s7 (wa, wp) = Trans "S7" (\p -> [addAxiomToPrecond p (wa, wp)])
g1  i = Trans "G1"  (\p -> [addTruth p i])
g2 i = Trans "G2" (\p -> [removeTriggers p i])

{- local ones -}
l1 whichB (from, to) = Trans "L1" (\p -> [whichBody p whichB swapLocalVar'])
  where swapLocalVar' b = swapLocalVar b (from, to)
l2 whichB = Trans "L2" (\p -> [whichBody p whichB multiLocalDecl])
l4 i = Trans "L4" (\p -> [andPreconds p i])
l5 i = Trans "L5" (\p -> [andPostconds p i])
l6 (from, to) = Trans "L6" (\p -> [swapContracts p (from, to)])
l8 i = Trans "L8" (\p -> [whichBody p i (flip flipIfinBody i)])








{- S1 -}
-- | swapDecl swap declartions
-- index starting from 0
-- leave the program untouched in case of out of bound indices
swapDecl :: Program -> (Int, Int) -> Program
swapDecl p@(Program decls com) (from, to)
  -- | from < 0 || to < 0 = p
  -- | from > length decls || to > length decls = p
  | otherwise = Program decls' com
  where decls' = swapElementsAt (from `mod` (length decls)) (to `mod` (length decls)) decls
{- S1 -}

{- S5 -}
decoupleProcedures :: Program -> Program
decoupleProcedures p@(Program decls com)
  | null proceduresWithBody = p -- Nothing to decouple 
  | otherwise = Program decls' com
  where proceduresWithBody = catMaybes $ filter hasBody $ map (preview _ProcedureDecl . node) decls
        imps = map (createImp . dropContract . getHeader) proceduresWithBody
        decls' = (map (fmap $ over _ProcedureDecl dropBody) decls) ++ imps
        dropBody = (_6 .~ Nothing)

getHeader :: (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) ->
             (Id, [Id], [IdType],      [IdType],      [Contract],  Body)
getHeader t@(pid, targs, formals, rets, contracts, (Just body)) =
  t & (_3 %~ (\idtws -> map noWhere idtws))
    & (_4 %~ (\idtws -> map noWhere idtws))
    & (_6 %~ fromJust)
getHeader _ = error "[Transformations]: getHeader with Nothing body"

dropContract :: (Id, [Id], [IdType], [IdType], [Contract],  Body) ->
                (Id, [Id], [IdType], [IdType], Body)
dropContract (a, b, c, d, _, f) = (a, b, c, d, f)

createImp :: (Id, [Id], [IdType], [IdType], Body) -> Decl
createImp (a, b, c, d, f) = gen $ ImplementationDecl a b c d [f]
{- S5 -}

{- S6 -}
splitProgram :: Int -> Program -> (Program, Program)
splitProgram i p@(Program decls com) = (Program front com, Program back com)
  where (front, back) = splitAt i decls

isolatedDecl :: Program -> Int -> (Program, Program)
isolatedDecl p@(Program decls com) i
  | i >= length decls = (p, p) -- TODO Better way of handling this 
  | otherwise = (Program decls' com, Program [decls !! i] com)
  where decls' = take i decls ++ drop (i+1) decls
{- S6 -}

{- S7 [Incomplete] -}
-- [Incomplete] as `whichAxiom` and `whichProcedure` are not currently in use 
addAxiomToPrecond :: Program -> (Int, Int) -> Program
addAxiomToPrecond p@(Program decls com) (whichAxiom, whichProcedure) 
  | null axioms = p
  | null procedures = p
  | otherwise = Program decls' com 
  where axioms = catMaybes $ map (preview _AxiomDecl . node) decls
        procedures = catMaybes $ map (preview _ProcedureDecl . node) decls
        decls' = (map (fmap $ over _ProcedureDecl (addAxiom axiom)) decls)
        axiom = axioms !! (whichAxiom `mod` (length axioms))

addAxiom :: Expression ->
  (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) ->
  (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) 
addAxiom  a t = t & (_5 %~ (\contracts -> contracts ++ [Requires False a]))

addAxioms :: [Expression] ->
  (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) ->
  (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) 
addAxioms [] t = t
addAxioms as t = t & (_5 %~ (\contracts -> contracts ++ [Requires False (head as)]))

--   where a' = head as -- !! (n `mod` length(as)) -- prefixAxiom a


{- S7 -}

{- G2 [Incomplete] -}
-- [Incomplete] as `whichAxiom` and `whichProcedure` are not currently in use 
addTruth :: Program -> Int -> Program
addTruth p@(Program decls com) whichProc
  | null procedures = p 
  | otherwise = Program decls' com 
  where procedures = allProcs p 
        decls' = (map (fmap $ over _ProcedureDecl (addAxioms truth)) decls)
        truth = [gen tt]
{- G2 -}        
{- G10 [Incomplete] -}
removeTriggers :: Program -> Int -> Program
removeTriggers p@(Program decls com) n = Program decls' com 
  where decls' = over (ix n) (fmap $ (over _AxiomDecl (fmap reTriggers))) decls
--   where decls' = map (fmap (over (_AxiomDecl) (fmap reTriggers))) decls

removeNthTrigger :: Int -> [Expression] -> [Expression]
removeNthTrigger n [] = []
removeNthTrigger 0 (e1:es) = (fmap reTriggers e1):es
removeNthTrigger n (e1:es) = e1 : (removeNthTrigger (n-1) es)

_withTrigger :: Prism' BareExpression BareExpression
_withTrigger = prism id $ \ e ->
  case e of
    Quantified [] qop typVars boundVars exp -> Left e
    Quantified ts qop typVars boundVars exp -> Right e    
    _ -> Left e

reTriggers :: BareExpression -> BareExpression
reTriggers = over _Quantified (\t -> t & (_1 %~ (\_ -> [])))
{- G10 -}

whAxiom :: Program -> Int -> (Expression -> Expression) -> Program 
whAxiom p@(Program decls com) n expTrans = Program decls' com
  where axoimsWithTrigger = map (preview _AxiomDecl . node) decls
        decls' = decls

{- Local Transformations : working on Body -}
whichBody :: Program -> Int -> (Body -> Body) -> Program 
whichBody p@(Program decls com) n bodyTrans = Program decls' com 
  where proceduresWithBody = catMaybes $ filter hasBody $ map (preview _ProcedureDecl . node) decls
        decls' = (map (fmap $ over _ProcedureDecl applyTrans) decls)
        applyTrans = (_6 %~ (\b -> case b of
                              Nothing -> Nothing -- TODO this would not cause any update! 
                              Just b -> Just $ bodyTrans b))


{- L1 -}
swapLocalVar :: Body -> (Int, Int) -> Body
swapLocalVar (locals, block) (from, to)
  | otherwise = (swapElementsAt from' to' locals, block)
  where from' = from `mod` (length locals)
        to'   = to `mod` (length locals)
{- L1 -}


{- L2 -}
multiLocalDecl :: Body -> Body
multiLocalDecl (locals, body) = ((groupBy (\_ -> \_ -> False) $ concat locals), body)
{- L2 -}

{- Contracts  -}
{- L4 -}
andPreconds :: Program -> Int -> Program
andPreconds p@(Program decls com) n = Program decls' com
  where decls' = (map (fmap $ over _ProcedureDecl andRequires) decls)
        andRequires = (_5 %~ andPres')

andPres' :: [Contract] -> [Contract]
andPres' contracts =  [conjunction] ++ others
  where (pres, others) = partition (\c -> case c of
                                       Requires False _ -> True
                                       othewise -> False) contracts
        conjunction = foldr (\(Requires _ a) -> \(Requires _ b) ->
                                Requires False (gen (BinaryExpression And a b ))) (Requires False (gen tt)) pres
{- L5 -}
andPostconds :: Program -> Int -> Program
andPostconds p@(Program decls com) n = Program decls' com
  where decls' = (map (fmap $ over _ProcedureDecl andEnsures) decls)
        andEnsures = (_5 %~ andPost')

andPost' :: [Contract] -> [Contract]
andPost' contracts =  [conjunction] ++ others
  where (pres, others) = partition (\c -> case c of
                                       Ensures False _ -> True
                                       othewise -> False) contracts
        conjunction = foldr (\(Ensures _ a) -> \(Ensures _ b) ->
                                Ensures False (gen (BinaryExpression And a b ))) (Ensures False (gen tt)) pres

{- L6 -}
swapContracts :: Program -> (Int, Int) -> Program
swapContracts p@(Program decls com) (from, to)
  | otherwise = Program decls' com
  where decls' = (map (fmap $ over _ProcedureDecl swapCons) decls)
        swapCons = (_5 %~ (\contracts ->
                             swapElementsAt (from `mod` (length contracts)) (to `mod` (length contracts)) contracts))


{- L7 -}
joinModifies :: Program -> Int -> Program
joinModifies p@(Program decls com) whichP = Program decls' com 
  where decls' = (map (fmap $ over _ProcedureDecl joinMods) decls)
        joinMods = (_5 %~ joinMods')
        
joinMods' :: [Contract] -> [Contract]
joinMods' contracts = [ms] ++ others
  where (mods, others) = partition (\c -> case c of
                                       Modifies False _ -> True
                                       othewise -> False) contracts
        ms = foldr (\(Modifies _ a) -> \(Modifies _ b) ->
                                Modifies False ((a ++ b ))) (Modifies False ([])) mods
-- TODO 
splitMods :: Program -> (Int, Int) -> Program
splitMods p@(Program decls com) whichP = Program decls' com
  where decls' = decls




{- flip if -}
flipIfExp :: BareExpression -> BareExpression
flipIfExp (IfExpr cond eThen eElse) = IfExpr (Pos p ((UnaryExpression Not) cond)) eElse eThen
  where p = position cond
flipIfExp e = e

flipIfStm :: BareStatement -> BareStatement
flipIfStm s@(If cond bThen Nothing) = s -- we cannot do flip here, then branch cannot be empty! 
flipIfStm (If cond bThen (Just bElse)) = case cond of
  Wildcard -> If cond bElse (Just bThen)
  Expr condE -> If (Expr condE') bElse (Just bThen)
    where condE' = Pos p (UnaryExpression Not condE)
          p = position condE
flipIfStm s = s 

flipIfinBody :: Body -> Int -> Body 
flipIfinBody (locals, block) n = (locals, block')
  where block' = map (fmap (\(ls, s) -> (ls, fmap flipIfStm s)) ) block

{- transformation on types -}
renameGenTyp :: Type -> (String, String) -> Type
renameGenTyp (MapType fvs domains range) (old, new) =
  MapType fvs (map (flip renameGenTyp (old, new)) domains) (flip renameGenTyp (old, new) range)
renameGenTyp t@(IdType id args) (old, new)
  | id == old = IdType new args
  | otherwise = t 




{- L2 -}
inlineLocalDecls :: Program -> Int -> Program
inlineLocalDecls p@(Program decls com) whichProc
  | null proceduresWithBody = p
  | otherwise = p
  where proceduresWithBody = catMaybes $ filter hasBody $ map (preview _ProcedureDecl . node) decls
{- L2 -}



{- misc -}
swapElementsAt :: Int -> Int -> [a] -> [a]
swapElementsAt a' b' [] = []
swapElementsAt a' b' list 
  | a' /= b' = front ++ targetB ++ list2 ++ targetA ++ back
  | otherwise = list 
    where   front = take a list
            targetA = [list !! a]
            targetB = [list !! b]
            list2 = drop (succ a) (take b list)
            back = drop (succ b) list
            (a, b) = sortPairInts (a', b')


sortPairInts :: (Int, Int) -> (Int, Int)
sortPairInts (a, b) | a >= b = (b, a)
                    | otherwise = (a, b)


hasBody :: Maybe (Id, [Id], [IdTypeWhere], [IdTypeWhere], [Contract], (Maybe Body)) -> Bool
hasBody Nothing = False 
hasBody (Just (_, _, _, _, _, Nothing))= False
hasBody (Just _) = True


zipUp :: [Maybe a] -> [a] -> [a]
zipUp maybes as = map f pairs
  where pairs = zip maybes as
        f (maybeA, originA) = case maybeA of
          Nothing -> originA
          Just a  -> a 

{- predicates over Expressions -}
hasConnjuction :: BareExpression -> Bool
hasConnjuction e@(BinaryExpression And _ _) = True
hasConnjuction _ = False 



{- MISC: fishing out things -}

allGlobalIDs :: Program -> [String]
allGlobalIDs p@(Program decls com) = constants ++ typs ++ functions ++ gvars ++ procs
  where constants = concatMap (view _2) (allGConstants p)
        typs = concatMap (map tId) (allTypes p)
        functions = map (view _2) (allFunctions p)
        gvars = concatMap (map itwId) (allGVars p)
        procs = map (view _1) (allProcs p)

-- workaround for `view` compatibility issue 
allGConstants p@(Program decls com) = catMaybes $ map (preview _ConstantDecl . node) decls 
allTypes      p@(Program decls com) = catMaybes $ map (preview _TypeDecl . node) decls 
allFunctions  p@(Program decls com) = catMaybes $ map (preview _FunctionDecl . node) decls 
allGVars      p@(Program decls com) = catMaybes $ map (preview _VarDecl . node) decls 
allProcs      p@(Program decls com) = catMaybes $ map (preview _ProcedureDecl . node) decls 
