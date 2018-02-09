{-# LANGUAGE OverloadedStrings #-}
{-| 
Module      : Renaming
Description : handles all renaming operators 
-}

module Renaming where

import Boogie.AST
import Boogie.TypeChecker
import Boogie.Position
import Transformations 
import Data.List
import Control.Lens
import Data.Maybe

-- `renameID` updates ID everywhere, accross all 7 decl types 
-- renameID :: Program -> (String, String) -> Program
-- renameID p@(Program decls com) (oldId, newId) = undefined 

replaceIDExpr e s = fmap (flip replaceIDExpr' s) e 

replaceIDExpr' :: BareExpression -> (String -> String) -> BareExpression
replaceIDExpr' (TypedVar id t) schema = TypedVar (schema id) t
replaceIDExpr' (Application id args) schema = Application (schema id) args
replaceIDExpr' (MapSelection m indcies) schema = MapSelection (replaceIDExpr m schema)
  (map (flip replaceIDExpr schema) indcies)
replaceIDExpr' (MapUpdate m indcies rhs) schema = MapUpdate (replaceIDExpr m schema)
  (map (flip replaceIDExpr schema) indcies) (replaceIDExpr rhs schema)
replaceIDExpr' (Old e) schema = Old (replaceIDExpr e schema)
replaceIDExpr' (IfExpr cond eThen eElse) schema = IfExpr (replaceIDExpr cond schema) (replaceIDExpr eThen schema) (replaceIDExpr eElse schema)
replaceIDExpr' e schema = e -- TODO implement all Exprs 


produceSchema :: (String, String) -> (String -> String)
produceSchema (from, to) = (\s -> if s == from then to else s)




programReplaceIds :: (String, String) -> Program -> Program
programReplaceIds (from, to) p@(Program decls com) = Program decls' com
  where decls' = (
          (gVarReplace (from, to) p) .
          (gconstReplace (from, to) p) .
          (f (from, to) p) 
          ) decls 


type Renaming = (String, String) -> Program -> [Decl] -> [Decl]

gVarReplace :: Renaming
gVarReplace (from, to) p decls = map (fmap $ over _VarDecl (\idtws -> map trans idtws)) decls
  where trans = (\idtw -> idtw { itwId = produceSchema (from, to) (itwId idtw) } )

gconstReplace :: Renaming
gconstReplace = gVarReplace


f :: Renaming
f (from, to) p decls = map (fmap $ over _ProcedureDecl trans) decls
  where trans = procNames . formals
        procNames = (_1 %~ (id))
        formals  = (_3 %~ (map (\idtw -> idtw { itwId = produceSchema (from, to) (itwId idtw) } )))

renameGVar :: Program -> (String, String) -> Program
renameGVar p@(Program decls com) (oldId, newId)
  -- base cases: not possible to transform
  | null idtws = p 
  | oldId == newId = p
  | newId `elem` (allGlobalIDs p) = p
  | not $ oldId `elem` ids = p
  -- actual update
  | otherwise = Program decls' com
  where idtws = concat $ catMaybes $ map (preview _VarDecl . node) decls
        ids = map itwId idtws 
        decls' = map (maintainPos $ over _VarDecl (map $ renameIdtws (oldId, newId))) decls


-- | remove me!!! 
transfromProcedure :: (Id, Id) -> Program -> Program
transfromProcedure (from, to) (Program decls com) = (Program decls' com)
  where decls' = map (maintainPos $ over _ProcedureDecl procedureT) decls
        procedureT (name, targs, formals, rets, contract, (Just (locals, stmts))) =
          (name, targs, formals, rets, contract, (Just (locals, (renameLabel (from, to) stmts))))


renameLabel :: (Id, Id) -> Block -> Block
renameLabel (from, to) block = [ (Pos p (rename bareLStmt)) | (Pos p bareLStmt) <- block]
  where rename (labels, (Pos p bstmt)) = (labels', (Pos p (renameLabelS (from, to) bstmt)))
          where labels' = map (renameID (from, to)) labels

renameLabelS :: (Id, Id) -> BareStatement -> BareStatement
renameLabelS (from, to) stmt = (over _Goto gotoRenameLabel) stmt
  where gotoRenameLabel labels = map (renameID (from, to)) labels


renameLVar :: Body -> (String, String) -> Body
renameLVar b@(locals, block) (oldId, newId)
  | otherwise = b -- TODO

replaceHavocID :: (String, String) -> [BareStatement]  -> [BareStatement]
replaceHavocID (from, to) stmts = map (over _Havoc havocReplace) stmts
  where havocReplace = map $ renameID (from, to)

replaceAssignID :: (String, String) -> [BareStatement]  -> [BareStatement]
replaceAssignID (from, to) stmts = map (over _Assign assignReplace) stmts
  where havocReplace = map $ renameID (from, to)
        assignReplace = undefined


{- expression level -}
renameExpression ::  (String, String) -> Expression -> Expression
renameExpression (from, to) (Pos p bexpr) = Pos p $ renameBareExpression (from, to) bexpr

-- | TODO not complete 
renameBareExpression :: (String, String) -> BareExpression -> BareExpression
renameBareExpression (from, to) expr = (over _BinaryExpression binaryExprUpdate .
                                        over _UnaryExpression unaryExprUpdate .
                                        over _Old oldReplace . 
                                        over _MapUpdate mapUpdateReplace . 
                                        over _MapSelection mapSelectReplace . 
                                        over _Application applicationReplace . 
                                        over _Var varReplace . 
                                        over _Literal literalReplace) expr
  where renameExpression' = renameExpression (from, to) 
        literalReplace = id
        varReplace id = renameID (from, to) id
        applicationReplace (fid, args) = ((renameID (from, to) fid),
                                          (map renameExpression' args))
        mapSelectReplace (mapId, indices) = (renameExpression' mapId,
                                             (map renameExpression' indices))
        mapUpdateReplace (mapId, indices, rhs) = (renameExpression' mapId,
                                                  (map renameExpression' indices), 
                                                  (renameExpression' rhs))
                                                   
        oldReplace expr = renameExpression' expr
        iteReplace (ifE, thenE, elseE) = (renameExpression' ifE,
                                          renameExpression' thenE,
                                          renameExpression' elseE)
        unaryExprUpdate (unop, expr) = (unop, renameExpression' expr)
        binaryExprUpdate (binop, exprL, exprR) = (binop,
                                                  renameExpression' exprL,
                                                  renameExpression' exprR)        



renameID :: (Id, Id) -> Id -> Id
renameID (from, to) id
  | id /= from = id
  | id == from = to

renameIdtws :: (String, String) -> IdTypeWhere -> IdTypeWhere
renameIdtws (from, to) idtw = IdTypeWhere (renameID (from, to) (itwId idtw)) (itwType idtw) (itwWhere idtw)
-- | from /= (itwId idtw) = idtw
-- | otherwise = IdTypeWhere to (itwType idtw) (itwWhere idtw)

