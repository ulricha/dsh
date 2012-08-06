{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import Debug.Trace

import Control.Monad

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common
  
optExpressions :: DagRewrite VL Bool
optExpressions = iteratively $ postOrder inferBottomUp expressionRules

expressionRules :: RuleSet VL BottomUpProps
expressionRules = [ mergeCompWithProjectLeft
                  , mergeCompWithProjectRight
                  , mergeCompExpr1WithProject
                  , constInputLeft
                  , constInputRight 
                  , sameInput
                  , mergeExpr11 ]

updateLeftCol :: Expr2 -> Expr2 -> Expr2
updateLeftCol c' (App2 o e1 e2)      = App2 o (updateLeftCol c' e1) (updateLeftCol c' e2)
updateLeftCol c' (Column2Left (L _)) = c'
updateLeftCol _  e                   = e

updateRightCol :: Expr2 -> Expr2 -> Expr2
updateRightCol c' (App2 o e1 e2)       = App2 o (updateRightCol c' e1) (updateRightCol c' e2)
updateRightCol c' (Column2Right (R c)) = c'
updateRightCol _  e                    = e
                                         
updateCol :: Expr1 -> Expr1 -> Expr1
updateCol c' (App1 o e1 e2) = App1 o (updateCol c' e1) (updateCol c' e2)
updateCol c' (Column1 c)    = c'
updateCol _  e              = e
                                         
leftCol :: Expr2 -> DBCol
leftCol e = 
  let leftCol' :: Expr2 -> Maybe DBCol
      leftCol' (App2 _ e1 e2) = 
        case leftCol' e1 of
          Just c  -> Just c
          Nothing -> leftCol' e2
      leftCol' (Column2Left (L c)) = Just c
      leftCol' _ = Nothing
  in 
   case leftCol' e of
    Just c -> c
    Nothing -> error "CompExpr2(L) expression does not reference its left input"

rightCol :: Expr2 -> DBCol
rightCol e = 
  let rightCol' (App2 _ e1 e2) = 
        case rightCol' e1 of
          Just c  -> Just c
          Nothing -> rightCol' e2
      rightCol' (Column2Right (R c)) = Just c
      rightCol' _ = Nothing
  in 
   case rightCol' e of
    Just c -> c
    Nothing -> error "CompExpr2(L) expression does not reference its right input"
   
col :: Expr1 -> DBCol
col e = 
  let col' (App1 _ e1 e2) = 
        case col' e1 of
          Just c  -> Just c
          Nothing -> col' e2
      col' (Column1 c) = Just c
      col' _ = Nothing
  in 
   case col' e of
    Just c -> c
    Nothing -> error "CompExpr1 expression does not reference its right input"
   
expr2ToExpr1 :: Expr2 -> Expr1
expr2ToExpr1 (App2 o e1 e2)          = App1 o (expr2ToExpr1 e1) (expr2ToExpr1 e2)
expr2ToExpr1 (Column2Left (L c))     = Column1 c
expr2ToExpr1 (Column2Right (R c))    = Column1 c
expr2ToExpr1 (Constant2 v)           = Constant1 v
                                       
-- Rewrite rules
                                       
sameInput :: Rule VL BottomUpProps
sameInput q =
  $(pattern [| q |] "(q1) CompExpr2L expr (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        return $ do
          logRewriteM "Expr.SameInput" q
          replaceM q $ UnOp (CompExpr1 (expr2ToExpr1 $(v "expr"))) $(v "q1") |])
  
-- Merge CompExpr operators with input projections in various combinations
    
mergeCompWithProjectLeft :: Rule VL BottomUpProps
mergeCompWithProjectLeft q =
  $(pattern [| q |] "(ProjectL ps (q1)) CompExpr2L expr (q2)"
    [| do
        return $ do
          logRewriteM "Expr.Merge.Project.Left" q
          let c1 = leftCol $(v "expr")
              c1' = $(v "ps") !! (c1 - 1)
              expr' = updateLeftCol (Column2Left (L c1')) $(v "expr")
          replaceM q $ BinOp (CompExpr2L expr') $(v "q1") $(v "q2") |])

mergeCompWithProjectRight :: Rule VL BottomUpProps
mergeCompWithProjectRight q =
  $(pattern [| q |] "(q1) CompExpr2L expr (ProjectL ps (q2))"
    [| do
        return $ do
          logRewriteM "Expr.Merge.Project.Right" q
          let c2 = rightCol $(v "expr")
              c2' = $(v "ps") !! (c2 - 1)
              expr' = updateRightCol (Column2Right (R c2')) $(v "expr")
          replaceM q $ BinOp (CompExpr2L expr') $(v "q1") $(v "q2") |])

mergeCompExpr1WithProject :: Rule VL BottomUpProps
mergeCompExpr1WithProject q =
  $(pattern [| q |] "CompExpr1 expr (ProjectL ps (q1))"
    [| do
        return $ do
          logRewriteM "Expr.Merge.Project" q
          let c = col $(v "expr")
              c' = $(v "ps") !! (c - 1)
              expr' = updateCol (Column1 c') $(v "expr")
          replaceM q $ UnOp (CompExpr1 expr') $(v "q1")|])
  
-- Remove the left input from a CompExpr operator if the input is constant
constInputLeft :: Rule VL BottomUpProps
constInputLeft q =
  $(pattern [| q |] "(q1) CompExpr2L expr (q2)"
    [| do
        constCols <- liftM constProp $ properties $(v "q1")
        let c = leftCol $(v "expr")
        constVal <- case constCols of
                      VProp (DBVConst _ plc) -> 
                        case plc !! (c - 1) of
                          ConstPL v -> return v
                          NonConstPL -> fail "no match"
                      _ -> fail "no match"
        return $ do
          logRewriteM "Expr.Const.Left" q
          let expr' = expr2ToExpr1 $ updateLeftCol (Constant2 constVal) $(v "expr")
          replaceM q $ UnOp (CompExpr1 expr') $(v "q2") |])
                     
-- Remove the right input from a CompExpr operator if the input is constant
constInputRight :: Rule VL BottomUpProps
constInputRight q =
  $(pattern [| q |] "(q1) CompExpr2L expr (q2)"
    [| do
        const <- liftM constProp $ properties $(v "q2")
        let c = rightCol $(v "expr")
        constVal <- case const of
                      VProp (DBVConst _ constPayload) -> 
                        case constPayload !! (c - 1) of
                          ConstPL v -> return v
                          NonConstPL -> fail "no match"
                      _ -> fail "no match"
        return $ do
          logRewriteM "Expr.Const.Right" q
          let expr' = expr2ToExpr1 $ updateRightCol (Constant2 constVal) $(v "expr")
          replaceM q $ UnOp (CompExpr1 expr') $(v "q1") |])
  
                     
-- Merge multiple stacked CompExpr operators if they have the same input.
  
-- FIXME this is way too hackish. Implement a clean solution to insert expressions into
-- other expressions
expr1ToExpr2 :: Expr1 -> Expr2
expr1ToExpr2 (App1 o e1 e2) = App2 o (expr1ToExpr2 e1) (expr1ToExpr2 e2)
expr1ToExpr2 (Column1 c)    = Column2Right (R c)
expr1ToExpr2 (Constant1 v)  = Constant2 v

mergeExpr11 :: Rule VL BottomUpProps
mergeExpr11 q =
  $(pattern [| q |] "(CompExpr1 e1 (q1)) CompExpr2L e (CompExpr1 e2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
       
        return $ do
          logRewriteM "Expr.Merge.11" q
          let e' = updateRightCol (expr1ToExpr2 $(v "e2")) $(v "e")
       
          let e'' = expr2ToExpr1 $ updateLeftCol (expr1ToExpr2 $(v "e1")) e'
          replaceM q $ UnOp (CompExpr1 e'') $(v "q1") |])
           
