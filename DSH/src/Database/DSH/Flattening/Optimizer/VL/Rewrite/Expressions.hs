{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import Debug.Trace

import Control.Monad

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Optimizer.Common.Match
import Optimizer.Common.Traversal
  
import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common
  
optExpressions :: VLRewrite Bool
optExpressions = iteratively $ postOrder inferBottomUp expressionRules

expressionRules :: VLRuleSet BottomUpProps
expressionRules = [ mergeCompWithProjectLeft
                  , mergeCompWithProjectRight
                  , mergeCompExpr1WithProject
                  , constInputLeft
                  , constInputRight 
                  , sameInput
                  , mergeExpr11 
                  , mergeExpr12 
                  , mergeExpr21Right ]

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
    Nothing -> error $ "CompExpr2(L) expression does not reference its left input" ++ (show e)

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
    Nothing -> error $ "CompExpr2(L) expression does not reference its right input" ++ (show e)
   
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
                                       
sameInput :: VLRule BottomUpProps
sameInput q =
  $(pattern [| q |] "(q1) CompExpr2L expr (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        return $ do
          logRewrite "Expr.SameInput" q
          replace q $ UnOp (CompExpr1 (expr2ToExpr1 $(v "expr"))) $(v "q1") |])
  
-- Merge CompExpr operators with input projections in various combinations
    
mergeCompWithProjectLeft :: VLRule BottomUpProps
mergeCompWithProjectLeft q =
  $(pattern [| q |] "(ProjectL ps (q1)) CompExpr2L expr (q2)"
    [| do
        return $ do
          logRewrite "Expr.Merge.Project.Left" q
          let c1 = leftCol $(v "expr")
              c1' = $(v "ps") !! (c1 - 1)
              expr' = updateLeftCol (Column2Left (L c1')) $(v "expr")
          replace q $ BinOp (CompExpr2L expr') $(v "q1") $(v "q2") |])

mergeCompWithProjectRight :: VLRule BottomUpProps
mergeCompWithProjectRight q =
  $(pattern [| q |] "(q1) CompExpr2L expr (ProjectL ps (q2))"
    [| do
        return $ do
          logRewrite "Expr.Merge.Project.Right" q
          let c2 = rightCol $(v "expr")
              c2' = $(v "ps") !! (c2 - 1)
              expr' = updateRightCol (Column2Right (R c2')) $(v "expr")
          replace q $ BinOp (CompExpr2L expr') $(v "q1") $(v "q2") |])

mergeCompExpr1WithProject :: VLRule BottomUpProps
mergeCompExpr1WithProject q =
  $(pattern [| q |] "CompExpr1 expr (ProjectL ps (q1))"
    [| do
        return $ do
          logRewrite "Expr.Merge.Project" q
          let c = col $(v "expr")
              c' = $(v "ps") !! (c - 1)
              expr' = updateCol (Column1 c') $(v "expr")
          replace q $ UnOp (CompExpr1 expr') $(v "q1")|])
  
-- Remove the left input from a CompExpr operator if the input is constant
constInputLeft :: VLRule BottomUpProps
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
          logRewrite "Expr.Const.Left" q
          let expr' = expr2ToExpr1 $ updateLeftCol (Constant2 constVal) $(v "expr")
          replace q $ UnOp (CompExpr1 expr') $(v "q2") |])
                     
-- Remove the right input from a CompExpr operator if the input is constant
constInputRight :: VLRule BottomUpProps
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
          logRewrite "Expr.Const.Right" q
          let expr' = expr2ToExpr1 $ updateRightCol (Constant2 constVal) $(v "expr")
          replace q $ UnOp (CompExpr1 expr') $(v "q1") |])
  
                     
-- Merge multiple stacked CompExpr operators if they have the same input.
  
-- FIXME this is way too hackish. Implement a clean solution to insert expressions into
-- other expressions
expr1ToExpr2Right :: Expr1 -> Expr2
expr1ToExpr2Right (App1 o e1 e2) = App2 o (expr1ToExpr2Right e1) (expr1ToExpr2Right e2)
expr1ToExpr2Right (Column1 c)    = Column2Right (R c)
expr1ToExpr2Right (Constant1 v)  = Constant2 v

expr1ToExpr2Left :: Expr1 -> Expr2
expr1ToExpr2Left (App1 o e1 e2) = App2 o (expr1ToExpr2Left e1) (expr1ToExpr2Left e2)
expr1ToExpr2Left (Column1 c)    = Column2Left (L c)
expr1ToExpr2Left (Constant1 v)  = Constant2 v

mergeExpr11 :: VLRule BottomUpProps
mergeExpr11 q =
  $(pattern [| q |] "(CompExpr1 e1 (q1)) CompExpr2L e (CompExpr1 e2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
       
        return $ do
          logRewrite "Expr.Merge.11" q
          let e' = updateRightCol (expr1ToExpr2Right $(v "e2")) $(v "e")
       
          let e'' = expr2ToExpr1 $ updateLeftCol (expr1ToExpr2Right $(v "e1")) e'
          replace q $ UnOp (CompExpr1 e'') $(v "q1") |])
  
mergeExpr12 :: VLRule BottomUpProps  
mergeExpr12 q =
  $(pattern [| q |] "CompExpr1 e1 ((q1) CompExpr2L e2 (q2))"
    [| do
        return $ do
          logRewrite "Expr.Merge.12" q
          let e1' = expr1ToExpr2Right $(v "e1")
              e' = updateRightCol $(v "e2") e1'
              op = BinOp (CompExpr2L e') $(v "q1") $(v "q2")
          replace q op |])
           
mergeExpr21Right :: VLRule BottomUpProps
mergeExpr21Right q =
  $(pattern [| q |] "(q1) CompExpr2L e2 (CompExpr1 e1 (q2))"
    [| do
        return $ do
          logRewrite "Expr.Merge.21.Right" q
          let e2' = updateRightCol (expr1ToExpr2Right $(v "e1")) $(v "e2")
          replace q $ BinOp (CompExpr2L e2') $(v "q1") $(v "q2") |])
          
mergeExpr21Left :: VLRule BottomUpProps
mergeExpr21Left q =
  $(pattern [| q |] "(CompExpr1 e1 (q1)) CompExpr2L e2 (q2)"
    [| do
        return $ do
          logRewrite "Expr.Merge.21.Left" q
          let e2' = updateLeftCol (expr1ToExpr2Left $(v "e1")) $(v "e2")
          replace q $ BinOp (CompExpr2L e2') $(v "q1") $(v "q2") |])
          
