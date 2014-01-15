{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import Control.Monad
import Control.Applicative

import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Rewrite.Common

optExpressions :: VLRewrite Bool
optExpressions = iteratively $ postOrder inferBottomUp expressionRules

expressionRules :: VLRuleSet BottomUpProps
expressionRules = [ constInputLeft
                  , constInputRight
                  , mergeExpr2SameInput
                  , mergeExpr12
                  , mergeExpr11
                  , mergeExpr21Right
                  , mergeExpr21Left 
                  , identityProject
                  ]

replaceLeftCol :: Expr2 -> Expr2 -> Expr2
replaceLeftCol col' e =
    case e of
        BinApp2 o e1 e2   -> BinApp2 o (replaceLeftCol col' e1) (replaceLeftCol col' e2)
        UnApp2 o e1       -> UnApp2 o (replaceLeftCol col' e1)
        Column2Left (L _) -> col'
        _                 -> e

replaceRightCol :: Expr2 -> Expr2 -> Expr2
replaceRightCol col' e =
    case e of
        BinApp2 o e1 e2    -> BinApp2 o (replaceRightCol col' e1) (replaceRightCol col' e2)
        UnApp2 o e1        -> UnApp2 o (replaceRightCol col' e1)
        Column2Right (R _) -> col'
        _                  -> e

replaceCol :: Expr1 -> Expr1 -> Expr1
replaceCol col' e =
    case e of
        BinApp1 o e1 e2 -> BinApp1 o (replaceCol col' e1) (replaceCol col' e2)
        UnApp1 o e1     -> UnApp1 o (replaceCol col' e1)
        Column1 _       -> col'
        _               -> e

leftCol :: Expr2 -> DBCol
leftCol e =
  let leftCol' :: Expr2 -> Maybe DBCol
      leftCol' (BinApp2 _ e1 e2) =
        case leftCol' e1 of
          Just c  -> Just c
          Nothing -> leftCol' e2
      leftCol' (UnApp2 _ e1) = leftCol' e1
      leftCol' (Column2Left (L c)) = Just c
      leftCol' _ = Nothing
  in
   case leftCol' e of
    Just c -> c
    Nothing -> error $ "CompExpr2(L) expression does not reference its left input" ++ (show e)

rightCol :: Expr2 -> DBCol
rightCol e =
  let rightCol' (BinApp2 _ e1 e2) =
        case rightCol' e1 of
          Just c  -> Just c
          Nothing -> rightCol' e2
      rightCol' (UnApp2 _ e1) = rightCol' e1
      rightCol' (Column2Right (R c)) = Just c
      rightCol' _ = Nothing
  in
   case rightCol' e of
    Just c -> c
    Nothing -> error $ "CompExpr2(L) expression does not reference its right input" ++ (show e)

col :: Expr1 -> DBCol
col e =
  let col' (BinApp1 _ e1 e2) =
          case col' e1 of
              Just c  -> Just c
              Nothing -> col' e2
      col' (UnApp1 _ e1) = col' e1
      col' (Column1 c) = Just c
      col' _ = Nothing
  in
   case col' e of
    Just c -> c
    Nothing -> error "CompExpr1L expression does not reference its right input"
    
expr2ToExpr1 :: Expr2 -> Expr1
expr2ToExpr1 (BinApp2 o e1 e2)    = BinApp1 o (expr2ToExpr1 e1) (expr2ToExpr1 e2)
expr2ToExpr1 (UnApp2 o e)         = UnApp1 o (expr2ToExpr1 e)
expr2ToExpr1 (Column2Left (L c))  = Column1 c
expr2ToExpr1 (Column2Right (R c)) = Column1 c
expr2ToExpr1 (Constant2 val)      = Constant1 val

-- Rewrite rules

-- Merge BinExpr operators with input projections in various combinations

-- Remove the left input from a CompExpr operator if the input is constant
constInputLeft :: VLRule BottomUpProps
constInputLeft q =
  $(pattern 'q "(q1) BinExpr expr (q2)"
    [| do
        constCols <- liftM constProp $ properties $(v "q1")
        let c = leftCol $(v "expr")
        constVal <- case constCols of
                      VProp (DBVConst _ plc) ->
                        case plc !! (c - 1) of
                          ConstPL val -> return val
                          NonConstPL  -> fail "no match"
                      _ -> fail "no match"
        return $ do
          logRewrite "Expr.Const.Left" q
          let expr' = expr2ToExpr1 $ replaceLeftCol (Constant2 constVal) $(v "expr")
          void $ replaceWithNew q $ UnOp (Project [expr']) $(v "q2") |])

-- Remove the right input from a CompExpr operator if the input is constant
constInputRight :: VLRule BottomUpProps
constInputRight q =
  $(pattern 'q "(q1) BinExpr expr (q2)"
    [| do
        constant <- liftM constProp $ properties $(v "q2")
        let c = rightCol $(v "expr")
        constVal <- case constant of
                      VProp (DBVConst _ constPayload) ->
                        case constPayload !! (c - 1) of
                          ConstPL val -> return val
                          NonConstPL  -> fail "no match"
                      _ -> fail "no match"
        return $ do
          logRewrite "Expr.Const.Right" q
          let expr' = expr2ToExpr1 $ replaceRightCol (Constant2 constVal) $(v "expr")
          void $ replaceWithNew q $ UnOp (Project [expr']) $(v "q1") |])


-- Merge multiple stacked CompExpr operators if they have the same input.

-- FIXME this is way too hackish. Implement a clean solution to insert expressions into
-- other expressions
expr1ToExpr2Right :: Expr1 -> Expr2
expr1ToExpr2Right e =
    case e of
        BinApp1 o e1 e2 -> BinApp2 o (expr1ToExpr2Right e1) (expr1ToExpr2Right e2)
        UnApp1 o e1     -> UnApp2 o (expr1ToExpr2Right e1)
        Column1 c       -> Column2Right (R c)
        Constant1 val   -> Constant2 val

expr1ToExpr2Left :: Expr1 -> Expr2
expr1ToExpr2Left e =
    case e of
        BinApp1 o e1 e2 -> BinApp2 o (expr1ToExpr2Left e1) (expr1ToExpr2Left e2)
        UnApp1 o e1     -> UnApp2 o (expr1ToExpr2Left e1)
        Column1 c       -> Column2Left (L c)
        Constant1 val   -> Constant2 val

mergeExpr2SameInput :: VLRule BottomUpProps
mergeExpr2SameInput q =
  $(pattern 'q "(q1) BinExpr e (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewrite "Expr.Merge.2.SameInput" q
          let e' = expr2ToExpr1 $(v "e")
          void $ replaceWithNew q $ UnOp (Project [e']) $(v "q1") |])
          
mergeExpr11 :: VLRule BottomUpProps
mergeExpr11 q =
  $(pattern 'q "Project es1 (Project es2 (q1))"
    [| do

        return $ do
          logRewrite "Expr.Merge.11" q
          let env  = zip [1..] $(v "es2")
              es1' = map (mergeExpr1 env) $(v "es1")
          void $ replaceWithNew q $ UnOp (Project es1') $(v "q1") |])

mergeExpr12 :: VLRule BottomUpProps
mergeExpr12 q =
  $(pattern 'q "Project es ((q1) BinExpr e2 (q2))"
    [| do
        [e1] <- return $(v "es")
        return $ do
          logRewrite "Expr.Merge.12" q
          let e1' = expr1ToExpr2Right $(v "e1")
              e' = replaceRightCol $(v "e2") e1'
              op = BinOp (BinExpr e') $(v "q1") $(v "q2")
          void $ replaceWithNew q op |])

mergeExpr21Right :: VLRule BottomUpProps
mergeExpr21Right q =
  $(pattern 'q "(q1) BinExpr e2 (Project es (q2))"
    [| do
        [e1] <- return $(v "es")
        return $ do
          logRewrite "Expr.Merge.21.Right" q
          let e2' = replaceRightCol (expr1ToExpr2Right $(v "e1")) $(v "e2")
          void $ replaceWithNew q $ BinOp (BinExpr e2') $(v "q1") $(v "q2") |])

mergeExpr21Left :: VLRule BottomUpProps
mergeExpr21Left q =
  $(pattern 'q "(Project es (q1)) BinExpr e2 (q2)"
    [| do
        [e1] <- return $(v "es")
        return $ do
          logRewrite "Expr.Merge.21.Left" q
          let e2' = replaceLeftCol (expr1ToExpr2Left $(v "e1")) $(v "e2")
          void $ replaceWithNew q $ BinOp (BinExpr e2') $(v "q1") $(v "q2") |])

identityProject :: VLRule BottomUpProps
identityProject q =
  $(pattern 'q "Project ps (q1)"
    [| do
        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "q1")
        predicate $ length $(v "ps") == w

        let sameCol :: (Int, Expr1) -> Bool
            sameCol (i, Column1 i') = i == i'
            sameCol _               = False

        predicate $ all sameCol (zip [1..] $(v "ps"))

        rs <- getRootNodes
        predicate $ not $ q `elem` rs

        return $ do
          logRewrite "Project.Identity" q
          replace q $(v "q1") |])

       
