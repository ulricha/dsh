{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ParallelListComp #-}

module Database.DSH.Optimizer.VL.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import Control.Monad
import Control.Applicative
import Data.Maybe

import Database.Algebra.Dag.Common

import Database.DSH.Impossible
import Database.DSH.VL.Lang
import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Rewrite.Common

optExpressions :: VLRewrite Bool
optExpressions = iteratively $ applyToAll inferBottomUp expressionRules

expressionRules :: VLRuleSet BottomUpProps
expressionRules = [ mergeExpr2SameInput
                  , mergeExpr12
                  , mergeExpr11
                  , mergeExpr21Right
                  , mergeExpr21Left 
                  , identityProject
                  , leftOnlyBinExpr
                  , rightOnlyBinExpr
                  , mergeSelectProject
                  , constBinExprLeft
                  , constBinExprRight
                  ]

-- | Traverse a *Expr2* and apply given functions to column
-- references.
mapExpr2Cols :: (LeftCol -> Expr2) -> (RightCol -> Expr2) -> Expr2 -> Expr2
mapExpr2Cols leftFun rightFun expr = case expr of
    BinApp2 op e1 e2 -> BinApp2 op (mapExpr2Cols leftFun rightFun e1)
                                   (mapExpr2Cols leftFun rightFun e2)
    UnApp2 op e1     -> UnApp2 op (mapExpr2Cols leftFun rightFun e1)
    Column2Left c    -> leftFun c
    Column2Right c   -> rightFun c
    Constant2 val    -> Constant2 val
    If2 c t e        -> If2 (mapExpr2Cols leftFun rightFun c)
                            (mapExpr2Cols leftFun rightFun t)
                            (mapExpr2Cols leftFun rightFun e)

replaceLeftCol :: [(DBCol, Expr2)] -> Expr2 -> Expr2
replaceLeftCol env expr = mapExpr2Cols replaceLeftCol Column2Right expr
  where
    replaceLeftCol :: LeftCol -> Expr2
    replaceLeftCol (L c) = maybe $impossible id (lookup c env)

replaceRightCol :: [(DBCol, Expr2)] -> Expr2 -> Expr2
replaceRightCol env expr = mapExpr2Cols Column2Left replaceRightCol expr
  where
    replaceRightCol :: RightCol -> Expr2
    replaceRightCol (R c) = maybe $impossible id (lookup c env)


expr2ToExpr1 :: Expr2 -> Expr1
expr2ToExpr1 (BinApp2 o e1 e2)    = BinApp1 o (expr2ToExpr1 e1) (expr2ToExpr1 e2)
expr2ToExpr1 (UnApp2 o e)         = UnApp1 o (expr2ToExpr1 e)
expr2ToExpr1 (Column2Left (L c))  = Column1 c
expr2ToExpr1 (Column2Right (R c)) = Column1 c
expr2ToExpr1 (Constant2 val)      = Constant1 val
expr2ToExpr1 (If2 c t e)          = If1 (expr2ToExpr1 c) (expr2ToExpr1 t) (expr2ToExpr1 e)

-- Merge multiple stacked CompExpr operators if they have the same input.

-- FIXME this is way too hackish. Implement a clean solution to insert expressions into
-- other expressions
expr1ToExpr2Right :: Expr1 -> Expr2
expr1ToExpr2Right expr =
    case expr of
        If1 c t e       -> If2 (expr1ToExpr2Right c) (expr1ToExpr2Right t) (expr1ToExpr2Right e)
        BinApp1 o e1 e2 -> BinApp2 o (expr1ToExpr2Right e1) (expr1ToExpr2Right e2)
        UnApp1 o e1     -> UnApp2 o (expr1ToExpr2Right e1)
        Column1 c       -> Column2Right (R c)
        Constant1 val   -> Constant2 val

expr1ToExpr2Left :: Expr1 -> Expr2
expr1ToExpr2Left expr =
    case expr of
        If1 c t e       -> If2 (expr1ToExpr2Left c) (expr1ToExpr2Left t) (expr1ToExpr2Left e)
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

mergeSelectProject :: VLRule BottomUpProps
mergeSelectProject q =
  $(pattern 'q "Select p (Project projs (q1))"
     [| do
        return $ do
          logRewrite "Expr.Merge.Select" q
          let env = zip [1..] $(v "projs")
          let p'  = mergeExpr1 env $(v "p")
          selectNode <- insert $ UnOp (Select p') $(v "q1")
          void $ replaceWithNew q $ UnOp (Project $(v "projs")) selectNode |])

mergeExpr12 :: VLRule BottomUpProps
mergeExpr12 q =
  $(pattern 'q "Project es ((q1) BinExpr e2 (q2))"
    [| do
        [e1] <- return $(v "es")
        return $ do
          logRewrite "Expr.Merge.12" q
          let e1' = expr1ToExpr2Right $(v "e1")
              e' = replaceRightCol [(1, $(v "e2"))] e1'
              op = BinOp (BinExpr e') $(v "q1") $(v "q2")
          void $ replaceWithNew q op |])

mergeExpr21Right :: VLRule BottomUpProps
mergeExpr21Right q =
  $(pattern 'q "(q1) BinExpr e2 (Project es (q2))"
    [| do
        let env = zip [1..] (map expr1ToExpr2Right $(v "es"))
        return $ do
          logRewrite "Expr.Merge.21.Right" q
          let e2' = replaceRightCol env $(v "e2")
          void $ replaceWithNew q $ BinOp (BinExpr e2') $(v "q1") $(v "q2") |])

mergeExpr21Left :: VLRule BottomUpProps
mergeExpr21Left q =
  $(pattern 'q "(Project es (q1)) BinExpr e2 (q2)"
    [| do
        let env = zip [1..] (map expr1ToExpr2Left $(v "es"))
        return $ do
          logRewrite "Expr.Merge.21.Left" q
          let e2' = replaceLeftCol env $(v "e2")
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

leftOnlyExpr :: Expr2 -> Bool
leftOnlyExpr expr = 
    case expr of
        BinApp2 _ e1 e2 -> leftOnlyExpr e1 && leftOnlyExpr e2
        If2 c t e       -> all leftOnlyExpr [c, t, e]
        UnApp2 _ e      -> leftOnlyExpr e
        Constant2 _     -> True
        Column2Left _   -> True
        Column2Right _  -> False

rightOnlyExpr :: Expr2 -> Bool
rightOnlyExpr expr = 
    case expr of
        BinApp2 _ e1 e2 -> rightOnlyExpr e1 && rightOnlyExpr e2
        UnApp2 _ e      -> rightOnlyExpr e
        If2 c t e       -> all rightOnlyExpr [c, t, e]
        Constant2 _     -> True
        Column2Left _   -> False
        Column2Right _  -> True

-- | If a binary expression op references only columns from it's left
-- input, replace it with a simple projection.
leftOnlyBinExpr :: VLRule p
leftOnlyBinExpr q = 
  $(pattern 'q "(q1) BinExpr expr (_)"
    [| do
        predicate $ leftOnlyExpr $(v "expr")
       
        return $ do
          logRewrite "Expr.Bin.LeftOnly" q
          let expr' = expr2ToExpr1 $(v "expr")
          void $ replaceWithNew q $ UnOp (Project [expr']) $(v "q1") |])

-- | Mirrored dual of `leftOnlyBinExpr`
rightOnlyBinExpr :: VLRule p
rightOnlyBinExpr q = 
  $(pattern 'q "(_) BinExpr expr (q2)"
    [| do
        predicate $ rightOnlyExpr $(v "expr")
       
        return $ do
          logRewrite "Expr.Bin.RightOnly" q
          let expr' = expr2ToExpr1 $(v "expr")
          void $ replaceWithNew q $ UnOp (Project [expr']) $(v "q2") |])

------------------------------------------------------------------------------
-- Constant expression inputs

insertConstantsLeft :: [(DBCol, VLVal)] -> Expr2 -> Expr2
insertConstantsLeft env expr =
    mapExpr2Cols leftConstant Column2Right expr
  where
    leftConstant (L c) =
        case lookup c env of
            Just v  -> Constant2 v
            Nothing -> Column2Left (L c)

insertConstantsRight :: [(DBCol, VLVal)] -> Expr2 -> Expr2
insertConstantsRight env expr =
    mapExpr2Cols Column2Left rightConstant expr
  where
    rightConstant (R c) =
        case lookup c env of
            Just v  -> Constant2 v
            Nothing -> Column2Right (R c)

liftPairRight :: Monad m => (a, m b) -> m (a, b)
liftPairRight (a, mb) = mb >>= \b -> return (a, b)

mapPair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
mapPair f g (a, b) = (f a, g b)

-- | If there are any constant columns in the left input of a BinExpr
-- operator, inline them.
constBinExprLeft :: VLRule BottomUpProps
constBinExprLeft q =
  $(pattern 'q "(q1) BinExpr expr (q2)"
    [| do
        VProp (DBVConst _ constCols) <- constProp <$> properties $(v "q1")
        let envEntry = liftPairRight . mapPair id (constVal id)
        let constEnv = mapMaybe envEntry $ zip [1..] constCols
        predicate $ not $ null constEnv
        let expr' = insertConstantsLeft constEnv $(v "expr")
  
        -- To avoid rewriting loops, ensure that a change occured.
        predicate $ expr' /= $(v "expr")

        return $ do
          logRewrite "Expr.Bin.Constant.Left" q
          void $ replaceWithNew q $ BinOp (BinExpr expr') $(v "q1") $(v "q2") |])

-- | If there are any constant columns in the right input of a BinExpr
-- operator, inline them.
constBinExprRight :: VLRule BottomUpProps
constBinExprRight q =
  $(pattern 'q "(q1) BinExpr expr (q2)"
    [| do
        VProp (DBVConst _ constCols) <- constProp <$> properties $(v "q2")
        let envEntry = liftPairRight . mapPair id (constVal id)
        let constEnv = mapMaybe envEntry $ zip [1..] constCols
        predicate $ not $ null constEnv
        let expr' = insertConstantsRight constEnv $(v "expr")
  
        -- To avoid rewriting loops, ensure that a change occured.
        predicate $ expr' /= $(v "expr")

        return $ do
          logRewrite "Expr.Bin.Constant.Right" q
          void $ replaceWithNew q $ BinOp (BinExpr expr') $(v "q1") $(v "q2") |])

