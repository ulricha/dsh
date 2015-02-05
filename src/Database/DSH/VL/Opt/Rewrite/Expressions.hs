{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ParallelListComp #-}

module Database.DSH.VL.Opt.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import Control.Monad
import Control.Applicative
import Data.Maybe

import Database.Algebra.Dag.Common

import Database.DSH.VL.Lang
import Database.DSH.Common.Opt
import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Rewrite.Common

optExpressions :: VLRewrite Bool
optExpressions = iteratively $ applyToAll inferBottomUp expressionRules

expressionRules :: VLRuleSet BottomUpProps
expressionRules = [ mergeExpr1
                  , identityProject
                  , mergeSelectProject
                  ]

mergeExpr1 :: VLRule BottomUpProps
mergeExpr1 q =
  $(dagPatMatch 'q "Project es1 (Project es2 (q1))"
    [| do

        return $ do
          logRewrite "Expr.Merge.11" q
          let env  = zip [1..] $(v "es2")
              es1' = map (mergeExpr env) $(v "es1")
          void $ replaceWithNew q $ UnOp (Project es1') $(v "q1") |])

mergeSelectProject :: VLRule BottomUpProps
mergeSelectProject q =
  $(dagPatMatch 'q "R1 (qs=Select p (Project projs (q1)))"
     [| do
        return $ do
          logRewrite "Expr.Merge.Select" q
          let env = zip [1..] $(v "projs")
          let p'  = mergeExpr env $(v "p")
          selectNode <- insert $ UnOp (Select p') $(v "q1")
          r1Node     <- insert $ UnOp R1 selectNode
          void $ replaceWithNew q $ UnOp (Project $(v "projs")) r1Node

          r2Parents <- lookupR2Parents $(v "qs")

          -- If there are any R2 nodes linking to the original
          -- Restrict operator (i.e. there are inner vectors to which
          -- changes must be propagated), they have to be rewired to
          -- the new Select operator.
          when (not $ null r2Parents) $ do
            qr2' <- insert $ UnOp R2 selectNode
            mapM_ (\qr2 -> replace qr2 qr2') r2Parents |])

identityProject :: VLRule BottomUpProps
identityProject q =
  $(dagPatMatch 'q "Project ps (q1)"
    [| do
        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "q1")
        predicate $ length $(v "ps") == w

        let sameCol :: (Int, Expr) -> Bool
            sameCol (i, Column i') = i == i'
            sameCol _               = False

        predicate $ all sameCol (zip [1..] $(v "ps"))

        rs <- getRootNodes
        predicate $ not $ q `elem` rs

        return $ do
          logRewrite "Project.Identity" q
          replace q $(v "q1") |])

------------------------------------------------------------------------------
-- Constant expression inputs

liftPairRight :: Monad m => (a, m b) -> m (a, b)
liftPairRight (a, mb) = mb >>= \b -> return (a, b)

mapPair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
mapPair f g (a, b) = (f a, g b)

insertConstants :: [(DBCol, VLVal)] -> Expr -> Expr
insertConstants env expr =
    case expr of
        BinApp o e1 e2 -> BinApp o (insertConstants env e1) (insertConstants env e2)
        UnApp o e1     -> UnApp o (insertConstants env e1)
        Column c       -> case lookup c env of
                               Just val -> Constant val
                               Nothing  -> Column c
        If c t e       -> If (insertConstants env c) (insertConstants env t) (insertConstants env e)
        Constant _     -> expr

constProject :: VLRule BottomUpProps
constProject q =
  $(dagPatMatch 'q "Project projs (q1)"
    [| do
        VProp (DBVConst _ constCols) <- constProp <$> properties $(v "q1")
        let envEntry = liftPairRight . mapPair id (constVal id)
        let constEnv = mapMaybe envEntry $ zip [1..] constCols

        predicate $ not $ null constEnv

        let projs' = map (insertConstants constEnv) $(v "projs")

        -- To avoid rewriting loops, ensure that a change occured.
        predicate $ projs' /= $(v "projs")

        return $ do
          logRewrite "Expr.Project.Const" q
          void $ replaceWithNew q $ UnOp (Project projs') $(v "q1") |])
