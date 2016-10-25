{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell  #-}

module Database.DSH.SL.Opt.Rewrite.Expressions where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang
import           Database.DSH.SL.Opt.Properties.Types
import           Database.DSH.SL.Opt.Rewrite.Common

optExpressions :: SLRewrite TExpr TExpr Bool
optExpressions = iteratively $ applyToAll inferBottomUp expressionRules

expressionRules :: SLRuleSet TExpr TExpr BottomUpProps
expressionRules = [ mergeExpr1
                  , identityProject
                  , mergeSelectProject
                  ]

mergeExpr1 :: SLRule TExpr TExpr BottomUpProps
mergeExpr1 q =
  $(dagPatMatch 'q "Project e2 (Project e1 (q1))"
    [| do

        return $ do
          logRewrite "Expr.Merge.11" q
          let e2' = partialEval $ mergeExpr $(v "e1") $(v "e2")
          void $ replaceWithNew q $ UnOp (Project e2') $(v "q1") |])

mergeSelectProject :: SLRule TExpr TExpr BottomUpProps
mergeSelectProject q =
  $(dagPatMatch 'q "R1 (qs=Select p (Project e (q1)))"
     [| do
        return $ do
          logRewrite "Expr.Merge.Select" q
          let p'  = partialEval $ mergeExpr $(v "e") $(v "p")
          selectNode <- insert $ UnOp (Select p') $(v "q1")
          r1Node     <- insert $ UnOp R1 selectNode
          void $ replaceWithNew q $ UnOp (Project $(v "e")) r1Node

          r2Parents <- lookupR2Parents $(v "qs")

          -- If there are any R2 nodes linking to the original
          -- Restrict operator (i.e. there are inner vectors to which
          -- changes must be propagated), they have to be rewired to
          -- the new Select operator.
          when (not $ null r2Parents) $ do
            qr2' <- insert $ UnOp R2 selectNode
            mapM_ (\qr2 -> replace qr2 qr2') r2Parents |])

identityProject :: SLRule TExpr TExpr BottomUpProps
identityProject q =
  $(dagPatMatch 'q "Project e (q1)"
    [| do
        TInput <- return $(v "e")

        return $ do
          logRewrite "Project.Identity" q
          replace q $(v "q1") |])

------------------------------------------------------------------------------
-- Constant expression inputs

-- liftPairRight :: Monad m => (a, m b) -> m (a, b)
-- liftPairRight (a, mb) = mb >>= \b -> return (a, b)

-- mapPair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
-- mapPair f g (a, b) = (f a, g b)

-- insertConstants :: [(DBCol, ScalarVal)] -> Expr -> Expr
-- insertConstants env expr =
--     case expr of
--         BinApp o e1 e2 -> BinApp o (insertConstants env e1) (insertConstants env e2)
--         UnApp o e1     -> UnApp o (insertConstants env e1)
--         Column c       -> case lookup c env of
--                                Just val -> Constant val
--                                Nothing  -> Column c
--         If c t e       -> If (insertConstants env c) (insertConstants env t) (insertConstants env e)
--         Constant _     -> expr

-- constProject :: SLRule TExpr TExpr BottomUpProps
-- constProject q =
--   $(dagPatMatch 'q "Project projs (q1)"
--     [| do
--         VProp (ConstVec constCols) <- constProp <$> properties $(v "q1")
--         let envEntry = liftPairRight . mapPair id (constVal id)
--         let constEnv = mapMaybe envEntry $ zip [1..] constCols

--         predicate $ not $ null constEnv

--         let projs' = map (insertConstants constEnv) $(v "projs")

--         -- To avoid rewriting loops, ensure that a change occured.
--         predicate $ projs' /= $(v "projs")

--         return $ do
--           logRewrite "Expr.Project.Const" q
--           void $ replaceWithNew q $ UnOp (Project projs') $(v "q1") |])
