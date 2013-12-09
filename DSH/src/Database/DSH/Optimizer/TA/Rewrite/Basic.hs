{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Rewrite.Basic where
       
import Debug.Trace
       
import Control.Monad
import Data.Maybe

import Database.Algebra.Dag.Common
import Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Impossible
import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.TA.Rewrite.Common

cleanup :: TARewrite Bool
cleanup = iteratively $ sequenceRewrites [ applyToAll noProps cleanupRules ]

cleanupRules :: TARuleSet ()
cleanupRules = [ stackedProject ]

mergeProjections :: [Proj] -> [Proj] -> [Proj]
mergeProjections proj1 proj2 = map (\(c, e) -> (c, inline e)) proj1

  where
    inline :: Expr -> Expr
    inline (BinAppE op e1 e2) = BinAppE op (inline e1) (inline e2)
    inline (UnAppE op e)      = UnAppE op (inline e)
    inline (ColE c)           = fromMaybe $impossible (lookup c proj2)
    inline (ConstE v)         = ConstE v 

stackedProject :: TARule ()
stackedProject q =
  $(pattern 'q "Project ps1 (Project ps2 (qi))"
    [| do
         return $ do
           let ps = trace ("at " ++ show q) $ mergeProjections $(v "ps1") $(v "ps2")
           logRewrite "Basic.Merge.Project" q
           void $ replaceWithNew q $ UnOp (Project ps) $(v "qi") |])
           
         
