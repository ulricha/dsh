{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Rewrite.Basic where
       
import Debug.Trace
       
import Control.Applicative
import Control.Monad
import Data.Maybe
import qualified Data.Set.Monad as S

import Database.Algebra.Dag.Common
import Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Impossible
import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.TA.Rewrite.Common
import Database.DSH.Optimizer.TA.Properties.Types

cleanup :: TARewrite Bool
cleanup = iteratively $ sequenceRewrites [ applyToAll noProps cleanupRules 
                                         , applyToAll inferTopDown cleanupRulesTopDown 
                                         ]

cleanupRules :: TARuleSet ()
cleanupRules = [ stackedProject ]

cleanupRulesTopDown :: TARuleSet TopDownProps
cleanupRulesTopDown = [ unreferencedRownum ]

mergeProjections :: [Proj] -> [Proj] -> [Proj]
mergeProjections proj1 proj2 = map (\(c, e) -> (c, inline e)) proj1

  where
    inline :: Expr -> Expr
    inline (BinAppE op e1 e2) = BinAppE op (inline e1) (inline e2)
    inline (UnAppE op e)      = UnAppE op (inline e)
    inline (ColE c)           = fromMaybe $impossible (lookup c proj2)
    inline (ConstE val)       = ConstE val

stackedProject :: TARule ()
stackedProject q =
  $(pattern 'q "Project ps1 (Project ps2 (qi))"
    [| do
         return $ do
           let ps = mergeProjections $(v "ps1") $(v "ps2")
           logRewrite "Basic.Project.Merge" q
           void $ replaceWithNew q $ UnOp (Project ps) $(v "qi") |])
           
unreferencedRownum :: TARule TopDownProps
unreferencedRownum q = 
  $(pattern 'q "RowNum args (q1)"
    [| do
         (res, _, _) <- return $(v "args")
         neededCols  <- icolsProp <$> properties q
         trace (show neededCols) $ return ()
         predicate $ not (res `S.member` neededCols)
         
         return $ do
           logRewrite "Basic.Rownum.Prune" q
           replace q $(v "q1") |])
 
