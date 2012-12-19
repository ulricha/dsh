{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Flattening.Optimizer.VL.Rewrite.MergeProjections where

import           Database.Algebra.Dag.Common
import           Database.Algebra.Rewrite
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Common

mergeProjections :: VLRewrite Bool
mergeProjections = iteratively $ preOrder noProps mergeRules

mergeRules :: VLRuleSet ()
mergeRules = [ mergeProjectL ]

colMap :: [DBCol] -> [(DBCol, DBCol)]
colMap cols = zip [1 .. length cols] cols

mapCols :: [(DBCol, DBCol)] -> [DBCol] -> [DBCol]
mapCols mapping cols = map (lookupCol mapping) cols
  where lookupCol m c = case lookup c m of
          Just c' -> c'
          Nothing -> error $ "VL.MergeProjections: column not found " ++ (show c)

mergeProjectL :: VLRule ()
mergeProjectL q =
  $(pattern 'q "ProjectL cols1 (ProjectL cols2 (q1))"
    [| do
        return ()
        return $ do
          logRewrite "Merge.Project.Narrowing" q
          let cols = mapCols (colMap $(v "cols2")) $(v "cols1")
              projectOp = UnOp (ProjectL $(v "cols")) $(v "q1")
          replace q projectOp |])
