{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.Optimizer.VL.Rewrite.ToDescr where

import           Control.Applicative
import           Control.Monad

import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Optimizer.Common.Rewrite
import           Database.DSH.Flattening.Optimizer.VL.Properties.Types
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Common

pruneColumns :: VLRewrite Bool
pruneColumns = applyToAll inferTopDown pruneRules

pruneRules :: VLRuleSet TopDownProps
pruneRules = [ insertToDescrForProjectPayload ]

insertToDescrForProjectPayload :: VLRule TopDownProps
insertToDescrForProjectPayload q =
  $(pattern 'q "ProjectPayload _ (q1)"
    [| do
        tdProps <- toDescrProp <$> properties q
        predicate $ case tdProps of
          VProp (Just b)  -> b
          VProp Nothing   -> False
          _               -> error "insertToDescrForProjectPayload"

        return $ do
          logRewrite "ToDescr.ProjectPayload" q
          void $ replaceWithNew q $ UnOp ToDescr $(v "q1") |])


