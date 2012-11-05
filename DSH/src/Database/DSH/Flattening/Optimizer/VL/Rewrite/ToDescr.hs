{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.ToDescr where

import Control.Monad
import Control.Applicative
  
import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

import Optimizer.Common.Match
import Optimizer.Common.Traversal

import Optimizer.VL.Rewrite.Common
import Optimizer.VL.Properties.Types
  
pruneColumns :: VLRewrite Bool
pruneColumns = preOrder inferTopDown pruneRules

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
          void $ relinkToNew q $ UnOp ToDescr $(v "q1") |])


