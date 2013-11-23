{-# LANGUAGE TemplateHaskell #-}

{- Based on the ReqColumns property, remove columns or entire operators which
produce value vectors but whose payload output is not needed downstream. This
is of course only sound if the operator in question does not change the vertical
layout.  -}

module Database.DSH.Optimizer.VL.Rewrite.Unused where

import           Control.Applicative

import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data

import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Rewrite.Common

pruneUnused :: VLRewrite Bool
pruneUnused = applyToAll inferTopDown [ {- unusedProject -} ]

{-

FIXME seems a bit fishy

unusedProject :: VLRule TopDownProps
unusedProject q =
  $(pattern 'q "[ProjectL | Project] _ (q1)"
    [| do
      -- Don't remove top-level projections. They ensure that all required
      -- columns required for the result type are actually there.
      predicate =<< not <$> elem q <$> getRootNodes

      reqColumns <- reqColumnsProp <$> properties q
      
      case reqColumns of
        VProp (Just []) -> return ()
        VProp (Just _)  -> fail "no match"
        p               -> error ("Unused.Project: " ++ show p)
        

      return $ do
        logRewrite "Unused.Project" q
        replace q $(v "q1") |])
-}
