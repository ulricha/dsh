{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.BottomUp where

import Database.Algebra.Dag
import Database.Algebra.Dag.Common
import Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Impossible

import Database.DSH.Optimizer.Common.Aux
import Database.DSH.Optimizer.Common.Rewrite

import Database.DSH.Optimizer.TA.Properties.Types
import Database.DSH.Optimizer.TA.Properties.Cols

-- FIXME this is (almost) identical to its X100 counterpart -> merge
inferWorker :: PFAlgebra -> AlgNode -> NodeMap BottomUpProps -> BottomUpProps
inferWorker op n pm =
    let res =
           case op of
                BinOp vl c1 c2 ->
                  let c1Props = lookupUnsafe pm "no children properties" c1
                      c2Props = lookupUnsafe pm "no children properties" c2
                  in inferBinOp vl c1Props c2Props
                UnOp vl c ->
                  let cProps = lookupUnsafe pm "no children properties" c
                  in inferUnOp vl cProps
                NullaryOp vl -> inferNullOp vl
    in case res of
            Left msg -> error $ "Inference failed at node " ++ (show n) ++ ": " ++ msg
            Right props -> props

inferNullOp :: NullOp -> Either String BottomUpProps
inferNullOp op = do
  let opCols = inferColsNullOp op
  return $ BUProps { colsProp = opCols }

inferUnOp :: UnOp -> BottomUpProps -> Either String BottomUpProps
inferUnOp op cProps = do
  let opCols = inferColsUnOp (colsProp cProps) op
  return $ BUProps { colsProp = opCols }

inferBinOp :: BinOp -> BottomUpProps -> BottomUpProps -> Either String BottomUpProps
inferBinOp op c1Props c2Props = do
  let opCols = inferColsBinOp (colsProp c1Props) (colsProp c2Props) op
  return $ BUProps { colsProp = opCols }

inferBottomUpProperties :: AlgebraDag PFAlgebra -> NodeMap BottomUpProps
inferBottomUpProperties dag = inferBottomUpGeneral inferWorker dag
