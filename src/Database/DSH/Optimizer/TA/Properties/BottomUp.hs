{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.BottomUp where

import qualified Data.Set.Monad                             as S

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang

import           Database.DSH.Impossible

import           Database.DSH.Optimizer.Common.Auxiliary
import           Database.DSH.Optimizer.Common.Rewrite

import           Database.DSH.Optimizer.TA.Properties.Card1
import           Database.DSH.Optimizer.TA.Properties.Cols
import           Database.DSH.Optimizer.TA.Properties.Empty
import           Database.DSH.Optimizer.TA.Properties.Keys
import           Database.DSH.Optimizer.TA.Properties.Order
import           Database.DSH.Optimizer.TA.Properties.Const
import           Database.DSH.Optimizer.TA.Properties.Types

-- FIXME this is (almost) identical to its X100 counterpart -> merge
inferWorker :: NodeMap TableAlgebra -> TableAlgebra -> AlgNode -> NodeMap BottomUpProps -> BottomUpProps
inferWorker _ op n pm =
    let res =
           case op of
                TerOp _ _ _ _ -> $impossible
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
  let opCols  = inferColsNullOp op
      opKeys  = inferKeysNullOp op
      opEmpty = inferEmptyNullOp op
      opCard1 = inferCard1NullOp op
      -- We only care for rownum-generated columns. Therefore, For
      -- nullary operators order is empty.
      opOrder = []
      opConst = inferConstNullOp op
  return $ BUProps { pCols = opCols
                   , pKeys = opKeys
                   , pEmpty = opEmpty
                   , pCard1 = opCard1
                   , pOrder = opOrder
                   , pConst = opConst
                   }

inferUnOp :: UnOp -> BottomUpProps -> Either String BottomUpProps
inferUnOp op cProps = do
  let opCols  = inferColsUnOp (pCols cProps) op
      opKeys  = inferKeysUnOp (pKeys cProps) (pCard1 cProps) (S.map fst $ pCols cProps) op
      opEmpty = inferEmptyUnOp (pEmpty cProps) op
      opCard1 = inferCard1UnOp (pCard1 cProps) (pEmpty cProps) op
      opOrder = inferOrderUnOp (pOrder cProps) op
      opConst = inferConstUnOp (pConst cProps) op
  return $ BUProps { pCols = opCols
                   , pKeys = opKeys
                   , pEmpty = opEmpty
                   , pCard1 = opCard1
                   , pOrder = opOrder
                   , pConst = opConst
                   }

inferBinOp :: BinOp -> BottomUpProps -> BottomUpProps -> Either String BottomUpProps
inferBinOp op c1Props c2Props = do
  let opCols  = inferColsBinOp (pCols c1Props) (pCols c2Props) op
      opKeys  = inferKeysBinOp (pKeys c1Props) (pKeys c2Props) (pCard1 c1Props) (pCard1 c2Props) op
      opEmpty = inferEmptyBinOp (pEmpty c1Props) (pEmpty c2Props) op
      opCard1 = inferCard1BinOp (pCard1 c1Props) (pCard1 c2Props) op
      opOrder = inferOrderBinOp (pOrder c1Props) (pOrder c2Props) op
      opConst = inferConstBinOp (pConst c1Props) (pConst c2Props) op
  return $ BUProps { pCols = opCols
                   , pKeys = opKeys
                   , pEmpty = opEmpty
                   , pCard1 = opCard1
                   , pOrder = opOrder
                   , pConst = opConst
                   }

inferBottomUpProperties :: AlgebraDag TableAlgebra -> NodeMap BottomUpProps
inferBottomUpProperties dag = inferBottomUpGeneral inferWorker dag
