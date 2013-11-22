module Database.DSH.Optimizer.VL.Properties.BottomUp where

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data

import           Database.DSH.Optimizer.Common.Aux
import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.Card
import           Database.DSH.Optimizer.VL.Properties.Const
import           Database.DSH.Optimizer.VL.Properties.Empty
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Properties.Untainted
import           Database.DSH.Optimizer.VL.Properties.VectorType
import           Database.DSH.Optimizer.VL.Properties.VerticalForm

-- FIXME this is (almost) identical to its X100 counterpart -> merge
inferWorker :: VL -> AlgNode -> NodeMap BottomUpProps -> BottomUpProps
inferWorker op n pm =
    let res =
           case op of
                TerOp vl c1 c2 c3 ->
                  let c1Props = lookupUnsafe pm "no children properties" c1
                      c2Props = lookupUnsafe pm "no children properties" c2
                      c3Props = lookupUnsafe pm "no children properties" c3
                  in inferTerOp n c1 c2 c3 vl c1Props c2Props c3Props
                BinOp vl c1 c2 ->
                  let c1Props = lookupUnsafe pm "no children properties" c1
                      c2Props = lookupUnsafe pm "no children properties" c2
                  in inferBinOp n c1 c2 vl c1Props c2Props
                UnOp vl c ->
                  let cProps = lookupUnsafe pm "no children properties" c
                  in inferUnOp n c vl cProps
                NullaryOp vl -> inferNullOp n vl
    in case res of
            Left msg -> error $ "Inference failed at node " ++ (show n) ++ ": " ++ msg
            Right props -> props

inferNullOp :: AlgNode -> NullOp -> Either String BottomUpProps
inferNullOp n op = do
  opEmpty <- inferEmptyNullOp op
  opConst <- inferConstVecNullOp op
  opType <- inferVectorTypeNullOp op
  opCard <- inferCardOneNullOp op
  opVerticallyIntact <- inferVerticallyIntactNullOp op
  let opUntainted = inferUntaintedNullOp op
  return $ BUProps { emptyProp = opEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , untaintedProp = opUntainted
                   , verticallyIntactProp = opVerticallyIntact
                   , vectorTypeProp = opType }

inferUnOp :: AlgNode -> AlgNode -> UnOp -> BottomUpProps -> Either String BottomUpProps
inferUnOp n c op cProps = do
  opEmpty <- inferEmptyUnOp (emptyProp cProps) op
  opType <- inferVectorTypeUnOp (vectorTypeProp cProps) op
  opConst <- inferConstVecUnOp (constProp cProps) op
  opCard <- inferCardOneUnOp (card1Prop cProps) op
  opVerticallyIntact <- inferVerticallyIntactUnOp (verticallyIntactProp cProps) c op
  let opUntainted = inferUntaintedUnOp (untaintedProp cProps) c op
  return $ BUProps { emptyProp = opEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , untaintedProp = opUntainted
                   , verticallyIntactProp = opVerticallyIntact
                   , vectorTypeProp = opType }

inferBinOp :: AlgNode -> AlgNode -> AlgNode -> BinOp -> BottomUpProps -> BottomUpProps -> Either String BottomUpProps
inferBinOp n c1 c2 op c1Props c2Props = do
  opEmpty <- inferEmptyBinOp (emptyProp c1Props) (emptyProp c2Props) op
  opType <- inferVectorTypeBinOp (vectorTypeProp c1Props) (vectorTypeProp c2Props) op
  opConst <- inferConstVecBinOp (constProp c1Props) (constProp c2Props) op
  opCard <- inferCardOneBinOp (card1Prop c1Props) (card1Prop c2Props) op
  opVerticallyIntact <- inferVerticallyIntactBinOp (verticallyIntactProp c1Props)
                                                   (verticallyIntactProp c2Props)
                                                   c1
                                                   c2
                                                   op
  let opUntainted = inferUntaintedBinOp (untaintedProp c1Props) (untaintedProp c2Props) c1 c2 op
  return $ BUProps { emptyProp = opEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , untaintedProp = opUntainted
                   , verticallyIntactProp = opVerticallyIntact
                   , vectorTypeProp = opType }

inferTerOp :: AlgNode
              -> AlgNode
              -> AlgNode
              -> AlgNode
              -> TerOp
              -> BottomUpProps
              -> BottomUpProps
              -> BottomUpProps
              -> Either String BottomUpProps
inferTerOp n c1 c2 c3 op c1Props c2Props c3Props = do
  opEmpty <- inferEmptyTerOp (emptyProp c1Props) (emptyProp c2Props) (emptyProp c3Props) op
  opType <- inferVectorTypeTerOp (vectorTypeProp c1Props) (vectorTypeProp c2Props) (vectorTypeProp c3Props) op
  opConst <- inferConstVecTerOp (constProp c1Props) (constProp c2Props) (constProp c3Props) op
  opCard <- inferCardOneTerOp (card1Prop c1Props) (card1Prop c2Props) (card1Prop c3Props) op
  opVerticallyIntact <- inferVerticallyIntactTerOp (verticallyIntactProp c1Props)
                                                   (verticallyIntactProp c2Props)
                                                   (verticallyIntactProp c3Props)
                                                   c1
                                                   c2
                                                   c3
                                                   op
  let opUntainted = inferUntaintedTerOp (untaintedProp c1Props) (untaintedProp c2Props) (untaintedProp c3Props) c1 c2 c3 op
  return $ BUProps { emptyProp = opEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , untaintedProp = opUntainted
                   , verticallyIntactProp = opVerticallyIntact
                   , vectorTypeProp = opType }

inferBottomUpProperties :: AlgebraDag VL -> NodeMap BottomUpProps
inferBottomUpProperties dag = inferBottomUpGeneral inferWorker dag
