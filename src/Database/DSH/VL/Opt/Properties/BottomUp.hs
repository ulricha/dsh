module Database.DSH.VL.Opt.Properties.BottomUp where

import Text.Printf

import Database.Algebra.Dag
import Database.Algebra.Dag.Common

import Database.DSH.VL.Lang
import Database.DSH.Common.Opt

import Database.DSH.VL.Opt.Properties.Card
import Database.DSH.VL.Opt.Properties.Const
import Database.DSH.VL.Opt.Properties.Empty
import Database.DSH.VL.Opt.Properties.NonEmpty
import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Properties.VectorType

-- FIXME this is (almost) identical to its X100 counterpart -> merge
inferWorker :: NodeMap VL -> VL -> AlgNode -> NodeMap BottomUpProps -> BottomUpProps
inferWorker d op node pm =
    case op of
         TerOp vl c1 c2 c3 ->
           let c1Props = lookupUnsafe pm "no children properties" c1
               c2Props = lookupUnsafe pm "no children properties" c2
               c3Props = lookupUnsafe pm "no children properties" c3
           in checkError d node [c1Props, c2Props, c3Props] pm $ inferTerOp vl c1Props c2Props c3Props
         BinOp vl c1 c2 ->
           let c1Props = lookupUnsafe pm "no children properties" c1
               c2Props = lookupUnsafe pm "no children properties" c2
           in checkError d node [c1Props, c2Props] pm $ inferBinOp vl c1Props c2Props
         UnOp vl c ->
           let cProps = lookupUnsafe pm "no children properties" c
           in checkError d node [cProps] pm $ inferUnOp vl cProps
         NullaryOp vl -> checkError d node [] pm $ inferNullOp vl

checkError :: NodeMap VL -> AlgNode -> [BottomUpProps] -> NodeMap BottomUpProps -> Either String BottomUpProps -> BottomUpProps
checkError d n childProps propMap (Left msg) =
    let childPropsMsg = concatMap ((++) "\n" . show) childProps
        completeMsg   = printf "Inference failed at node %d\n%s\n%s\n%s\n%s" n msg childPropsMsg (show propMap) (show d)
    in error completeMsg
checkError _ _ _ _ (Right props) = props

inferNullOp :: NullOp -> Either String BottomUpProps
inferNullOp op = do
  opEmpty    <- inferEmptyNullOp op
  opNonEmpty <- inferNonEmptyNullOp op
  opConst    <- inferConstVecNullOp op
  opType     <- inferVectorTypeNullOp op
  opCard     <- inferCardOneNullOp op
  return $ BUProps { emptyProp = opEmpty
                   , nonEmptyProp = opNonEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , vectorTypeProp = opType }

inferUnOp :: UnOp -> BottomUpProps -> Either String BottomUpProps
inferUnOp op cProps = do
  opEmpty    <- inferEmptyUnOp (emptyProp cProps) op
  opNonEmpty <- inferNonEmptyUnOp (nonEmptyProp cProps) op
  opType     <- inferVectorTypeUnOp (vectorTypeProp cProps) op
  opConst    <- inferConstVecUnOp (constProp cProps) op
  opCard     <- inferCardOneUnOp (card1Prop cProps) op
  return $ BUProps { emptyProp = opEmpty
                   , nonEmptyProp = opNonEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , vectorTypeProp = opType }

inferBinOp :: BinOp -> BottomUpProps -> BottomUpProps -> Either String BottomUpProps
inferBinOp op c1Props c2Props = do
  opEmpty    <- inferEmptyBinOp (emptyProp c1Props) (emptyProp c2Props) op
  opNonEmpty <- inferNonEmptyBinOp (nonEmptyProp c1Props) (nonEmptyProp c2Props) op
  opType     <- inferVectorTypeBinOp (vectorTypeProp c1Props) (vectorTypeProp c2Props) op
  opConst    <- inferConstVecBinOp (constProp c1Props) (constProp c2Props) op
  opCard     <- inferCardOneBinOp (card1Prop c1Props) (card1Prop c2Props) op
  return $ BUProps { emptyProp = opEmpty
                   , nonEmptyProp = opNonEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , vectorTypeProp = opType }

inferTerOp :: TerOp
           -> BottomUpProps
           -> BottomUpProps
           -> BottomUpProps
           -> Either String BottomUpProps
inferTerOp op c1Props c2Props c3Props = do
  opEmpty    <- inferEmptyTerOp (emptyProp c1Props) (emptyProp c2Props) (emptyProp c3Props) op
  opNonEmpty <- inferNonEmptyTerOp (nonEmptyProp c1Props) (nonEmptyProp c2Props) (nonEmptyProp c3Props) op
  opType     <- inferVectorTypeTerOp (vectorTypeProp c1Props) (vectorTypeProp c2Props) (vectorTypeProp c3Props) op
  opConst    <- inferConstVecTerOp (constProp c1Props) (constProp c2Props) (constProp c3Props) op
  opCard     <- inferCardOneTerOp (card1Prop c1Props) (card1Prop c2Props) (card1Prop c3Props) op
  return $ BUProps { emptyProp = opEmpty
                   , nonEmptyProp = opNonEmpty
                   , constProp = opConst
                   , card1Prop = opCard
                   , vectorTypeProp = opType }

inferBottomUpProperties :: AlgebraDag VL -> NodeMap BottomUpProps
inferBottomUpProperties dag = inferBottomUpGeneral inferWorker dag
