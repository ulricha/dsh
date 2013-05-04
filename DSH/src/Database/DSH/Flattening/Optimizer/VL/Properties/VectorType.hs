-- FIXME introduce consistency checks for schema inference

module Database.DSH.Flattening.Optimizer.VL.Properties.VectorType where

import Control.Monad
import Data.Functor

import Database.DSH.Flattening.Optimizer.VL.Properties.Types
  
import Database.Algebra.VL.Data
  
{- Implement more checks: check the input types for correctness -}

vectorWidth :: VectorProp VectorType -> Int
vectorWidth (VProp (ValueVector w))  = w
vectorWidth (VProp (AtomicVector w)) = w
vectorWidth _                        = error "vectorWidth: non-ValueVector input"

inferVectorTypeNullOp :: NullOp -> Either String (VectorProp VectorType)
inferVectorTypeNullOp op =
  case op of
    SingletonDescr               -> Right $ VProp $ ValueVector 0
    ConstructLiteralTable t _    -> Right $ VProp $ ValueVector $ length t
    ConstructLiteralValue t _    -> Right $ VProp $ ValueVector $ length t
    TableRef              _ cs _ -> Right $ VProp $ ValueVector $ length cs
  
unpack :: VectorProp VectorType -> Either String VectorType
unpack (VProp s) = Right s
unpack _         = Left "Input is not a single vector property" 

inferVectorTypeUnOp :: VectorProp VectorType -> UnOp -> Either String (VectorProp VectorType)
inferVectorTypeUnOp s op = 
  case op of
    Unique -> VProp <$> unpack s
    UniqueL -> VProp <$> unpack s
    NotPrim -> Right $ VProp $ AtomicVector 1
    NotVec -> Right $ VProp $ ValueVector 1
    LengthA -> Right $ VProp $ AtomicVector 1
    DescToRename -> Right $ VProp $ RenameVector
    Segment -> VProp <$> unpack s
    Unsegment -> VProp <$> unpack s
    VecSum _ -> Right $ VProp $ AtomicVector 1
    VecAvg -> Right $ VProp $ AtomicVector 1
    VecMin -> Right $ VProp $ AtomicVector 1
    VecMinL -> Right $ VProp $ ValueVector 1
    VecMax -> Right $ VProp $ AtomicVector 1
    VecMaxL -> Right $ VProp $ ValueVector 1
    ProjectL ps -> Right $ VProp $ ValueVector $ length ps
    ProjectA ps -> Right $ VProp $ AtomicVector $ length ps
    IntegerToDoubleA -> Right $ VProp $ AtomicVector 1
    IntegerToDoubleL -> Right $ VProp $ ValueVector 1
    ReverseA -> liftM2 VPropPair (unpack s) (Right PropVector)
    ReverseL -> liftM2 VPropPair (unpack s) (Right PropVector)
    FalsePositions -> Right $ VProp $ ValueVector 1
    SelectPos1 _ _ -> liftM2 VPropPair (unpack s) (Right PropVector)
    SelectPos1L _ _ -> liftM2 VPropPair (unpack s) (Right PropVector)
    R1 -> 
      case s of
        VPropPair s1 _ -> Right $ VProp s1
        VPropTriple s1 _ _ -> Right $ VProp s1
        _ -> Left "Input of R1 is not a tuple"
    R2 -> 
      case s of
        VPropPair _ s2 -> Right $ VProp s2
        VPropTriple _ s2 _ -> Right $ VProp s2
        _ -> Left "Input of R2 is not a tuple"
    R3 -> 
      case s of
        VPropTriple s3 _ _ -> Right $ VProp s3
        _ -> Left "Input of R3 is not a tuple"
    ProjectRename _ -> Right $ VProp RenameVector
    ProjectPayload valProjs -> Right $ VProp $ ValueVector $ length valProjs
    ProjectAdmin _ -> VProp <$> unpack s
    SelectExpr _ -> VProp <$> unpack s
    Only -> undefined
    Singleton -> undefined
    CompExpr1L _ -> Right $ VProp $ ValueVector 1
    VecAggr g as -> Right $ VProp $ ValueVector (length g + length as)
  
reqValVectors :: VectorProp VectorType 
                 -> VectorProp VectorType 
                 -> (Int -> Int -> VectorProp VectorType)
                 -> String 
                 -> Either String (VectorProp VectorType)
reqValVectors (VProp (ValueVector w1)) (VProp (ValueVector w2)) f _ =
  Right $ f w1 w2
reqValVectors _ _ _ e =
  Left $ "Inputs of " ++ e ++ " are not ValueVectors"
      
inferVectorTypeBinOp :: VectorProp VectorType -> VectorProp VectorType -> BinOp -> Either String (VectorProp VectorType)
inferVectorTypeBinOp s1 s2 op = 
  case op of
    GroupBy -> 
      case (s1, s2) of
        (VProp t1@(ValueVector _), VProp t2@(ValueVector _)) -> Right $ VPropTriple t1 t2 PropVector
        _                                                    -> Left "Input of GroupBy is not a value vector"
    SortWith -> undefined
    LengthSeg -> return $ VProp $ ValueVector 1
    DistPrim -> liftM2 VPropPair (unpack s1) (Right PropVector)
    DistDesc -> liftM2 VPropPair (unpack s1) (Right PropVector)
    DistLift -> liftM2 VPropPair (unpack s1) (Right PropVector)
    PropRename -> Right s2
    PropFilter -> liftM2 VPropPair (unpack s2) (Right RenameVector)
    PropReorder -> liftM2 VPropPair (unpack s2) (Right PropVector)
    Append -> 
      case (s1, s2) of
        (VProp (ValueVector w1), VProp (ValueVector w2)) | w1 == w2 -> 
          Right $ VPropTriple (ValueVector w1) RenameVector RenameVector
        (VProp (ValueVector w1), VProp (ValueVector w2)) -> 
          Left $ "Inputs of Append do not have the same width " ++ (show w1) ++ " " ++ (show w2)
        v -> 
          Left $ "Input of Append is not a ValueVector " ++ (show v)

    RestrictVec -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    CompExpr2 _ -> Right $ VProp $ AtomicVector 1
    CompExpr2L _ -> Right $ VProp $ ValueVector 1
    VecSumL -> Right $ VProp $ ValueVector 1
    VecAvgL -> Right $ VProp $ ValueVector 1
    SelectPos _ -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    SelectPosL _ -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    PairA -> reqValVectors s1 s2 (\w1 w2 -> VProp $ AtomicVector $ w1 + w2) "PairA"
    -- PairL -> reqValVectors s1 s2 (\w1 w2 -> VProp $ AtomicVector $ w1 + w2) "PairL"
    PairL ->
      case (s1, s2) of
        (VProp (ValueVector w1), VProp (ValueVector w2)) -> Right $ VProp $ ValueVector $ w1 + w2
        _                                                -> Left "Inputs of PairL are not ValueVectors"
    ZipL -> reqValVectors s1 s2 (\w1 w2 -> VPropTriple (ValueVector $ w1 + w2) RenameVector RenameVector) "ZipL"
    CartProduct -> reqValVectors s1 s2 (\w1 w2 -> VPropTriple (ValueVector $ w1 + w2) PropVector PropVector) "CartProduct"
    -- FIXME check that the join predicate is compatible with the input schemas.
    ThetaJoin    _ -> reqValVectors s1 s2 (\w1 w2 -> let t = ValueVector (w1 + w2) in VPropPair t t) "ThetaJoin"

inferVectorTypeTerOp :: VectorProp VectorType -> VectorProp VectorType -> VectorProp VectorType -> TerOp -> Either String (VectorProp VectorType)
inferVectorTypeTerOp _ s2 s3 op = 
  case op of
    CombineVec -> 
      case (s2, s3) of
        (VProp (ValueVector w1), VProp (ValueVector w2)) | w1 == w2 -> 
          Right $ VPropTriple (ValueVector w1) RenameVector RenameVector
        (VProp (ValueVector _), VProp (ValueVector _))              -> 
          Left $ "Inputs of CombineVec do not have the same width"
        _                                                           -> 
          Left $ "Inputs of CombineVec are not ValueVectors/DescrVectors " ++ (show (s2, s3))
