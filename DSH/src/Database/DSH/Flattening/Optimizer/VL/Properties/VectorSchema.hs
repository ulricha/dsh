-- FIXME introduce consistency checks for schema inference

module Optimizer.VL.Properties.VectorSchema where

import Data.Functor
import Control.Monad

import Optimizer.VL.Properties.Types
  
import Database.Algebra.VL.Data
  
{- Implement more checks: check the input types for correctness -}

schemaWidth :: VectorProp Schema -> Int
schemaWidth (VProp (ValueVector w)) = w
schemaWidth _                       = error "schemaWidth: non-ValueVector input"

inferSchemaNullOp :: NullOp -> Either String (VectorProp Schema)
inferSchemaNullOp op =
  case op of
    SingletonDescr              -> Right $ VProp $ DescrVector
    ConstructLiteralTable t _   -> Right $ VProp $ ValueVector $ length t
    ConstructLiteralValue t _   -> Right $ VProp $ ValueVector $ length t
    TableRef              _ cs _ -> Right $ VProp $ ValueVector $ length cs
  
unpack :: VectorProp Schema -> Either String Schema
unpack (VProp s) = Right s
unpack _         = Left "Input is not a single vector property" 

inferSchemaUnOp :: VectorProp Schema -> UnOp -> Either String (VectorProp Schema)
inferSchemaUnOp s op = 
  case op of
    Unique -> VProp <$> unpack s
    UniqueL -> VProp <$> unpack s
    NotPrim -> Right $ VProp $ AtomicVector 1
    NotVec -> Right $ VProp $ ValueVector 1
    LengthA -> Right $ VProp $ AtomicVector 1
    DescToRename -> Right $ VProp $ RenameVector
    ToDescr -> Right $ VProp $ DescrVector
    Segment -> VProp <$> unpack s
    VecSum _ -> Right $ VProp $ AtomicVector 1
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
    ProjectValue (_, _, valProjs) -> Right $ VProp $ ValueVector $ length valProjs
    SelectItem -> VProp <$> unpack s
    Only -> undefined
    Singleton -> undefined
    VecBinOpSingle _ -> Right $ VProp $ ValueVector 1
  
reqValVectors :: VectorProp Schema 
                 -> VectorProp Schema 
                 -> (Int -> Int -> VectorProp Schema)
                 -> String 
                 -> Either String (VectorProp Schema)
reqValVectors (VProp (ValueVector w1)) (VProp (ValueVector w2)) f _ =
  Right $ f w1 w2
reqValVectors _ _ _ e =
  Left $ "Inputs of " ++ e ++ " are not ValueVectors"
      
inferSchemaBinOp :: VectorProp Schema -> VectorProp Schema -> BinOp -> Either String (VectorProp Schema)
inferSchemaBinOp s1 s2 op = 
  case op of
    GroupBy -> 
      case s1 of
        VProp vv@(ValueVector _) -> Right $ VPropTriple DescrVector vv PropVector -- FIXME double-check
        _                        -> Left "Input of GroupBy is not a value vector"
    SortWith -> undefined
    LengthSeg -> undefined
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
        (VProp (ValueVector _), VProp (ValueVector _)) -> 
          Left "Inputs of Append do not have the same width"
        _ -> 
          Left "Input of Append is not a ValueVector"

    RestrictVec -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    VecBinOp _ -> Right $ VProp $ AtomicVector 1
    VecBinOpL _ -> Right $ VProp $ ValueVector 1
    VecSumL -> Right $ VProp $ ValueVector 1
    SelectPos _ -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    SelectPosL _ -> liftM2 VPropPair (unpack s1) (Right RenameVector)
    PairA -> reqValVectors s1 s2 (\w1 w2 -> VProp $ AtomicVector $ w1 + w2) "PairA"
    -- PairL -> reqValVectors s1 s2 (\w1 w2 -> VProp $ AtomicVector $ w1 + w2) "PairL"
    PairL ->
      case (s1, s2) of
        (VProp (ValueVector w1), VProp (ValueVector w2)) -> Right $ VProp $ ValueVector $ w1 + w2
        _                                                -> Right $ VProp $ ValueVector 0
        -- FIXME check disabled for now
        -- _                                -> Left "Inputs of PairL are not ValueVectors"
    ZipL -> reqValVectors s1 s2 (\w1 w2 -> VPropTriple (ValueVector $ w1 + w2) RenameVector RenameVector) "ZipL"
    CartProduct -> reqValVectors s1 s2 (\w1 w2 -> VProp $ ValueVector $ w1 + w2) "CartProduct"
    -- FIXME check that the join predicate is compatible with the input schemas.
    ThetaJoin _ -> reqValVectors s1 s2 (\w1 w2 -> VProp $ ValueVector $ w1 + w2) "ThetaJoin"

inferSchemaTerOp :: VectorProp Schema -> VectorProp Schema -> VectorProp Schema -> TerOp -> Either String (VectorProp Schema)
inferSchemaTerOp _ s2 s3 op = 
  case op of
    CombineVec -> 
      case (s2, s3) of
        (VProp (ValueVector w1), VProp (ValueVector w2)) | w1 == w2 -> 
          Right $ VPropTriple (ValueVector w1) RenameVector RenameVector
        (VProp (ValueVector _), VProp (ValueVector _)) ->
          Left $ "Inputs of CombineVec do not have the same width"
        _                                           -> 
          Left $ "Inputs of CombineVec are not ValueVectors"
