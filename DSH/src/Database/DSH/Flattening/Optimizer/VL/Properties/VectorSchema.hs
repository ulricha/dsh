-- FIXME introduce consistency checks for schema inference

module Optimizer.VL.Properties.VectorSchema where

import Optimizer.VL.Properties.Types
  
import Database.Algebra.VL.Data

inferSchemaNullOp :: NullOp -> Either String VectorSchema
inferSchemaNullOp op =
  case op of
    SingletonDescr              -> Right $ DescrVector
    ConstructLiteralTable t _   -> Right $ ValueVector $ length t
    ConstructLiteralValue t _   -> Right $ ValueVector $ length t
    TableRef              _ cs _ -> Right $ ValueVector $ length cs
                    
inferSchemaUnOp :: VectorSchema -> UnOp -> Either String VectorSchema
inferSchemaUnOp s op = 
  case op of
    Unique -> Right s
    UniqueL -> Right s
    NotPrim -> Right $ AtomicVector 1
    NotVec -> Right $ ValueVector 1
    LengthA -> Right $ AtomicVector 1
    DescToRename -> Right $ RenameVector
    ToDescr -> Right DescrVector
    Segment -> Right s
    VecSum _ -> Right $ AtomicVector 1
    VecMin -> Right $ AtomicVector 1
    VecMinL -> Right $ ValueVector 1
    VecMax -> Right $ AtomicVector 1
    VecMaxL -> Right $ ValueVector 1
    ProjectL ps -> Right $ ValueVector $ length ps
    ProjectA ps -> Right $ AtomicVector $ length ps
    IntegerToDoubleA -> Right $ AtomicVector 1
    IntegerToDoubleL -> Right $ ValueVector 1
    ReverseA -> Right $ VectorPair s PropVector
    ReverseL -> Right $ VectorPair s PropVector
    FalsePositions -> Right $ ValueVector 1
    R1 -> 
      case s of
        VectorPair s1 _ -> Right s1
        VectorTriple s1 _ _ -> Right s1
        _ -> Left "Input of R1 is not a tuple"
    R2 -> 
      case s of
        VectorPair _ s2 -> Right s2
        VectorTriple _ s2 _ -> Right s2
        _ -> Left "Input of R2 is not a tuple"
    R3 -> 
      case s of
        VectorTriple s3 _ _ -> Right s3
        _ -> Left "Input of R3 is not a tuple"
    ProjectRename _ -> Right RenameVector
    ProjectValue (_, _, valProjs) -> Right $ ValueVector $ length valProjs
    SelectItem -> Right s
    Only -> undefined
    Singleton -> undefined
    VecBinOpSingle _ -> Right $ ValueVector 1
      
inferSchemaBinOp :: VectorSchema -> VectorSchema -> BinOp -> Either String VectorSchema
inferSchemaBinOp s1 s2 op = 
  case op of
    GroupBy -> 
      case s1 of
        ValueVector w1 -> Right $ VectorTriple DescrVector (ValueVector w1) PropVector -- FIXME double-check
        _              -> Left "Input of GroupBy is not a value vector"
    SortWith -> undefined
    LengthSeg -> undefined
    DistPrim -> Right $ VectorPair s1 PropVector
    DistDesc -> Right $ VectorPair s1 PropVector
    DistLift -> Right $ VectorPair s1 PropVector
    PropRename -> Right s2
    PropFilter -> Right s2
    PropReorder -> Right s2
    Append -> 
      case (s1, s2) of
        (ValueVector w1, ValueVector w2) | w1 == w2 -> Right $ VectorTriple (ValueVector w1) RenameVector RenameVector
        (ValueVector w1, ValueVector w2)            -> Left "Inputs of Append do not have the same width"
        _                                           -> Left "Input of Append is not a ValueVector"

    RestrictVec -> Right $ VectorPair s1 RenameVector
    VecBinOp _ -> Right $ AtomicVector 1
    VecBinOpL _ -> Right $ ValueVector 1
    VecSumL -> Right $ ValueVector 1
    SelectPos _ -> Right $ VectorPair s1 RenameVector
    SelectPosL _ -> Right $ VectorPair s1 RenameVector
    PairA -> 
      case (s1, s2) of
        (ValueVector w1, ValueVector w2) -> Right $ AtomicVector $ w1 + w2
        _                                -> Left "Inputs of PairA are not ValueVectors"
    PairL ->
      case (s1, s2) of
        (ValueVector w1, ValueVector w2) -> Right $ ValueVector $ w1 + w2
        _                                -> Left "Inputs of PairL are not ValueVectors"
    ZipL -> 
      case (s1, s2) of
        (ValueVector w1, ValueVector w2) -> Right $ VectorTriple (ValueVector $ w1 + w2) RenameVector RenameVector
        _                                -> Left "Inputs of ZipL are not ValueVectors"
    CartProduct ->
      case (s1, s2) of
        (ValueVector w1, ValueVector w2) -> Right $ ValueVector $ w1 + w2
        _                                -> Left "Inputs of CartProduct are not ValueVectors"

inferSchemaTerOp :: VectorSchema -> VectorSchema -> VectorSchema -> TerOp -> Either String VectorSchema
inferSchemaTerOp s1 s2 s3 op = 
  case op of
    CombineVec -> 
      case (s2, s3) of
        (ValueVector w1, ValueVector w2) | w1 == w2 -> Right $ VectorTriple (ValueVector w1) RenameVector RenameVector
        (ValueVector _ , ValueVector _ )            -> Left $ "Inputs of CombineVec do not have the same width"
        _                                           -> Left $ "Inputs of CombineVec are not ValueVectors"
