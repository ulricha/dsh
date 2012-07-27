module Optimizer.VL.Properties.Descriptor where

import Data.Functor
import Control.Monad

import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.Common
  
unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.IndexSpace"

fromDBVIS :: IS -> Either String (DescrIS, PosIS)
fromDBVIS = undefined

fromDescrVecIS :: IS -> Either String (DescrIS, PosIS)
fromDescrVecIS = undefined
                 
fromRenameVecTrans :: IS -> Either String (SourceIS, TargetIS)
fromRenameVecTrans = undefined
    
inferIndexSpaceNullOp :: AlgNode -> NullOp -> Either String (VectorProp IS)
inferIndexSpaceNullOp q op =
  case op of
    SingletonDescr             -> undefined
    ConstructLiteralTable _ _  -> undefined
    ConstructLiteralValue _ _  -> undefined
    TableRef _ _ _             -> Right $ VProp $ DBVSpace (D $ DescrSeed q) (P $ PosSeed q)
  
inferIndexSpaceUnOp :: AlgNode -> VectorProp IS -> UnOp -> Either String (VectorProp IS)
inferIndexSpaceUnOp q is op =
  case op of
    ToDescr -> VProp <$> uncurry DescrVectorSpace <$> (fromDBVIS =<< unp is)

    DescToRename -> do
      (D d, P p) <- unp is >>= fromDescrVecIS
      return $ VProp $ RenameVectorTransform (S p) (T d)
    
    Segment -> do
      (_, (P p)) <- unp is >>= fromDBVIS
      return $ VProp $ DBVSpace (D p) (P p)
    
    SelectItem -> do
      (D d, P p) <- unp is >>= fromDBVIS
      return $ VProp $ DBVSpace (D $ SelectT d) (P $ SelectT p)
      
    VecBinOpSingle (op, col1, col2) -> do
      (D d, P p) <- unp is >>= fromDBVIS
      let pred = PredT $ Pred op col1 col2
      return $ VProp $ DBVSpace (D $ pred d) (P $ pred p)
  
    ProjectRename (pn, po) -> do
      (D d, P p) <- unp is >>= fromDBVIS
      let d' = case pn of
            STDescrCol -> d
            STPosCol   -> p
            STNumber   -> NumberT d
      let p' = case po of
            STDescrCol -> d
            STPosCol   -> p
            STNumber   -> NumberT p
            
      return $ VProp $ DBVSpace (D d') (P p')
      
    ProjectL _ -> do
      (d, p) <- unp is >>= fromDBVIS
      return $ VProp $ DBVSpace d p
  
    R1 -> 
      case is of
        VProp _           -> Left "Properties.IndexSpace: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case is of
        VProp _           -> Left "Properties.IndexSpace: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case is of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.IndexSpace: not a triple"
    
inferIndexSpaceBinOp :: AlgNode -> VectorProp IS -> VectorProp IS -> BinOp -> Either String (VectorProp IS)
inferIndexSpaceBinOp q is1 is2 op =
  case op of
    CartProduct -> do
      (D d, _) <- unp is1 >>= fromDBVIS
      return $ VProp $ DBVSpace (D d) (P $ PosSeed q)
      
    RestrictVec -> do
      (D d2, P p2) <- unp is1 >>= fromDBVIS
      return $ VProp $ DBVSpace (D $ SelectT d2) (P $ SelectT p2)
      
    PropRename -> do
      (_ , T t) <- unp is1 >>= fromRenameVecTrans
      (_, p) <- unp is2 >>= fromDBVIS
      return $ VProp $ DBVSpace (D t) p
      
    DistPrim -> do
      (d, _) <- unp is2 >>= fromDescrVecIS
      return $ VProp $ DBVSpace d (P $ PosSeed q)

    -- FIXME this is just a dummy
    GroupBy -> return $ VPropPair (DescrVectorSpace (D $ DescrSeed q) (P $ PosSeed q)) (DBVSpace (D $ DescrSeed q) (P $ PosSeed q))
    
    -- FIXME dummy
    SelectPosL _ -> return $ VProp (DBVSpace (D $ DescrSeed q) (P $ PosSeed q))

    -- FIXME dummy
    PropFilter -> return $ VProp (DBVSpace (D $ DescrSeed q) (P $ PosSeed q))
    
    -- FIXME dummy
    PairL -> return $ VProp (DBVSpace (D $ DescrSeed q) (P $ PosSeed q))

    _           -> undefined
    
inferIndexSpaceTerOp :: AlgNode -> IS -> IS -> IS -> TerOp -> IS
inferIndexSpaceTerOp q is1 is2 is3 op =
  case op of
    _ -> undefined
