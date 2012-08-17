module Optimizer.VL.Properties.TopDown(inferTopDownProperties) where

import Control.Monad.State
  
import Text.PrettyPrint

import qualified Data.Map as M
import qualified Data.Set as S

import Database.Algebra.Aux
import Database.Algebra.Dag.Common
import Database.Algebra.Dag
import Database.Algebra.VL.Data

import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.ToDescr
  
toDescrSeed :: Maybe Bool
toDescrSeed = Nothing

vPropSeed :: TopDownProps
vPropSeed = TDProps { toDescrProp = VProp toDescrSeed }

vPropPairSeed :: TopDownProps
vPropPairSeed = TDProps { toDescrProp = VPropPair toDescrSeed toDescrSeed }

vPropTripleSeed :: TopDownProps
vPropTripleSeed = TDProps { toDescrProp = VPropTriple toDescrSeed toDescrSeed toDescrSeed }
                  
seed :: VL -> TopDownProps
seed (NullaryOp op) = vPropSeed
seed (UnOp op _) =
  case op of
    SelectPos1 _ _     -> vPropPairSeed
    SelectPos1L _ _    -> vPropPairSeed 
    ReverseA           -> vPropPairSeed
    ReverseL           -> vPropPairSeed
    Unique             -> vPropSeed
    UniqueL            -> vPropSeed
    NotPrim            -> vPropSeed
    NotVec             -> vPropSeed
    LengthA            -> vPropSeed
    DescToRename       -> vPropSeed
    ToDescr            -> vPropSeed
    Segment            -> vPropSeed
    VecSum _           -> vPropSeed
    VecMin             -> vPropSeed
    VecMinL            -> vPropSeed
    VecMax             -> vPropSeed
    VecMaxL            -> vPropSeed
    ProjectL _         -> vPropSeed
    ProjectA _         -> vPropSeed
    IntegerToDoubleA   -> vPropSeed
    IntegerToDoubleL   -> vPropSeed
    FalsePositions     -> vPropSeed
    SelectItem         -> vPropSeed
    ProjectRename _    -> vPropSeed
    ProjectAdmin _     -> vPropSeed
    ProjectPayload _   -> vPropSeed
    CompExpr1 _        -> vPropSeed
    R1                 -> vPropSeed
    R2                 -> vPropSeed
    R3                 -> vPropSeed

seed (BinOp op _ _) = 
  case op of
    GroupBy            -> vPropTripleSeed
    Append             -> vPropTripleSeed
    ZipL               -> vPropTripleSeed
    SortWith           -> vPropPairSeed
    DistPrim           -> vPropPairSeed
    DistDesc           -> vPropPairSeed
    DistLift           -> vPropPairSeed
    PropFilter         -> vPropPairSeed
    PropReorder        -> vPropPairSeed
    RestrictVec        -> vPropPairSeed
    SelectPos _        -> vPropPairSeed
    SelectPosL _       -> vPropPairSeed
    LengthSeg          -> vPropSeed
    PropRename         -> vPropSeed
    CompExpr2 _        -> vPropSeed
    CompExpr2L _       -> vPropSeed
    VecSumL            -> vPropSeed
    PairA              -> vPropSeed
    PairL              -> vPropSeed
    CartProductFlat    -> vPropSeed
    ThetaJoinFlat _    -> vPropSeed
    
seed (TerOp op _ _ _) =
  case op of
    CombineVec -> vPropTripleSeed
    

type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> error "TopDown.lookupProps"

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: TopDownProps -> TopDownProps -> UnOp -> TopDownProps
inferUnOp ownProps cp op =
    TDProps { toDescrProp = inferToDescrUnOp (toDescrProp ownProps) (toDescrProp cp) op }

inferBinOp :: TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> BinOp 
              -> (TopDownProps, TopDownProps)
inferBinOp ownProps cp1 cp2 op =
  let (ctd1', ctd2') = inferToDescrBinOp (toDescrProp ownProps) (toDescrProp cp1) (toDescrProp cp2) op
      cp1' = TDProps { toDescrProp = ctd1' }
      cp2' = TDProps { toDescrProp = ctd2' }
  in (cp1', cp2')

inferTerOp :: TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> TerOp 
              -> (TopDownProps, TopDownProps, TopDownProps)
inferTerOp ownProps cp1 cp2 cp3 op =
  let (ctd1', ctd2', ctd3') = inferToDescrTerOp (toDescrProp ownProps) (toDescrProp cp1) (toDescrProp cp2) (toDescrProp cp3) op
      cp1' = TDProps { toDescrProp = ctd1' }
      cp2' = TDProps { toDescrProp = ctd2' }
      cp3' = TDProps { toDescrProp = ctd3' }
  in (cp1', cp2', cp3')

inferChildProperties :: AlgebraDag VL -> AlgNode -> State InferenceState ()
inferChildProperties d n = do
    ownProps <- lookupProps n
    case operator n d of
        NullaryOp _ -> return ()
        UnOp op c -> do
            cp <- lookupProps c
            let cp' = inferUnOp ownProps cp op
            replaceProps c cp'
        BinOp op c1 c2 -> do
            cp1 <- lookupProps c1
            cp2 <- lookupProps c2
            let (cp1', cp2') = inferBinOp ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> do
          cp1 <- lookupProps c1
          cp2 <- lookupProps c2
          cp3 <- lookupProps c3
          let (cp1', cp2', cp3') = inferTerOp ownProps cp1 cp2 cp3 op
          replaceProps c1 cp1'
          replaceProps c2 cp2'
          replaceProps c3 cp3'
    
-- | Infer properties during a top-down traversal.
inferTopDownProperties :: [AlgNode] -> AlgebraDag VL -> NodeMap TopDownProps
inferTopDownProperties topOrderedNodes d = execState action initialMap 
    where action = mapM_ (inferChildProperties d) topOrderedNodes
          initialMap = M.map seed $ nodeMap d
          
-- | Rendering function for top-down inferred properties.
renderTopDownProps :: TopDownProps -> Doc
renderTopDownProps props = text "toDescr" <> colon <+> (text $ show $ toDescrProp props)

