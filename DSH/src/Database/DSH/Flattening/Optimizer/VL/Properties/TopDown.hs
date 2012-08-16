module Optimizer.VL.Properties.TopDown(inferTopDownProperties, renderTopDownProps) where

import Control.Monad.State
  
import Text.PrettyPrint

import qualified Data.Map as M
import qualified Data.Set as S

import Database.Algebra.Aux
import Database.Algebra.Dag.Common
import Database.Algebra.Dag
import Database.Algebra.VL.Data

import Optimizer.VL.Properties.Types
  
instance Show TopDownProps where
    show props = render $ renderTopDownProps props

seedProps :: TopDownProps
seedProps = TDProps {
    reqType = Just 0
}

type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> return seedProps

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: TopDownProps -> TopDownProps -> UnOp -> TopDownProps
inferUnOp ownProps cp op =
    let childICols = inferReqTypeUnOp (reqType ownProps) (reqType cp) op
    in TDProps {
        reqType = childICols
        }

inferBinOp :: TopDownProps 
              -> TopDownProps 
              -> BottomUpProps 
              -> TopDownProps 
              -> BottomUpProps 
              -> BinOp 
              -> (TopDownProps, TopDownProps)
inferBinOp ownProps cp1 cpBU1 cp2 cpBU2 op =
    let vt = vectorTypeProp cpBU1
        vt2 = vectorTypeProp cpBU2
        ownType = reqType ownProps
        childType1 = reqType cp1
        childType2 = reqType cp2
        (childType1', childType2') = inferReqTypeBinOp ownType childType1 vt childType2 vt2 op
        cp1' = TDProps { reqType = childType1' }
        cp2' = TDProps { reqType = childType2' }
    in (cp1', cp2')

inferTerOp :: TopDownProps 
              -> TopDownProps 
              -> BottomUpProps 
              -> TopDownProps 
              -> BottomUpProps 
              -> BinOp 
              -> (TopDownProps, TopDownProps)
inferTerOp ownProps cp1 cpBU1 cp2 cpBU2 cp3 cpBU3 op =
    let vt = vectorTypeProp cpBU1
        vt2 = vectorTypeProp cpBU2
        vt3 = vectorTypeProp cpBU3
        ownType = reqType ownProps
        childType1 = reqType cp1
        childType2 = reqType cp2
        childType3 = reqType cp3
        (childType1', childType2', childType3') = inferReqTypeTerOp ownType childType1 vt childType2 vt2 childType3 vt3 op
        cp1' = TDProps { reqType = childType1' }
        cp2' = TDProps { reqType = childType2' }
        cp3' = TDProps { reqType = childType3' }
    in (cp1', cp2', cp3')

inferChildProperties :: NodeMap BottomUpProps -> AlgebraDag VL -> AlgNode -> State InferenceState ()
inferChildProperties buPropMap d n = do
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
            let cpBU1 = lookupUnsafe buPropMap "foo" c1 
                cpBU2 = lookupUnsafe buPropMap "bar" c2 
                (cp1', cp2') = inferBinOp ownProps cp1 cpBU1 cp2 cpBU2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> do
          cp1 <- lookupProps c1
          cp2 <- lookupProps c2
          cp3 <- lookupProps c3
          let cpBU1 = lookupUnsafe buPropMap "foo" c1
              cpBU2 = lookupUnsafe buPropMap "foo" c2
              cpBU3 = lookupUnsafe buPropMap "foo" c3
              (cp1', cp2', cp3') = inferTerOp ownProps cp1 cpBU1 cp2 cpBU2 cp3 cpBU3 op
          replaceProps c1 cp1'
          replaceProps c2 cp2'
          replaceProps c3 cp3'
    
rootProps :: NodeMap BottomUpProps -> AlgNode -> TopDownProps
rootProps buPropMap rootNode = TDProps { reqType = icols }
    where cols = map fst $ vectorTypeProp $ lookupUnsafe buPropMap "schema" rootNode
          icols = S.fromList cols
            
-- | Infer properties during a top-down traversal.
inferTopDownProperties :: NodeMap BottomUpProps -> [AlgNode] -> AlgebraDag VL -> NodeMap TopDownProps
inferTopDownProperties buPropMap topOrderedNodes d = execState action initialMap 
    where action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes
          initialMap = foldr (\r m -> M.insert r (rootProps buPropMap r) m) M.empty (rootNodes d)
          
-- | Rendering function for top-down inferred properties.
renderTopDownProps :: TopDownProps -> Doc
renderTopDownProps props = text "icols" <> colon <+> (renderProp $ reqType props)

