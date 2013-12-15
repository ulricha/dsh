{-# LANGUAGE TemplateHaskell #-}        

module Database.DSH.Optimizer.TA.Properties.TopDown where

import           Debug.Trace

import           Control.Monad.State

import qualified Data.IntMap as M
import qualified Data.Set.Monad as S

import           Database.Algebra.Dag.Common
import           Database.Algebra.Dag
import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Impossible

import           Database.DSH.Optimizer.Common.Aux
import           Database.DSH.Optimizer.TA.Properties.Types
import           Database.DSH.Optimizer.TA.Properties.ICols


seed :: TopDownProps
seed = TDProps { icolsProp = S.empty }

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
    TDProps { icolsProp = inferIColsUnOp (icolsProp ownProps) (icolsProp cp) op }

inferBinOp :: BottomUpProps 
           -> BottomUpProps
           -> TopDownProps 
           -> TopDownProps 
           -> TopDownProps 
           -> BinOp 
           -> (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op =
  let (crc1', crc2') = inferIColsBinOp (icolsProp ownProps) 
                                       (icolsProp cp1) 
                                       (colsProp childBUProps1)
                                       (icolsProp cp2)
                                       (colsProp childBUProps2)
                                       op
      cp1' = TDProps { icolsProp = crc1' }
      cp2' = TDProps { icolsProp = crc2' }
  in (cp1', cp2')

inferChildProperties :: NodeMap BottomUpProps -> AlgebraDag PFAlgebra -> AlgNode -> State InferenceState ()
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
            let buProps1 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
                buProps2 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c2
            let (cp1', cp2') = inferBinOp buProps1 buProps2 ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> $impossible
        
seedTopNodes :: AlgebraDag PFAlgebra -> NodeMap BottomUpProps -> NodeMap TopDownProps -> NodeMap TopDownProps
seedTopNodes dag buPropMap tdPropMap = foldr seed tdPropMap (rootNodes dag)
  where
    seed :: AlgNode -> NodeMap TopDownProps -> NodeMap TopDownProps
    seed n propMap = 
        case M.lookup n buPropMap of
            Just buProps -> M.insert n (TDProps { icolsProp = colsProp buProps }) propMap
            Nothing      -> $impossible


-- | Infer properties during a top-down traversal.
inferTopDownProperties :: NodeMap BottomUpProps -> [AlgNode] -> AlgebraDag PFAlgebra -> NodeMap TopDownProps
inferTopDownProperties buPropMap topOrderedNodes d = let m = execState action initialMap 
                                                     in {- trace (show buPropMap) $ trace (show m) -} m
    where action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes
          initialMap = seedTopNodes d buPropMap $ M.map (const seed) $ nodeMap d
