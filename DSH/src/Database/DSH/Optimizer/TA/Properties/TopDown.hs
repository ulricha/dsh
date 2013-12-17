{-# LANGUAGE TemplateHaskell #-}        

module Database.DSH.Optimizer.TA.Properties.TopDown where

import           Debug.Trace

import           Control.Monad.State

import Data.List
import qualified Data.IntMap as M
import qualified Data.Set.Monad as S

import           Database.Algebra.Dag.Common
import           Database.Algebra.Dag
import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Impossible

import           Database.DSH.Optimizer.Common.Aux
import           Database.DSH.Optimizer.TA.Properties.Types
import           Database.DSH.Optimizer.TA.Properties.ICols
import           Database.DSH.Optimizer.TA.Properties.Use


seed :: TopDownProps
seed = TDProps { pICols = S.empty, pUse = S.empty }

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
    TDProps { pICols = inferIColsUnOp (pICols ownProps) (pICols cp) op 
            , pUse   = inferUseUnOp (pUse ownProps) (pUse cp) op }

inferBinOp :: BottomUpProps 
           -> BottomUpProps
           -> TopDownProps 
           -> TopDownProps 
           -> TopDownProps 
           -> BinOp 
           -> (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op =
  let (crc1', crc2') = inferIColsBinOp (pICols ownProps) 
                                       (pICols cp1) 
                                       (pCols childBUProps1)
                                       (pICols cp2)
                                       (pCols childBUProps2)
                                       op
      (urc1', urc2') = inferUseBinOp (pUse ownProps)
                                     (pUse cp1)
                                     (pUse cp2)
                                     (pCols childBUProps1)
                                     (pCols childBUProps2)
                                     op
      cp1' = TDProps { pICols = crc1', pUse = urc1' }
      cp2' = TDProps { pICols = crc2', pUse = urc2' }
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
seedTopNodes dag buPropMap tdPropMap = foldr seedNodes tdPropMap (rootNodes dag)
  where
    seedNodes :: AlgNode -> NodeMap TopDownProps -> NodeMap TopDownProps
    seedNodes n propMap = 
        case M.lookup n buPropMap of
            Just buProps -> let seedProps = TDProps { pICols = pCols buProps 
                            -- FIXME seeding Use with all columns
                            -- might be too much.  E.g. for flat
                            -- results, descriptor values are
                            -- certainly not needed. Maybe we should re-introduce
                            -- sth equiv. to the SERIALIZEREL operator.
                                                    , pUse   = pCols buProps
                                                    }
                            in M.insert n seedProps propMap
            Nothing      -> $impossible


-- | Infer properties during a top-down traversal.
inferAllProperties :: NodeMap BottomUpProps -> [AlgNode] -> AlgebraDag PFAlgebra -> NodeMap AllProps
inferAllProperties buPropMap topOrderedNodes d = let tdPropMap = execState action initialMap  
                                                 in case mergeProps buPropMap tdPropMap of
                                                        Just ps -> ps
                                                        Nothing -> $impossible
  where 
    action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes

    initialMap = seedTopNodes d buPropMap $ M.map (const seed) $ nodeMap d

    mergeProps :: NodeMap BottomUpProps -> NodeMap TopDownProps -> Maybe (NodeMap AllProps)
    mergeProps bum tdm = do
        let keys1 = M.keys bum
            keys2 = M.keys tdm
            keys  = keys1 `intersect` keys2
        guard $ length keys == length keys1 && length keys == length keys2
        
        let merge :: AlgNode -> Maybe (AlgNode, AllProps)
            merge n = do
                bup <- M.lookup n bum
                tdp <- M.lookup n tdm
                return (n, AllProps { td = tdp, bu = bup })

        merged <- mapM merge keys
        return $ M.fromList merged
        
            
