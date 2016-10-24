-- FIXME remove once top-down properties are re-enabled
{-# OPTIONS_GHC -w #-}

module Database.DSH.SL.Opt.Properties.TopDown
    ( inferTopDownProperties
    ) where

import           Control.Monad.State
import           Text.Printf

import qualified Data.IntMap                               as M

import qualified Database.Algebra.Dag                      as D
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.SL.Lang
import           Database.DSH.SL.Opt.Properties.Types

vPropSeed :: TopDownProps
vPropSeed = TDProps

vPropPairSeed :: TopDownProps
vPropPairSeed = TDProps

vPropTripleSeed :: TopDownProps
vPropTripleSeed = TDProps

seed :: SLOp r e -> TopDownProps
seed (NullaryOp _) = vPropSeed
seed (UnOp op _)   =
    case op of
        WinFun _         -> vPropSeed
        Reverse          -> vPropPairSeed
        Unique           -> vPropSeed
        UnboxKey         -> vPropSeed
        Segment          -> vPropSeed
        Unsegment        -> vPropSeed
        Select     _     -> vPropPairSeed
        Sort _           -> vPropPairSeed
        Group _          -> vPropTripleSeed
        Project      _   -> vPropSeed
        GroupAggr (_, _) -> vPropSeed
        R1               -> vPropSeed
        R2               -> vPropSeed
        R3               -> vPropSeed
        Number           -> vPropSeed

seed (BinOp op _ _) =
    case op of
        Append          -> vPropTripleSeed
        Zip             -> vPropTripleSeed
        ReplicateNest   -> vPropPairSeed
        ReplicateScalar -> vPropPairSeed
        AppKey          -> vPropPairSeed
        AppSort         -> vPropPairSeed
        AppFilter       -> vPropPairSeed
        AppRep          -> vPropPairSeed
        UnboxSng        -> vPropPairSeed
        Fold _          -> vPropSeed
        Align           -> vPropSeed
        CartProduct     -> vPropTripleSeed
        ThetaJoin _     -> vPropTripleSeed
        SemiJoin _      -> vPropPairSeed
        AntiJoin _      -> vPropPairSeed
        NestJoin _      -> vPropTripleSeed
        GroupJoin _     -> vPropSeed
        ReplicateVector -> vPropPairSeed

seed (TerOp op _ _ _) =
    case op of
        Combine -> vPropTripleSeed


type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> error "TopDown.lookupProps"

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: BottomUpProps
          -> TopDownProps
          -> TopDownProps
          -> UnOp r e
          -> Either String TopDownProps
inferUnOp childBUProps ownProps cp op = do
    return $ TDProps

inferBinOp :: BottomUpProps
           -> BottomUpProps
           -> TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> BinOp e
           -> Either String (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op = do
    return (TDProps, TDProps)

inferTerOp :: TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> TerOp
           -> Either String (TopDownProps, TopDownProps, TopDownProps)
inferTerOp ownProps cp1 cp2 cp3 op = do
    return (TDProps, TDProps, TDProps)

inferChildProperties :: (Ord r, Ord e, Show r, Show e)
                     => NodeMap BottomUpProps
                     -> D.AlgebraDag (SLOp r e)
                     -> AlgNode
                     -> State InferenceState ()
inferChildProperties buPropMap d n = do
    ownProps <- lookupProps n
    case D.operator n d of
        NullaryOp _ -> return ()
        UnOp op c -> do
            cp <- lookupProps c
            let buProps = lookupUnsafe buPropMap "TopDown.infer" c
            let cp' = checkError n [cp] d $ inferUnOp buProps ownProps cp op
            replaceProps c cp'
        BinOp op c1 c2 -> do
            cp1 <- lookupProps c1
            cp2 <- lookupProps c2
            let buProps1 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
                buProps2 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c2
            let (cp1', cp2') = checkError n [cp1, cp2] d
                               $ inferBinOp buProps1 buProps2 ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> do
          cp1 <- lookupProps c1
          cp2 <- lookupProps c2
          cp3 <- lookupProps c3
          let (cp1', cp2', cp3') = checkError n [cp1, cp2, cp3] d
                                   $ inferTerOp ownProps cp1 cp2 cp3 op
          replaceProps c1 cp1'
          replaceProps c2 cp2'
          replaceProps c3 cp3'

checkError :: AlgNode -> [TopDownProps] -> D.AlgebraDag (SLOp r e) -> Either String p -> p
checkError n childProps d (Left msg) =
    let completeMsg   = printf "Inference failed at node %d\n%s\n%s"
                                n msg (show childProps)
    in error completeMsg
checkError _ _ _ (Right props) = props

-- | Infer properties during a top-down traversal.
inferTopDownProperties :: (Ord r, Ord e, Show r, Show e)
                       => NodeMap BottomUpProps
                       -> [AlgNode]
                       -> D.AlgebraDag (SLOp r e)
                       -> NodeMap TopDownProps
inferTopDownProperties buPropMap topOrderedNodes d = execState action initialMap
  where
    action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes
    initialMap = M.map seed $ D.nodeMap d
