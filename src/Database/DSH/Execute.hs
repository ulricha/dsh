{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Execute
    ( execQueryBundle
    ) where

import           Control.Applicative
import           Control.Monad.State
import qualified Data.DList                      as D
import qualified Data.IntMap                     as IM
import           Data.List
import           Text.Printf

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend
import           Database.DSH.Execute.TH
import qualified Database.DSH.Frontend.Internals as F
import           Database.DSH.Impossible

------------------------------------------------------------------------------
-- Different kinds of layouts that contain results in various forms

-- Generate the definition for the 'TabTuple' type
$(mkTabTupleType 16)

-- | Row layout with nesting data in the form of raw tabular results
data TabLayout a where
    TCol   :: F.Type a -> String -> TabLayout a
    TNest  :: (F.Reify a, Backend c, Row (BackendRow c))
           => F.Type [a] -> [BackendRow c] -> TabLayout a -> TabLayout [a]
    TTuple :: TabTuple a -> TabLayout a


-- Generate the definition for the 'SegTuple' type
$(mkSegTupleType 16)

-- | A map from segment descriptor to list value expressions
type SegMap a = IM.IntMap (F.Exp a)

-- | Row layout with nesting data in the form of segment maps
data SegLayout a where
    SCol   :: F.Type a -> String -> SegLayout a
    SNest  :: F.Reify a => F.Type [a] -> SegMap [a] -> SegLayout [a]
    STuple :: SegTuple a -> SegLayout a

--------------------------------------------------------------------------------
-- Turn layouts into layouts with explicit column position indexes

data PosLayout q = PCol Int
                 | PNest q (PosLayout q)
                 | PTuple [PosLayout q]

-- | Annotate every column reference with its column index in a flat
-- column layout.
columnIndexes :: Layout q -> PosLayout q
columnIndexes lyt = evalState (numberCols lyt) 1

numberCols :: Layout q -> State Int (PosLayout q)
numberCols LCol          = currentCol >>= \i -> return (PCol i)
numberCols (LTuple lyts) = PTuple <$> mapM numberCols lyts
numberCols (LNest q lyt) = PNest q <$> posBracket (numberCols lyt)

currentCol :: State Int Int
currentCol = do
    i <- get
    put $ i + 1
    return i

posBracket :: State Int (PosLayout q) -> State Int (PosLayout q)
posBracket ma = do
    c <- get
    put 1
    a <- ma
    put c
    return a

--------------------------------------------------------------------------------
-- Execute flat queries and construct result values

execQueryBundle :: (Backend c, Row (BackendRow c)) => c -> Shape (BackendCode c) -> F.Type a -> IO (F.Exp a)
execQueryBundle conn shape ty =
    case (shape, ty) of
        (VShape q lyt, F.ListT ety) -> do
            tab  <- execFlatQuery conn q
            tlyt <- execNested conn (columnIndexes lyt) ety
            return $ fromVector tab tlyt
        (SShape q lyt, _) -> do
            tab  <- execFlatQuery conn q
            tlyt <- execNested conn (columnIndexes lyt) ty
            return $ fromPrim tab tlyt
        _ -> $impossible

-- | Traverse the layout and execute all subqueries for nested vectors
execNested :: (Backend c, Row (BackendRow c)) => c -> PosLayout (BackendCode c) -> F.Type a -> IO (TabLayout a)
execNested conn lyt ty =
    case (lyt, ty) of
        (PCol i, t)                   -> return $ TCol t (itemCol i)
        (PNest q clyt, F.ListT t)     -> do
            tab   <- execFlatQuery conn q
            clyt' <- execNested conn clyt t
            return $ TNest ty tab clyt'
        (PTuple lyts, F.TupleT tupTy) -> let execTuple = $(mkExecTuple 16)
                                         in execTuple lyts tupTy
        (_, _)                        -> error $ printf "Type does not match query structure: %s" (pp ty)

------------------------------------------------------------------------------
-- Construct result value terms from raw tabular results

-- |
itemCol :: Int -> String
itemCol 1 = "item1"
itemCol 2 = "item2"
itemCol 3 = "item3"
itemCol 4 = "item4"
itemCol 5 = "item5"
itemCol 6 = "item6"
itemCol 7 = "item7"
itemCol 8 = "item8"
itemCol 9 = "item9"
itemCol 10 = "item10"
itemCol n = "item" ++ show n

posCol :: Row r => r -> Int
posCol row = descrVal $ col "pos" row

descrCol :: Row r => r -> Int
descrCol row = descrVal $ col "descr" row

fromVector :: (F.Reify a, Row r) => [r] -> TabLayout a -> F.Exp [a]
fromVector tab tlyt =
    let slyt = segmentLayout tlyt
    in F.ListE $ D.toList $ foldl' (vecIter slyt) D.empty tab

vecIter :: Row r => SegLayout a -> D.DList (F.Exp a) -> r -> D.DList (F.Exp a)
vecIter slyt vals row =
    let val = constructVal slyt row
    in D.snoc vals val

fromPrim :: Row r => [r] -> TabLayout a -> F.Exp a
fromPrim tab tlyt =
    let slyt = segmentLayout tlyt
    in case tab of
           [row] -> constructVal slyt row
           _     -> $impossible

------------------------------------------------------------------------------
-- Construct nested result values from segmented vectors

-- | Construct values for nested vectors in the layout.
segmentLayout :: TabLayout a -> SegLayout a
segmentLayout tlyt =
    case tlyt of
        TCol ty s            -> SCol ty s
        TNest ty tab clyt    -> SNest ty (fromSegVector tab clyt)
        TTuple tup           -> let segmentTuple = $(mkSegmentTupleFun 16)
                                in STuple $ segmentTuple tup

data SegAcc a = SegAcc { currSeg :: Int
                       , segMap  :: SegMap [a]
                       , currVec :: D.DList (F.Exp a)
                       }

-- | Construct a segment map from a segmented vector
fromSegVector :: (F.Reify a, Row r) => [r] -> TabLayout a -> SegMap [a]
fromSegVector tab tlyt =
    let slyt = segmentLayout tlyt
        initialAcc = SegAcc { currSeg = 0, segMap = IM.empty, currVec = D.empty }
        finalAcc = foldl' (segIter slyt) initialAcc tab
    in IM.insert (currSeg finalAcc) (F.ListE $ D.toList $ currVec finalAcc) (segMap finalAcc)

-- | Fold iterator that constructs a map from segment descriptor to
-- the list value that is represented by that segment
segIter :: (F.Reify a, Row r) => SegLayout a -> SegAcc a -> r -> SegAcc a
segIter lyt acc row =
    let val   = constructVal lyt row
        descr = descrCol row
    in if descr == currSeg acc
       then acc { currVec = D.snoc (currVec acc) val }
       else acc { currSeg = descr
                , segMap  = IM.insert (currSeg acc) (F.ListE $ D.toList $ currVec acc) (segMap acc)
                , currVec = D.singleton val
                }

------------------------------------------------------------------------------
-- Construct values from table rows

-- | Construct a value from a vector row according to the given layout
constructVal :: Row r => SegLayout a -> r -> F.Exp a
constructVal lyt row =
    case lyt of
        STuple stup       -> let constructTuple = $(mkConstructTuple 16)
                             in constructTuple stup row
        SNest _ segmap    -> let pos = posCol row
                              in case IM.lookup pos segmap of
                                  Just v  -> v
                                  Nothing -> F.ListE []
        SCol ty c         -> scalarVal (col c row) ty

--------------------------------------------------------------------------------

