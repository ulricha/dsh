{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

-- | This module provides an abstraction over flat relational backends
-- w.r.t. to query execution and result value construction.
module Database.DSH.Execute.Backend where

import           Text.Printf
import qualified Data.IntMap                     as IM
import qualified Data.DList as D
import           Data.List              

import           Database.DSH.Impossible
import           Database.DSH.Frontend.Internals
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Execute.TH

-- | An abstract backend on which flat queries can be executed.
class Backend c where
    data BackendRow c
    data BackendCode c

    execFlatQuery :: c -> BackendCode c -> IO [BackendRow c]

-- | Abstraction over result rows for a specific backend.
class Row r where
    -- | The type of single attribute values
    data Scalar r

    -- | Look up an attribute in the row
    col       :: String -> r -> (Scalar r)

    -- | Convert an attribute value to a segment descriptor value
    descrVal  :: Scalar r -> Int

    -- | Convert an attribute value to a value term
    scalarVal :: Scalar r -> Type a -> Exp a

------------------------------------------------------------------------------
-- Different kinds of layouts that contain results in various forms

-- Generate the definition for the 'TabTuple' type
$(mkTabTupleType 16)

-- | Row layout with nesting data in the form of raw tabular results
data TabLayout a where
    TCol   :: Type a -> String -> TabLayout a
    TNest  :: (Reify a, Backend c, Row (BackendRow c)) => Type [a] -> [BackendRow c] -> TabLayout a -> TabLayout [a]
    TTuple :: TabTuple a -> TabLayout a

-- Generate the definition for the 'SegTuple' type
$(mkSegTupleType 16)

-- | A map from segment descriptor to list value expressions
type SegMap a = IM.IntMap (Exp a)

-- | Row layout with nesting data in the form of segment maps
data SegLayout a where
    SCol   :: Type a -> String -> SegLayout a
    SNest  :: Reify a => Type [a] -> SegMap [a] -> SegLayout [a]
    STuple :: SegTuple a -> SegLayout a

execQueryBundle :: (Backend c, Row (BackendRow c)) => c -> Shape (BackendCode c) -> Type a -> IO (Exp a)
execQueryBundle conn shape ty = 
    case (shape, ty) of
        (VShape q lyt, ListT ety) -> do
            tab  <- execFlatQuery conn q
            tlyt <- execNested conn lyt ety
            return $ fromVector tab tlyt
        (SShape q lyt, _) -> do
            tab  <- execFlatQuery conn q
            tlyt <- execNested conn lyt ty
            return $ fromPrim tab tlyt
        _ -> $impossible

-- | Traverse the layout and execute all subqueries for nested vectors
execNested :: (Backend c, Row (BackendRow c)) => c -> Layout (BackendCode c) -> Type a -> IO (TabLayout a)
execNested conn lyt ty =
    case (lyt, ty) of
        (LCol i, t)             -> return $ TCol t (itemCol i)
        (LNest q clyt, ListT t) -> do
            tab   <- execFlatQuery conn q
            clyt' <- execNested conn clyt t
            return $ TNest ty tab clyt'
        (LTuple lyts, TupleT tupTy) -> let execTuple = $(mkExecTuple 16)
                                       in execTuple lyts tupTy
        (_, _) -> error $ printf "Type does not match query structure: %s"

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

fromVector :: (Reify a, Row r) => [r] -> TabLayout a -> Exp [a]
fromVector tab tlyt =
    let slyt = segmentLayout tlyt
    in ListE $ D.toList $ foldl' (vecIter slyt) D.empty tab

vecIter :: Row r => SegLayout a -> D.DList (Exp a) -> r -> D.DList (Exp a)
vecIter slyt vals row = 
    let val = constructVal slyt row
    in D.snoc vals val

fromPrim :: Row r => [r] -> TabLayout a -> Exp a
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
                       , currVec :: D.DList (Exp a)
                       }

-- | Construct a segment map from a segmented vector
fromSegVector :: (Reify a, Row r) => [r] -> TabLayout a -> SegMap [a]
fromSegVector tab tlyt =
    let slyt = segmentLayout tlyt
        initialAcc = SegAcc { currSeg = 0, segMap = IM.empty, currVec = D.empty }
        finalAcc = foldl' (segIter slyt) initialAcc tab
    in IM.insert (currSeg finalAcc) (ListE $ D.toList $ currVec finalAcc) (segMap finalAcc)

-- | Fold iterator that constructs a map from segment descriptor to
-- the list value that is represented by that segment
segIter :: (Reify a, Row r) => SegLayout a -> SegAcc a -> r -> SegAcc a
segIter lyt acc row = 
    let val   = constructVal lyt row
        descr = descrCol row
    in if descr == currSeg acc
       then acc { currVec = D.snoc (currVec acc) val }
       else acc { currSeg = descr
                , segMap  = IM.insert (currSeg acc) (ListE $ D.toList $ currVec acc) (segMap acc)
                , currVec = D.singleton val
                }

------------------------------------------------------------------------------
-- Construct values from table rows    

-- | Construct a value from a vector row according to the given layout
constructVal :: Row r => SegLayout a -> r -> Exp a
constructVal lyt row =
    case lyt of
        STuple stup       -> let constructTuple = $(mkConstructTuple 16) 
                             in constructTuple stup row
        SNest _ segmap    -> let pos = posCol row
                              in case IM.lookup pos segmap of
                                  Just v  -> v
                                  Nothing -> ListE []
        SCol ty c         -> scalarVal (col c row) ty
