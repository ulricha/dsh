{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Common.VectorLang where

import           Data.Aeson.TH
import           Data.Monoid
import qualified Data.Sequence                  as S

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Type

--------------------------------------------------------------------------------
-- Scalar expressions and aggregate functions

-- | One-based reference to a payload column in a data vector.
type DBCol = Int

data Expr = BinApp L.ScalarBinOp Expr Expr
          | UnApp L.ScalarUnOp Expr
          | Column DBCol
          | Constant L.ScalarVal
          | If Expr Expr Expr
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Expr)

data AggrFun = AggrSum ScalarType Expr
             | AggrMin Expr
             | AggrMax Expr
             | AggrAvg Expr
             | AggrAll Expr
             | AggrAny Expr
             | AggrCount
             | AggrCountDistinct Expr
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''AggrFun)

data WinFun = WinSum Expr
            | WinMin Expr
            | WinMax Expr
            | WinAvg Expr
            | WinAll Expr
            | WinAny Expr
            | WinFirstValue Expr
            | WinCount
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''WinFun)

-- | Specification of a window for the window aggregate operator.
data FrameSpec = -- | All elements up to and including the current
                 -- element are in the window
                 FAllPreceding
                 -- | All n preceding elements up to and including the
                 -- current one.
               | FNPreceding Int
                deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''FrameSpec)

--------------------------------------------------------------------------------
-- Segments for vector literals.

type Column = S.Seq L.ScalarVal

data Segment = Seg
    { segCols :: [Column]
    , segLen  :: !Int
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Segment)

newtype SegFrame = SegFrame { frameLen :: Int } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''SegFrame)

data Segments = UnitSeg [Column]
              | Segs [Segment]
              deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Segments)

-- | Extract complete columns from segments.
vectorCols :: [ScalarType] -> Segments -> [Column]
vectorCols tys (UnitSeg [])   = map (const S.empty) tys
vectorCols _   (UnitSeg cols) = cols
vectorCols tys (Segs segs)    = flattenSegments tys segs

flattenSegments :: [ScalarType] -> [Segment] -> [Column]
flattenSegments tys []   = map (const S.empty) tys
flattenSegments tys segs = go (map (const S.empty) tys) segs
  where
    go cols (s:ss) = go (zipWith (<>) cols (segCols s)) ss
    go cols []     = cols
