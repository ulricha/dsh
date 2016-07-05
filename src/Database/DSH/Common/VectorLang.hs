{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Common.VectorLang where

import           Data.Aeson.TH
import           Data.Monoid
import qualified Data.Sequence                  as S

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
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

----------------------------------------------------------------------------------
-- Convert join expressions into regular SL/VSL expressions

pVal :: L.Val -> L.ScalarVal
pVal (L.ScalarV v) = v
pVal L.ListV{}     = error "VectorLang: Not a scalar value"
pVal L.TupleV{}    = error "VectorLang: Not a scalar value"

-- | Determine the horizontal relational schema width of a type
recordWidth :: Type -> Int
recordWidth t =
    case t of
        ScalarT _   -> 1
        TupleT ts   -> sum $ map recordWidth ts
        ListT _     -> 0

data ColExpr = Offset Int | Expr Expr

-- | If the child expressions are tuple operators which only give the
-- column offset, convert it into a proper expression first.
offsetExpr :: ColExpr -> Expr
offsetExpr (Offset o) = Column $ o + 1
offsetExpr (Expr e)   = e

addOffset :: Int -> ColExpr -> ColExpr
addOffset _ (Expr _)   = error "VectorLang: Expression in offset calculation"
addOffset i (Offset o) = Offset $ o + i

toSLjoinConjunct :: L.JoinConjunct L.ScalarExpr -> L.JoinConjunct Expr
toSLjoinConjunct (L.JoinConjunct e1 o e2) =
    L.JoinConjunct (scalarExpr e1) o (scalarExpr e2)

toSLJoinPred :: L.JoinPredicate L.ScalarExpr -> L.JoinPredicate Expr
toSLJoinPred (L.JoinPred cs) = L.JoinPred $ fmap toSLjoinConjunct cs

-- | Convert join expressions into SL expressions. The main challenge
-- here is to convert sequences of tuple accessors (fst/snd) into SL
-- column indices.
scalarExpr :: L.ScalarExpr -> Expr
scalarExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following:
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding SL expression
    aux :: L.ScalarExpr -> ColExpr
    -- FIXME SL joins should include join expressions!
    aux (L.JBinOp op e1 e2)  = Expr $ BinApp op
                                             (offsetExpr $ aux e1)
                                             (offsetExpr $ aux e2)
    aux (L.JUnOp op e)       = Expr $ UnApp op (offsetExpr $ aux e)
    aux (L.JTupElem i e)     =
        case typeOf e of
            -- Compute the record width of all preceding tuple elements in the type
            TupleT ts -> addOffset (sum $ map recordWidth $ take (tupleIndex i - 1) ts) (aux e)
            _         -> error "VectorLang: type mismatch (not a tuple type)"
    aux (L.JLit _ v)         = Expr $ Constant $ pVal v
    aux (L.JInput _)         = Offset 0

--------------------------------------------------------------------------------
-- Type conversion

typeToScalarType :: Type -> ScalarType
typeToScalarType ListT{}     = $impossible
typeToScalarType TupleT{}    = $impossible
typeToScalarType (ScalarT t) = t
