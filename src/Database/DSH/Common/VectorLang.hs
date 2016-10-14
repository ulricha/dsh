{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Common.VectorLang where

import           Data.Aeson.TH
import qualified Data.Foldable                  as F
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.Sequence                  as S
import           Text.PrettyPrint.ANSI.Leijen   hiding ((<$>))

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type

--------------------------------------------------------------------------------
-- Payload values

data VecVal = VVTuple [VecVal]
            | VVScalar L.ScalarVal
            | VVIndex
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''VecVal)

instance Pretty VecVal where
    pretty VVIndex      = text "Idx"
    pretty (VVTuple vs) = tupled $ map pretty vs
    pretty (VVScalar v) = pretty v

--------------------------------------------------------------------------------
-- Scalar expressions and aggregate functions

data VectorExpr = VBinApp L.ScalarBinOp VectorExpr VectorExpr
                | VUnApp L.ScalarUnOp VectorExpr
                | VInput
                | VTupElem TupleIndex VectorExpr
                | VMkTuple [VectorExpr]
                | VConstant L.ScalarVal
                | VIf VectorExpr VectorExpr VectorExpr
                | VIndex
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''VectorExpr)

data AggrFun = AggrSum ScalarType VectorExpr
             | AggrMin VectorExpr
             | AggrMax VectorExpr
             | AggrAvg VectorExpr
             | AggrAll VectorExpr
             | AggrAny VectorExpr
             | AggrCount
             | AggrCountDistinct VectorExpr
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''AggrFun)

data WinFun = WinSum VectorExpr
            | WinMin VectorExpr
            | WinMax VectorExpr
            | WinAvg VectorExpr
            | WinAll VectorExpr
            | WinAny VectorExpr
            | WinFirstValue VectorExpr
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

type SegD = S.Seq VecVal

data VecSegs = UnitSeg SegD
             | Segs (S.Seq SegD)
              deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''VecSegs)

segmentData :: VecSegs -> SegD
segmentData (UnitSeg s) = s
segmentData (Segs ss)   = F.foldl' (S.><) S.empty ss

----------------------------------------------------------------------------------
-- Convert join expressions into regular SL/VSL expressions

scalarVal :: L.Val -> L.ScalarVal
scalarVal (L.ScalarV v) = v
scalarVal _             = $impossible

-- | Convert join expressions into SL expressions.
scalarExpr :: L.ScalarExpr -> VectorExpr
scalarExpr (L.JBinOp op e1 e2)  = VBinApp op (scalarExpr e1) (scalarExpr e2)
scalarExpr (L.JUnOp op e)       = VUnApp op (scalarExpr e)
scalarExpr (L.JTupElem i e)     = VTupElem i (scalarExpr e)
scalarExpr (L.JLit _ v)         = VConstant $ scalarVal v
scalarExpr (L.JInput _)         = VInput

--------------------------------------------------------------------------------
-- Type conversion

typeToScalarType :: Type -> ScalarType
typeToScalarType ListT{}     = $impossible
typeToScalarType TupleT{}    = $impossible
typeToScalarType (ScalarT t) = t

--------------------------------------------------------------------------------

-- | The type of vector payloads
data PType = PTupleT ![PType]
           | PScalarT !ScalarType
           | PIndexT
           deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''PType)

instance Pretty PType where
    pretty PIndexT      = text "Idx"
    pretty (PTupleT vs) = tupled $ map pretty vs
    pretty (PScalarT v) = pretty v

--------------------------------------------------------------------------------
-- Rewrite Utilities

-- | 'mergeExpr e1 e2' inlines 'e1' into 'e2'.
mergeExpr :: VectorExpr -> VectorExpr -> VectorExpr
mergeExpr inp (VBinApp o e1 e2) = VBinApp o (mergeExpr inp e1) (mergeExpr inp e2)
mergeExpr inp (VUnApp o e)      = VUnApp o (mergeExpr inp e)
mergeExpr inp VInput            = inp
mergeExpr inp (VTupElem i e)    = VTupElem i (mergeExpr inp e)
mergeExpr inp (VMkTuple es)     = VMkTuple $ map (mergeExpr inp) es
mergeExpr _   (VConstant v)     = VConstant v
mergeExpr inp (VIf c t e)       = VIf (mergeExpr inp c)
                                      (mergeExpr inp t)
                                      (mergeExpr inp e)
mergeExpr _   VIndex            = VIndex

-- | Construct a pair where the first component is an expression applied to the
-- first component of the input pair. This rewrite is used whenever projections
-- are pulled through a tuplifying operator.
--
-- (e[x.1/x], x.2)
appExprFst :: VectorExpr -> VectorExpr
appExprFst e = VMkTuple [ mergeExpr (VTupElem First VInput) e
                        , VTupElem (Next First) VInput
                        ]

-- | Construct a pair where the second component is an expression applied to the
-- second component of the input pair. This rewrite is used whenever projections
-- are pulled through a tuplifying operator.
--
-- (x.1, e[x.2/x])
appExprSnd :: VectorExpr -> VectorExpr
appExprSnd e = VMkTuple [ VTupElem First VInput
                        , mergeExpr (VTupElem (Next First) VInput) e
                        ]

-- | Returns the list element denoted by a tuple index.
safeIndex :: TupleIndex -> [a] -> Maybe a
safeIndex First    (x:_)  = Just x
safeIndex (Next i) (_:xs) = safeIndex i xs
safeIndex _        _      = Nothing

-- | Partially evaluate scalar vector expressions. This covers:
--
-- * 'if' conditionals with constant conditions
-- * Tuple selectors on tuple constructors
partialEval :: VectorExpr -> VectorExpr
partialEval (VBinApp o e1 e2)                     =
    VBinApp o (partialEval e1) (partialEval e2)
partialEval (VUnApp o e)                          =
    VUnApp o (partialEval e)
partialEval VInput                                =
    VInput
partialEval (VTupElem i (VMkTuple es))            =
    case safeIndex i es of
        Just e  -> partialEval e
        Nothing -> $impossible
partialEval (VTupElem i e)                        =
    VTupElem i (partialEval e)
partialEval (VMkTuple es)                         =
    VMkTuple $ map partialEval es
partialEval (VConstant v)                         =
    VConstant v
partialEval (VIf (VConstant (L.BoolV True)) t _)  =
    partialEval t
partialEval (VIf (VConstant (L.BoolV False)) _ e) =
    partialEval e
partialEval (VIf c t e)                           =
   VIf (partialEval c) (partialEval t) (partialEval e)
partialEval VIndex                                =
    VIndex

-- | Transform the argument expression of an aggregate.
mapAggrFun :: (VectorExpr -> VectorExpr) -> AggrFun -> AggrFun
mapAggrFun f (AggrMax e)           = AggrMax $ f e
mapAggrFun f (AggrSum t e)         = AggrSum t $ f e
mapAggrFun f (AggrMin e)           = AggrMin $ f e
mapAggrFun f (AggrAvg e)           = AggrAvg $ f e
mapAggrFun f (AggrAny e)           = AggrAny $ f e
mapAggrFun f (AggrAll e)           = AggrAll $ f e
mapAggrFun _ AggrCount             = AggrCount
mapAggrFun f (AggrCountDistinct e) = AggrCountDistinct $ f e

-- | Transform the argument expression of a window aggregate.
mapWinFun :: (VectorExpr -> VectorExpr) -> WinFun -> WinFun
mapWinFun f (WinMax e)        = WinMax $ f e
mapWinFun f (WinSum e)        = WinSum $ f e
mapWinFun f (WinMin e)        = WinMin $ f e
mapWinFun f (WinAvg e)        = WinAvg $ f e
mapWinFun f (WinAny e)        = WinAny $ f e
mapWinFun f (WinAll e)        = WinAll $ f e
mapWinFun f (WinFirstValue e) = WinFirstValue $ f e
mapWinFun _ WinCount          = WinCount

inlineJoinPredLeft :: VectorExpr -> L.JoinPredicate VectorExpr -> L.JoinPredicate VectorExpr
inlineJoinPredLeft e (L.JoinPred conjs) = L.JoinPred $ fmap inlineLeft conjs
  where
    inlineLeft (L.JoinConjunct le op re) = L.JoinConjunct (mergeExpr e le) op re

inlineJoinPredRight :: VectorExpr -> L.JoinPredicate VectorExpr -> L.JoinPredicate VectorExpr
inlineJoinPredRight e (L.JoinPred conjs) = L.JoinPred $ fmap inlineRight conjs
  where
    inlineRight (L.JoinConjunct le op re) = L.JoinConjunct le op (mergeExpr e re)

-- | Returns 'True' iff only the tuple component of the input determined by the
-- predicate is accessed.
idxOnly :: (TupleIndex -> Bool) -> VectorExpr -> Bool
idxOnly p (VBinApp _ e1 e2)   = idxOnly p e1 && idxOnly p e2
idxOnly p (VUnApp _ e)        = idxOnly p e
idxOnly p (VTupElem i VInput) = p i
idxOnly _ VInput              = False
idxOnly p (VTupElem _ e)      = idxOnly p e
idxOnly p (VMkTuple es)       = all (idxOnly p) es
idxOnly _   (VConstant _)     = True
idxOnly p (VIf c t e)         = all (idxOnly p) [c, t, e]
idxOnly _   VIndex            = True

--------------------------------------------------------------------------------
-- Common patterns

pattern SingleJoinPred :: t -> L.BinRelOp -> t -> L.JoinPredicate t
pattern SingleJoinPred e1 op e2 = L.JoinPred ((L.JoinConjunct e1 op e2) :| [])

pattern DoubleJoinPred :: t -> L.BinRelOp -> t -> t -> L.BinRelOp -> t -> L.JoinPredicate t
pattern DoubleJoinPred e11 op1 e12 e21 op2 e22 = L.JoinPred ((L.JoinConjunct e11 op1 e12)
                                                             :|
                                                             [L.JoinConjunct e21 op2 e22])
pattern VAddExpr :: VectorExpr -> VectorExpr -> VectorExpr
pattern VAddExpr e1 e2 = VBinApp (L.SBNumOp L.Add) e1 e2

pattern VSubExpr :: VectorExpr -> VectorExpr -> VectorExpr
pattern VSubExpr e1 e2 = VBinApp (L.SBNumOp L.Sub) e1 e2

--------------------------------------------------------------------------------
-- Pretty Printing

instance Pretty VectorExpr where
    pretty = renderExpr

renderRecord :: [Doc] -> Doc
renderRecord = encloseSep (char '<') (char '>') comma


renderExpr :: VectorExpr -> Doc
renderExpr (VBinApp op e1 e2) = parenthize1 e1 <+> text (pp op) <+> parenthize1 e2
renderExpr (VUnApp op e)      = text (pp op) <+> parens (renderExpr e)
renderExpr (VConstant val)    = pretty val
renderExpr VInput             = text "x"
renderExpr (VMkTuple es)      = renderRecord $ map renderExpr es
renderExpr (VTupElem i e)     = renderExpr e <> dot <> (int $ tupleIndex i)
renderExpr VIndex             = text "Idx"
renderExpr (VIf c t e)        = text "if"
                                 <+> renderExpr c
                                 <+> text "then"
                                 <+> renderExpr t
                                 <+> text "else"
                                 <+> renderExpr e

parenthize1 :: VectorExpr -> Doc
parenthize1 e@(VConstant _) = renderExpr e
parenthize1 e@VBinApp{}     = parens $ renderExpr e
parenthize1 e@VUnApp{}      = parens $ renderExpr e
parenthize1 e@VIf{}         = renderExpr e
parenthize1 VIndex          = renderExpr VIndex
parenthize1 VInput          = renderExpr VInput
parenthize1 e@VMkTuple{}    = renderExpr e
parenthize1 e@VTupElem{}    = renderExpr e
