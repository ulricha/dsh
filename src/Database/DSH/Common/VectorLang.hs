{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds      #-}

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

-- | Payload expressions for segment vectors.
--
-- 'VectorExpr' expresses scalar computations on vector payloads, in contrast to
-- non-scalar computations (list operations) which are handled at the
-- vector/segment level.
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

-- | *Flat* payload expressions for segment vectors.
--
-- This type expresses scalar payload computations on vectors with flat records
-- of scalar values.
data FlatExpr = FBinApp L.ScalarBinOp FlatExpr FlatExpr
              | FUnApp L.ScalarUnOp FlatExpr
              | FInputElem TupleIndex
              | FConstant L.ScalarVal
              | FIf FlatExpr FlatExpr FlatExpr
              deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''FlatExpr)

-- | Construction of a flat payload tuple.
newtype FlatTuple = FT [FlatExpr] deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''FlatTuple)

data AggrFun e = AggrSum ScalarType e
               | AggrMin e
               | AggrMax e
               | AggrAvg e
               | AggrAll e
               | AggrAny e
               | AggrCount
               | AggrCountDistinct e
               deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''AggrFun)

instance Functor AggrFun where
    fmap f (AggrMax e)           = AggrMax $ f e
    fmap f (AggrSum t e)         = AggrSum t $ f e
    fmap f (AggrMin e)           = AggrMin $ f e
    fmap f (AggrAvg e)           = AggrAvg $ f e
    fmap f (AggrAny e)           = AggrAny $ f e
    fmap f (AggrAll e)           = AggrAll $ f e
    fmap _ AggrCount             = AggrCount
    fmap f (AggrCountDistinct e) = AggrCountDistinct $ f e

data WinFun e = WinSum e
              | WinMin e
              | WinMax e
              | WinAvg e
              | WinAll e
              | WinAny e
              | WinFirstValue e
              | WinCount
              deriving (Eq, Ord, Show)

instance Functor WinFun where
    fmap f (WinMax e)        = WinMax $ f e
    fmap f (WinSum e)        = WinSum $ f e
    fmap f (WinMin e)        = WinMin $ f e
    fmap f (WinAvg e)        = WinAvg $ f e
    fmap f (WinAny e)        = WinAny $ f e
    fmap f (WinAll e)        = WinAll $ f e
    fmap f (WinFirstValue e) = WinFirstValue $ f e
    fmap _ WinCount          = WinCount

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
--
-- This type corresponds directly to the element type of a list, with nested
-- list type constructors replaced by the index type.
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
simplify :: VectorExpr -> VectorExpr
simplify (VBinApp o e1 e2)                     =
    VBinApp o (simplify e1) (simplify e2)
simplify (VUnApp o e)                          =
    VUnApp o (simplify e)
simplify VInput                                =
    VInput
simplify (VTupElem i (VMkTuple es))            =
    case safeIndex i es of
        Just e  -> simplify e
        Nothing -> $impossible
simplify (VTupElem i e)                        =
    VTupElem i (simplify e)
simplify (VMkTuple es)                         =
    VMkTuple $ map simplify es
simplify (VConstant v)                         =
    VConstant v
simplify (VIf (VConstant (L.BoolV True)) t _)  =
    simplify t
simplify (VIf (VConstant (L.BoolV False)) _ e) =
    simplify e
simplify (VIf c t e)                           =
   VIf (simplify c) (simplify t) (simplify e)
simplify VIndex                                =
    VIndex

partialEval :: VectorExpr -> VectorExpr
partialEval e = if e == e' then e else partialEval e'
  where
    e' = simplify e

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

instance Pretty FlatExpr where
    pretty = renderFlatExpr

instance Pretty FlatTuple where
    pretty = renderFlatTuple

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

renderFlatTuple :: FlatTuple -> Doc
renderFlatTuple (FT es) = renderRecord $ map renderFlatExpr es

renderFlatExpr :: FlatExpr -> Doc
renderFlatExpr (FBinApp op e1 e2) = parenthizeF e1 <+> text (pp op) <+> parenthizeF e2
renderFlatExpr (FUnApp op e)      = text (pp op) <+> parens (renderFlatExpr e)
renderFlatExpr (FConstant val)    = pretty val
renderFlatExpr (FInputElem i)     = text "x" <> dot <> (int $ tupleIndex i)
renderFlatExpr (FIf c t e)        = text "if"
                                    <+> renderFlatExpr c
                                    <+> text "then"
                                    <+> renderFlatExpr t
                                    <+> text "else"
                                    <+> renderFlatExpr e

parenthizeF :: FlatExpr -> Doc
parenthizeF e@(FConstant _) = renderFlatExpr e
parenthizeF e@FBinApp{}     = parens $ renderFlatExpr e
parenthizeF e@FUnApp{}      = parens $ renderFlatExpr e
parenthizeF e@FIf{}         = renderFlatExpr e
parenthizeF e@FInputElem{}  = renderFlatExpr e

type Ordish r e = (Ord r, Ord e, Show r, Show e)
