{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Common.VectorLang where

import Text.Printf
import           Control.Monad.Reader
import           Control.Monad.Except
import           Data.Aeson.TH
import qualified Data.Foldable                  as F
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.List.NonEmpty             as N
import           Data.Semigroup                 hiding (First)
import qualified Data.Sequence                  as S
import           Text.PrettyPrint.ANSI.Leijen   hiding ((<$>), (<>))
import qualified Text.PrettyPrint.ANSI.Leijen   as P

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty     hiding (join)
import           Database.DSH.Common.Type

--------------------------------------------------------------------------------
-- Payload values

data VecVal = VVTuple [VecVal]
            | VVScalar L.ScalarVal
            | VTIndex
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''VecVal)

instance Pretty VecVal where
    pretty VTIndex      = text "Idx"
    pretty (VVTuple vs) = tupled $ map pretty vs
    pretty (VVScalar v) = pretty v

--------------------------------------------------------------------------------
-- Scalar expressions and aggregate functions

-- | Payload expressions for segment vectors.
--
-- 'TExpr' expresses scalar computations on vector payloads, in contrast to
-- non-scalar computations (list operations) which are handled at the
-- vector/segment level.
data TExpr = TBinApp L.ScalarBinOp TExpr TExpr
           | TUnApp L.ScalarUnOp TExpr
           | TInput
           | TTupElem TupleIndex TExpr
           | TMkTuple (NonEmpty TExpr)
           | TConstant L.ScalarVal
           | TIf TExpr TExpr TExpr
           | TIndex
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TExpr)

valExpr :: VecVal -> TExpr
valExpr (VVTuple (v:vs)) = TMkTuple $ valExpr v :| map valExpr vs
valExpr (VVTuple [])     = $impossible
valExpr (VVScalar v)     = TConstant v
valExpr VTIndex          = TIndex

-- | *Flat* payload expressions for segment vectors.
--
-- This type expresses scalar payload computations on vectors with flat records
-- of scalar values.
data RExpr = RBinApp L.ScalarBinOp RExpr RExpr
           | RUnApp L.ScalarUnOp RExpr
           | RInputElem TupleIndex
           | RConstant L.ScalarVal
           | RIf RExpr RExpr RExpr
           deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''RExpr)

-- | Construction of a flat payload row.
newtype VRow = VR { unVR :: NonEmpty RExpr } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''VRow)

sngRow :: RExpr -> VRow
sngRow = VR . pure

instance Semigroup VRow where
    r1 <> r2 = VR $ unVR r1 <> unVR r2

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
scalarExpr :: L.ScalarExpr -> TExpr
scalarExpr (L.JIf e1 e2 e3)     = TIf (scalarExpr e1) (scalarExpr e2) (scalarExpr e3)
scalarExpr (L.JBinOp op e1 e2)  = TBinApp op (scalarExpr e1) (scalarExpr e2)
scalarExpr (L.JUnOp op e)       = TUnApp op (scalarExpr e)
scalarExpr (L.JTupElem i e)     = TTupElem i (scalarExpr e)
scalarExpr (L.JLit _ v)         = TConstant $ scalarVal v
scalarExpr (L.JInput _)         = TInput

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
data PType = PTupleT !(NonEmpty PType)
           | PScalarT !ScalarType
           | PIndexT
           deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''PType)

instance Pretty PType where
    pretty PIndexT      = text "Idx"
    pretty (PTupleT vs) = prettyTupTy $ map pretty $ N.toList vs
    pretty (PScalarT v) = pretty v

--------------------------------------------------------------------------------
-- Rewrite Utilities

-- | 'mergeExpr e1 e2' inlines 'e1' into 'e2'.
mergeExpr :: TExpr -> TExpr -> TExpr
mergeExpr inp (TBinApp o e1 e2) = TBinApp o (mergeExpr inp e1) (mergeExpr inp e2)
mergeExpr inp (TUnApp o e)      = TUnApp o (mergeExpr inp e)
mergeExpr inp TInput            = inp
mergeExpr inp (TTupElem i e)    = TTupElem i (mergeExpr inp e)
mergeExpr inp (TMkTuple es)     = TMkTuple $ fmap (mergeExpr inp) es
mergeExpr _   (TConstant v)     = TConstant v
mergeExpr inp (TIf c t e)       = TIf (mergeExpr inp c)
                                      (mergeExpr inp t)
                                      (mergeExpr inp e)
mergeExpr _   TIndex            = TIndex

-- | Construct a pair where the first component is an expression applied to the
-- first component of the input pair. This rewrite is used whenever projections
-- are pulled through a tuplifying operator.
--
-- (e[x.1/x], x.2)
appExprFst :: TExpr -> TExpr
appExprFst e = TMkTuple [ mergeExpr (TTupElem First TInput) e
                        , TTupElem (Next First) TInput
                        ]

-- | Construct a pair where the second component is an expression applied to the
-- second component of the input pair. This rewrite is used whenever projections
-- are pulled through a tuplifying operator.
--
-- (x.1, e[x.2/x])
appExprSnd :: TExpr -> TExpr
appExprSnd e = TMkTuple [ TTupElem First TInput
                        , mergeExpr (TTupElem (Next First) TInput) e
                        ]

-- | Partially evaluate scalar vector expressions. This covers:
--
-- * 'if' conditionals with constant conditions
-- * Tuple selectors on tuple constructors
simplify :: TExpr -> TExpr
simplify (TBinApp o e1 e2)                     =
    TBinApp o (simplify e1) (simplify e2)
simplify (TUnApp o e)                          =
    TUnApp o (simplify e)
simplify TInput                                =
    TInput
simplify (TTupElem i (TMkTuple es))            =
    case safeIndexN i es of
        Just e  -> simplify e
        Nothing -> error (printf "simplify %s (%s)" (show $ tupleIndex i) (pp $ TMkTuple es))
simplify (TTupElem i e)                        =
    TTupElem i (simplify e)
simplify (TMkTuple es)                         =
    TMkTuple $ fmap simplify es
simplify (TConstant v)                         =
    TConstant v
simplify (TIf (TConstant (L.BoolV True)) t _)  =
    simplify t
simplify (TIf (TConstant (L.BoolV False)) _ e) =
    simplify e
simplify (TIf c t e)                           =
   TIf (simplify c) (simplify t) (simplify e)
simplify TIndex                                =
    TIndex

partialEval :: TExpr -> TExpr
partialEval e = if e == e' then e else partialEval e'
  where
    e' = simplify e

inlineJoinPredLeft :: TExpr -> L.JoinPredicate TExpr -> L.JoinPredicate TExpr
inlineJoinPredLeft e (L.JoinPred conjs) = L.JoinPred $ fmap inlineLeft conjs
  where
    inlineLeft (L.JoinConjunct le op re) = L.JoinConjunct (mergeExpr e le) op re

inlineJoinPredRight :: TExpr -> L.JoinPredicate TExpr -> L.JoinPredicate TExpr
inlineJoinPredRight e (L.JoinPred conjs) = L.JoinPred $ fmap inlineRight conjs
  where
    inlineRight (L.JoinConjunct le op re) = L.JoinConjunct le op (mergeExpr e re)

-- | Returns 'True' iff only the tuple component of the input determined by the
-- predicate is accessed.
idxOnly :: (TupleIndex -> Bool) -> TExpr -> Bool
idxOnly p (TBinApp _ e1 e2)   = idxOnly p e1 && idxOnly p e2
idxOnly p (TUnApp _ e)        = idxOnly p e
idxOnly p (TTupElem i TInput) = p i
idxOnly _ TInput              = False
idxOnly p (TTupElem _ e)      = idxOnly p e
idxOnly p (TMkTuple es)       = all (idxOnly p) es
idxOnly _   (TConstant _)     = True
idxOnly p (TIf c t e)         = all (idxOnly p) (c:t:e:[])
idxOnly _   TIndex            = True

--------------------------------------------------------------------------------
-- Pretty Printing

instance Pretty TExpr where
    pretty = renderExpr

instance Pretty RExpr where
    pretty = renderRExpr

instance Pretty VRow where
    pretty = renderVRow

renderExpr :: TExpr -> Doc
renderExpr (TBinApp op e1 e2) = parenthize1 e1 <+> text (pp op) <+> parenthize1 e2
renderExpr (TUnApp op e)      = text (pp op) <+> parens (renderExpr e)
renderExpr (TConstant val)    = pretty val
renderExpr TInput             = text "x"
renderExpr (TMkTuple es)      = prettyTupConst $ N.toList $ fmap renderExpr es
renderExpr (TTupElem i e)     = renderExpr e P.<> dot P.<> (int $ tupleIndex i)
renderExpr TIndex             = text "Idx"
renderExpr (TIf c t e)        = text "if"
                                 <+> renderExpr c
                                 <+> text "then"
                                 <+> renderExpr t
                                 <+> text "else"
                                 <+> renderExpr e

parenthize1 :: TExpr -> Doc
parenthize1 e@(TConstant _) = renderExpr e
parenthize1 e@TBinApp{}     = parens $ renderExpr e
parenthize1 e@TUnApp{}      = parens $ renderExpr e
parenthize1 e@TIf{}         = renderExpr e
parenthize1 TIndex          = renderExpr TIndex
parenthize1 TInput          = renderExpr TInput
parenthize1 e@TMkTuple{}    = renderExpr e
parenthize1 e@TTupElem{}    = renderExpr e

renderVRow :: VRow -> Doc
renderVRow (VR es) = prettyTupConst $ map renderRExpr $ N.toList es

renderRExpr :: RExpr -> Doc
renderRExpr (RBinApp op e1 e2) = parenthizeF e1 <+> text (pp op) <+> parenthizeF e2
renderRExpr (RUnApp op e)      = text (pp op) <+> parens (renderRExpr e)
renderRExpr (RConstant val)    = pretty val
renderRExpr (RInputElem i)     = text "x" P.<> dot P.<> (int $ tupleIndex i)
renderRExpr (RIf c t e)        = text "if"
                                    <+> renderRExpr c
                                    <+> text "then"
                                    <+> renderRExpr t
                                    <+> text "else"
                                    <+> renderRExpr e

parenthizeF :: RExpr -> Doc
parenthizeF e@(RConstant _) = renderRExpr e
parenthizeF e@RBinApp{}     = parens $ renderRExpr e
parenthizeF e@RUnApp{}      = parens $ renderRExpr e
parenthizeF e@RIf{}         = renderRExpr e
parenthizeF e@RInputElem{}  = renderRExpr e

instance Pretty e => Pretty (AggrFun e) where
    pretty (AggrSum t c)         = prettyFun (text "sum" P.<> char '_' P.<> pretty t) [pretty c]
    pretty (AggrMin c)           = prettyFun (text "min") [pretty c]
    pretty (AggrMax c)           = prettyFun (text "max") [pretty c]
    pretty (AggrAvg c)           = prettyFun (text "avg") [pretty c]
    pretty (AggrAny c)           = prettyFun (text "any") [pretty c]
    pretty (AggrAll c)           = prettyFun (text "all") [pretty c]
    pretty AggrCount             = prettyFun (text "count") []
    pretty (AggrCountDistinct c) = prettyFun (text "countDistinct") [pretty c]

instance Pretty e => Pretty (WinFun e) where
    pretty (WinSum c)        = prettyFun (text "sum") [pretty c]
    pretty (WinMin c)        = prettyFun (text "min") [pretty c]
    pretty (WinMax c)        = prettyFun (text "max") [pretty c]
    pretty (WinAvg c)        = prettyFun (text "avg") [pretty c]
    pretty (WinAny c)        = prettyFun (text "any") [pretty c]
    pretty (WinAll c)        = prettyFun (text "all") [pretty c]
    pretty (WinFirstValue c) = prettyFun (text "first_value") [pretty c]
    pretty WinCount          = prettyFun (text "count") []

instance Pretty FrameSpec where
    pretty FAllPreceding   = text "allprec"
    pretty (FNPreceding n) = int n P.<+> text "prec"

instance Pretty VecSegs where
    pretty (UnitSeg seg) = pretty seg
    pretty (Segs segs)   = vcat $ map pretty $ F.toList segs

instance Pretty a => Pretty (S.Seq a) where
    pretty s = list $ map pretty $ F.toList s

--------------------------------------------------------------------------------

type Ordish r e = (Ord r, Ord e, Show r, Show e)

--------------------------------------------------------------------------------
-- Type inference and checking for tuple expressions

data TypedTExpr = TE TExpr PType

instance Pretty TypedTExpr where
    pretty (TE e ty) = pretty e P.<> char ':' P.<> pretty ty

tupElemTyErr :: TypedTExpr -> TupleIndex -> String
tupElemTyErr e i =
    if length te > 60
    then printf "tExpTy:\n(%s).%d" te (tupleIndex i)
    else printf "tExpTy: (%s).%d" te (tupleIndex i)
  where
    te = pp e

condTyErr :: TypedTExpr -> TypedTExpr -> TypedTExpr -> String
condTyErr e1 e2 e3 = printf "tExpTy: if %s then %s else %s" (pp e1) (pp e2) (pp e3)

unOpTyErr :: L.ScalarUnOp -> TypedTExpr -> String
unOpTyErr op e = printf "tExpTy: %s(%s)" (pp op) (pp e)

binOpTyErr :: L.ScalarBinOp -> TypedTExpr -> TypedTExpr -> String
binOpTyErr op e1 e2 = printf "tExpTy: (%s) %s (%s)" (pp e1) (pp op) (pp e2)

aggFunTyErr :: AggrFun TypedTExpr -> String
aggFunTyErr op = printf "tExpTy: %s" (pp op)

winFunTyErr :: WinFun TypedTExpr -> String
winFunTyErr op = printf "tExpTy: %s" (pp op)

conjTyErr :: L.JoinConjunct TypedTExpr -> String
conjTyErr c = printf "predTy: (%s) %s (%s)" (pp $ L.jcLeft c) (pp $ L.jcOp c) (pp $ L.jcRight c)

tExpTy :: (MonadError String m, MonadReader (Maybe PType) m) => TExpr -> m PType
tExpTy TIndex             = pure PIndexT
tExpTy (TConstant c)      = pure $ PScalarT $ L.litScalarTy c
tExpTy TInput             = do
    mTy <- ask
    case mTy of
        Just ty -> pure ty
        Nothing -> throwError "tExpTy: TInput with empty env"
tExpTy (TTupElem i e)     = do
    ty <- tExpTy e
    case ty of
        PTupleT ts ->
            case safeIndexN i ts of
                Just t  -> pure t
                Nothing -> throwError $ tupElemTyErr (TE e ty) i
        _          -> throwError $ tupElemTyErr (TE e ty) i
tExpTy (TMkTuple es)      = PTupleT <$> sequenceA (tExpTy <$> es)
tExpTy (TIf e1 e2 e3)     = do
    t1 <- tExpTy e1
    t2 <- tExpTy e2
    t3 <- tExpTy e3
    case t1 of
        PScalarT BoolT -> do
            if t2 == t3
               then pure t2
               else throwError $ condTyErr (TE e1 t1) (TE e2 t2) (TE e3 t3)
        _              -> throwError $ condTyErr (TE e1 t1) (TE e2 t2) (TE e3 t3)

tExpTy (TBinApp op e1 e2) = do
    ty1 <- tExpTy e1
    ty2 <- tExpTy e2
    case (ty1, ty2) of
        (PScalarT sty1, PScalarT sty2) -> PScalarT <$> L.inferBinOpScalar sty1 sty2 op
        _                              -> throwError $ binOpTyErr op (TE e1 ty1) (TE e2 ty2)
tExpTy (TUnApp op e)      = do
    ty <- tExpTy e
    case ty of
        PScalarT sty -> PScalarT <$> L.inferUnOpScalar sty op
        _            -> throwError $ unOpTyErr op (TE e ty)

tAggrTy :: (MonadError String m, MonadReader (Maybe PType) m) => AggrFun TExpr -> m PType
tAggrTy (AggrSum _ e)         = tExpTy e
tAggrTy (AggrMin e)           = tExpTy e
tAggrTy (AggrMax e)           = tExpTy e
tAggrTy (AggrAvg e)           = tExpTy e
tAggrTy (AggrAll e)           = do
    ty <- tExpTy e
    if ty == PScalarT BoolT
       then pure ty
       else throwError $ aggFunTyErr $ AggrAll (TE e ty)
tAggrTy (AggrAny e)   = do
    ty <- tExpTy e
    if ty == PScalarT BoolT
       then pure ty
       else throwError $ aggFunTyErr $ AggrAny (TE e ty)
tAggrTy AggrCount             = pure $ PScalarT IntT
tAggrTy (AggrCountDistinct e) = do
    _ <- tExpTy e
    pure $ PScalarT IntT

tWinTy :: (MonadError String m, MonadReader (Maybe PType) m) => WinFun TExpr -> m PType
tWinTy (WinSum e)         = tExpTy e
tWinTy (WinMin e)           = tExpTy e
tWinTy (WinMax e)           = tExpTy e
tWinTy (WinAvg e)           = tExpTy e
tWinTy (WinAll e)           = do
    ty <- tExpTy e
    if ty == PScalarT BoolT
       then pure ty
       else throwError $ winFunTyErr $ WinAll (TE e ty)
tWinTy (WinAny e)   = do
    ty <- tExpTy e
    if ty == PScalarT BoolT
       then pure ty
       else throwError $ winFunTyErr $ WinAny (TE e ty)
tWinTy WinCount             = pure $ PScalarT IntT
tWinTy (WinFirstValue e)    = tExpTy e

conjTy :: MonadError String m => PType -> PType -> L.JoinConjunct TExpr -> m ()
conjTy ty1 ty2 c = do
    leftTy  <- runReaderT (tExpTy (L.jcLeft c)) (Just ty1)
    rightTy <- runReaderT (tExpTy (L.jcRight c)) (Just ty2)
    if leftTy == rightTy
       then pure ()
       else throwError $ conjTyErr $ c { L.jcLeft = TE (L.jcLeft c) leftTy
                                       , L.jcRight = TE (L.jcRight c) rightTy
                                       }

predTy :: MonadError String m => PType -> PType -> L.JoinPredicate TExpr -> m ()
predTy ty1 ty2 p = void $ sequenceA $ fmap (conjTy ty1 ty2) (L.jpConjuncts p)


--------------------------------------------------------------------------------
-- Patterns for tuple expressions

pattern TFirst :: TExpr -> TExpr
pattern TFirst e = TTupElem First e

pattern TSecond :: TExpr -> TExpr
pattern TSecond e = TTupElem (Next First) e

pattern TThird :: TExpr -> TExpr
pattern TThird e = TTupElem (Next (Next First)) e

pattern TFourth :: TExpr -> TExpr
pattern TFourth e = TTupElem (Next (Next (Next First))) e

pattern TInpFirst :: TExpr
pattern TInpFirst = TFirst TInput

pattern TInpSecond :: TExpr
pattern TInpSecond = TSecond TInput

pattern TEq :: TExpr -> TExpr -> TExpr
pattern TEq e1 e2 = TBinApp (L.SBRelOp L.Eq) e1 e2

tPair :: TExpr -> TExpr -> TExpr
tPair e1 e2 = TMkTuple (e1 :| [e2])
