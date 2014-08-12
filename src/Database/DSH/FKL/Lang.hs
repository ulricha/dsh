{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.FKL.Lang where

import           Text.Printf

import qualified Database.DSH.Common.Lang   as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type   (Type, Typed, typeOf)

import           GHC.Generics               (Generic)

-- Signal wether a scalar operator is applied in its lifted or
-- unlifted form.
data Lifted a = Lifted a
              | NotLifted a
              deriving (Show, Eq, Generic)

-- | Data type expr represents flat kernel language.
data Expr = Table   Type String [L.Column] L.TableHints
          | PApp1   Type Prim1 Expr
          | PApp2   Type Prim2 Expr Expr
          | PApp3   Type Prim3 Expr Expr Expr
          | CloApp  Type Expr Expr
          | CloLApp Type Expr Expr
          | If      Type Expr Expr Expr
          | BinOp   Type (Lifted L.ScalarBinOp) Expr Expr
          | UnOp    Type (Lifted L.ScalarUnOp) Expr
          | Const   Type L.Val
          | Var     Type L.Ident
          | Clo     Type L.Ident [L.Ident] L.Ident Expr Expr -- When performing normal function application ignore the first value of the freeVars!!!
          | AClo    Type L.Ident [L.Ident] L.Ident Expr Expr
    deriving (Eq, Generic, Show)

data Prim1 = FLength Type
           | FLengthL Type
           | FConcat Type
           | FConcatL Type
           | FFst Type
           | FFstL Type
           | FSnd Type
           | FSndL Type
           | FSum Type
           | FSumL Type
           | FAvg Type
           | FAvgL Type
           | FMinimum Type
           | FMinimumL Type
           | FMaximum Type
           | FMaximumL Type
           | FThe Type
           | FTheL Type
           | FQuickConcat Type
           | FTail Type
           | FTailL Type
           | FReverse Type
           | FReverseL Type
           | FAnd Type
           | FAndL Type
           | FOr Type
           | FOrL Type
           | FInit Type
           | FInitL Type
           | FLast Type
           | FLastL Type
           | FNub Type
           | FNubL Type
           | FNumber Type
           | FNumberL Type
           | FTranspose Type
           | FTransposeL Type
           | FReshape Integer Type
           | FReshapeL Integer Type
    deriving (Eq, Generic)

instance Show Prim1 where
    show (FLength _)     = "length"
    show (FLengthL _)    = "lengthL"
    show (FConcatL _)    = "concatL"
    show (FFst _)        = "fst"
    show (FSnd _)        = "snd"
    show (FFstL _)       = "fstL"
    show (FSndL _)       = "sndL"
    show (FConcat _)     = "concat"
    show (FQuickConcat _) = "quickConcat"
    show (FSum _)        = "sum"
    show (FAvg _)        = "avg"
    show (FSumL _)       = "sumL"
    show (FAvgL _)       = "avgL"
    show (FThe _)        = "the"
    show (FTheL _)       = "theL"
    show (FMinimum _)    = "minimum"
    show (FMinimumL _)   = "minimumL"
    show (FMaximum _)    = "maximum"
    show (FMaximumL _)   = "maximumL"
    show (FTail _)       = "tail"
    show (FTailL _)      = "tailL"
    show (FReverse _)    = "reverse"
    show (FReverseL _)   = "reverseL"
    show (FAnd _)        = "and"
    show (FAndL _)       = "andL"
    show (FOr _)         = "or"
    show (FOrL _)        = "orL"
    show (FInit _)       = "init"
    show (FInitL _)      = "initL"
    show (FLast _)       = "last"
    show (FLastL _)      = "lastL"
    show (FNub _)        = "nub"
    show (FNubL _)       = "nubL"
    show (FNumber _)     = "number"
    show (FNumberL _)    = "numberL"
    show (FTranspose _)  = "transpose"
    show (FTransposeL _) = "transposeL"
    show (FReshape n _)  = printf "reshape(%d)" n
    show (FReshapeL n _) = printf "reshapeL(%d)" n

data Prim2 = FGroupWithKey Type
           | FGroupWithKeyL Type
           | FSortWithS Type
           | FSortWithL Type
           | FDist Type
           | FDistL Type
           | FRestrict Type
           | FUnconcat Type
           | FPair Type
           | FPairL Type
           | FAppend Type
           | FAppendL Type
           | FIndex Type
           | FIndexL Type
           | FZip Type
           | FZipL Type
           | FCons Type
           | FConsL Type
           | FCartProduct Type
           | FCartProductL Type
           | FNestProduct Type
           | FNestProductL Type
           | FThetaJoin (L.JoinPredicate L.JoinExpr) Type
           | FThetaJoinL (L.JoinPredicate L.JoinExpr) Type
           | FNestJoin (L.JoinPredicate L.JoinExpr) Type
           | FNestJoinL (L.JoinPredicate L.JoinExpr) Type
           | FSemiJoin (L.JoinPredicate L.JoinExpr) Type
           | FSemiJoinL (L.JoinPredicate L.JoinExpr) Type
           | FAntiJoin (L.JoinPredicate L.JoinExpr) Type
           | FAntiJoinL (L.JoinPredicate L.JoinExpr) Type
    deriving (Eq, Generic)

instance Show Prim2 where
    show (FGroupWithKey _)    = "groupWithKey"
    show (FGroupWithKeyL _)   = "groupWithKeyL"
    show (FSortWithS _)       = "sortWithS"
    show (FSortWithL _)       = "sortWithL"
    show (FDist _)            = "dist"
    show (FDistL _)           = "distL"
    show (FRestrict _)        = "restrict"
    show (FUnconcat _)        = "unconcat"
    show (FPair _)            = "pair"
    show (FPairL _)           = "pairL"
    show (FAppend _)          = "append"
    show (FAppendL _)         = "appendL"
    show (FIndex _)           = "index"
    show (FIndexL _)          = "indexL"
    show (FZip _)             = "zip"
    show (FZipL _)            = "zipL"
    show (FCons _)            = "cons"
    show (FConsL _)           = "consL"
    show (FCartProduct _)     = "cartProduct"
    show (FCartProductL _)    = "cartProductL"
    show (FNestProduct _)     = "nestProduct"
    show (FNestProductL _)    = "nestProductL"
    show (FThetaJoin p _)     = printf "equiJoinS_%s" (pp p)
    show (FThetaJoinL p _)    = printf "equiJoinL_%s" (pp p)
    show (FNestJoin p _)      = printf "nestJoinS_%s" (pp p)
    show (FNestJoinL p _)     = printf "nestJoinL_%s" (pp p)
    show (FSemiJoin p _)      = printf "semiJoinS_%s" (pp p)
    show (FSemiJoinL p _)     = printf "semiJoinL_%s" (pp p)
    show (FAntiJoin p _)      = printf "antiJoinS_%s" (pp p)
    show (FAntiJoinL p _)     = printf "antiJoinL_%s" (pp p)

data Prim3 = FCombine Type
    deriving (Eq, Generic)

instance Show Prim3 where
    show (FCombine _) = "combine"

instance Typed Expr where
    typeOf (Table t _ _ _)    = t
    typeOf (PApp1 t _ _)      = t
    typeOf (PApp2 t _ _ _)    = t
    typeOf (PApp3 t _ _ _ _)  = t
    typeOf (If t _ _ _)       = t
    typeOf (BinOp t _ _ _)    = t
    typeOf (UnOp t _ _)       = t
    typeOf (Const t _)        = t
    typeOf (Var t _)          = t
    typeOf (CloApp t _ _)     = t
    typeOf (CloLApp t _ _)    = t
    typeOf (Clo t _ _ _ _ _)  = t
    typeOf (AClo t _ _ _ _ _) = t
