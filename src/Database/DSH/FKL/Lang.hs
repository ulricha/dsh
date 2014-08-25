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

data Expr = Table   Type String [L.Column] L.TableHints
          | PApp1   Type Prim1 Expr
          | PApp2   Type Prim2 Expr Expr
          | PApp3   Type Prim3 Expr Expr Expr
          | If      Type Expr Expr Expr
          | BinOp   Type (Lifted L.ScalarBinOp) Expr Expr
          | UnOp    Type (Lifted L.ScalarUnOp) Expr
          | Const   Type L.Val
          -- FIXME variables should not occur after flattening (as
          -- long as we don't have let bindings).
          | Var     Type L.Ident
    deriving (Eq, Generic, Show)

data Prim1 = Length Type
           | LengthL Type
           | Concat Type
           | ConcatL Type
           | Fst Type
           | FstL Type
           | Snd Type
           | SndL Type
           | Sum Type
           | SumL Type
           | Avg Type
           | AvgL Type
           | Minimum Type
           | MinimumL Type
           | Maximum Type
           | MaximumL Type
           | The Type
           | TheL Type
           -- | QuickConcat does not unsegment the vector. That is:
           -- the descriptor might not be normalized and segment
           -- descriptors other than 1 might occur. This is propably
           -- ok when we know that a concated vector will be
           -- unconcated again. We know this statically when
           -- introducing concat/unconcat for higher-lifted
           -- primitives.
           | QuickConcat Type
           | Tail Type
           | TailL Type
           | Reverse Type
           | ReverseL Type
           | And Type
           | AndL Type
           | Or Type
           | OrL Type
           | Init Type
           | InitL Type
           | Last Type
           | LastL Type
           | Nub Type
           | NubL Type
           | Number Type
           | NumberL Type
           | Transpose Type
           | TransposeL Type
           | Reshape Integer Type
           | ReshapeL Integer Type
    deriving (Eq, Generic)

instance Show Prim1 where
    show (Length _)      = "length"
    show (LengthL _)     = "lengthᴸ"
    show (ConcatL _)     = "concatᴸ"
    show (Fst _)         = "fst"
    show (Snd _)         = "snd"
    show (FstL _)        = "fstᴸ"
    show (SndL _)        = "sndᴸ"
    show (Concat _)      = "concat"
    show (QuickConcat _) = "quickConcat"
    show (Sum _)         = "sum"
    show (Avg _)         = "avg"
    show (SumL _)        = "sumᴸ"
    show (AvgL _)        = "avgᴸ"
    show (The _)         = "the"
    show (TheL _)        = "theᴸ"
    show (Minimum _)     = "minimum"
    show (MinimumL _)    = "minimumᴸ"
    show (Maximum _)     = "maximum"
    show (MaximumL _)    = "maximumᴸ"
    show (Tail _)        = "tail"
    show (TailL _)       = "tailᴸ"
    show (Reverse _)     = "reverse"
    show (ReverseL _)    = "reverseᴸ"
    show (And _)         = "and"
    show (AndL _)        = "andᴸ"
    show (Or _)          = "or"
    show (OrL _)         = "orᴸ"
    show (Init _)        = "init"
    show (InitL _)       = "initᴸ"
    show (Last _)        = "last"
    show (LastL _)       = "lastᴸ"
    show (Nub _)         = "nub"
    show (NubL _)        = "nubᴸ"
    show (Number _)      = "number"
    show (NumberL _)     = "numberᴸ"
    show (Transpose _)   = "transpose"
    show (TransposeL _)  = "transposeᴸ"
    show (Reshape n _)   = printf "reshape(%d)" n
    show (ReshapeL n _)  = printf "reshapeᴸ(%d)" n

data Prim2 = Group Type
           | GroupL Type
           | Sort Type
           | SortL Type
           | Restrict Type
           | RestrictL Type
           | Pair Type
           | PairL Type
           | Append Type
           | AppendL Type
           | Index Type
           | IndexL Type
           | Zip Type
           | ZipL Type
           | Cons Type
           | ConsL Type
           | CartProduct Type
           | CartProductL Type
           | NestProduct Type
           | NestProductL Type
           | ThetaJoin (L.JoinPredicate L.JoinExpr) Type
           | ThetaJoinL (L.JoinPredicate L.JoinExpr) Type
           | NestJoin (L.JoinPredicate L.JoinExpr) Type
           | NestJoinL (L.JoinPredicate L.JoinExpr) Type
           | SemiJoin (L.JoinPredicate L.JoinExpr) Type
           | SemiJoinL (L.JoinPredicate L.JoinExpr) Type
           | AntiJoin (L.JoinPredicate L.JoinExpr) Type
           | AntiJoinL (L.JoinPredicate L.JoinExpr) Type
           | Unconcat Type
           | Dist Type
           | DistL Type
    deriving (Eq, Generic)

instance Show Prim2 where
    show (Group _)           = "group"
    show (GroupL _)          = "groupᴸ"
    show (Sort _)            = "sort"
    show (SortL _)           = "sortᴸ"
    show (Dist _)            = "dist"
    show (DistL _)           = "distᴸ"
    show (Restrict _)        = "restrict"
    show (RestrictL _)       = "restrictᴸ"
    show (Unconcat _)        = "unconcat"
    show (Pair _)            = "pair"
    show (PairL _)           = "pairᴸ"
    show (Append _)          = "append"
    show (AppendL _)         = "appendᴸ"
    show (Index _)           = "index"
    show (IndexL _)          = "indexᴸ"
    show (Zip _)             = "zip"
    show (ZipL _)            = "zipᴸ"
    show (Cons _)            = "cons"
    show (ConsL _)           = "consᴸ"
    show (CartProduct _)     = "⨯"
    show (CartProductL _)    = "⨯ᴸL"
    show (NestProduct _)     = "▽"
    show (NestProductL _)    = "▽ᴸ"
    show (ThetaJoin p _)     = printf "⨝_%s" (pp p)
    show (ThetaJoinL p _)    = printf "⨝ᴸ_%s" (pp p)
    show (NestJoin p _)      = printf "△_%s" (pp p)
    show (NestJoinL p _)     = printf "△ᴸ_%s" (pp p)
    show (SemiJoin p _)      = printf "⋉_%s" (pp p)
    show (SemiJoinL p _)     = printf "⋉ᴸ_%s" (pp p)
    show (AntiJoin p _)      = printf "▷_%s" (pp p)
    show (AntiJoinL p _)     = printf "▷ᴸ_%s" (pp p)

data Prim3 = Combine Type
    deriving (Eq, Generic)

instance Show Prim3 where
    show (Combine _) = "combine"

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
