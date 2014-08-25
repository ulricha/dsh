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

data Prim1 = Length
           | LengthL
           | Concat
           | ConcatL
           | Fst
           | FstL
           | Snd
           | SndL
           | Sum
           | SumL
           | Avg
           | AvgL
           | Minimum
           | MinimumL
           | Maximum
           | MaximumL
           | The
           | TheL
           -- | QuickConcat does not unsegment the vector. That is:
           -- the descriptor might not be normalized and segment
           -- descriptors other than 1 might occur. This is propably
           -- ok when we know that a concated vector will be
           -- unconcated again. We know this statically when
           -- introducing concat/unconcat for higher-lifted
           -- primitives.
           | QuickConcat
           | Tail
           | TailL
           | Reverse
           | ReverseL
           | And
           | AndL
           | Or
           | OrL
           | Init
           | InitL
           | Last
           | LastL
           | Nub
           | NubL
           | Number
           | NumberL
           | Transpose
           | TransposeL
           | Reshape Integer
           | ReshapeL Integer
    deriving (Eq, Generic)

instance Show Prim1 where
    show Length       = "length"
    show LengthL      = "lengthᴸ"
    show ConcatL      = "concatᴸ"
    show Fst          = "fst"
    show Snd          = "snd"
    show FstL         = "fstᴸ"
    show SndL         = "sndᴸ"
    show Concat       = "concat"
    show QuickConcat  = "quickConcat"
    show Sum          = "sum"
    show Avg          = "avg"
    show SumL         = "sumᴸ"
    show AvgL         = "avgᴸ"
    show The          = "the"
    show TheL         = "theᴸ"
    show Minimum      = "minimum"
    show MinimumL     = "minimumᴸ"
    show Maximum      = "maximum"
    show MaximumL     = "maximumᴸ"
    show Tail         = "tail"
    show TailL        = "tailᴸ"
    show Reverse      = "reverse"
    show ReverseL     = "reverseᴸ"
    show And          = "and"
    show AndL         = "andᴸ"
    show Or           = "or"
    show OrL          = "orᴸ"
    show Init         = "init"
    show InitL        = "initᴸ"
    show Last         = "last"
    show LastL        = "lastᴸ"
    show Nub          = "nub"
    show NubL         = "nubᴸ"
    show Number       = "number"
    show NumberL      = "numberᴸ"
    show Transpose    = "transpose"
    show TransposeL   = "transposeᴸ"
    show (Reshape n)  = printf "reshape(%d)" n
    show (ReshapeL n) = printf "reshapeᴸ(%d)" n

data Prim2 = Group
           | GroupL
           | Sort
           | SortL
           | Restrict
           | RestrictL
           | Pair
           | PairL
           | Append
           | AppendL
           | Index
           | IndexL
           | Zip
           | ZipL
           | Cons
           | ConsL
           | CartProduct
           | CartProductL
           | NestProduct
           | NestProductL
           | ThetaJoin (L.JoinPredicate L.JoinExpr)
           | ThetaJoinL (L.JoinPredicate L.JoinExpr)
           | NestJoin (L.JoinPredicate L.JoinExpr)
           | NestJoinL (L.JoinPredicate L.JoinExpr)
           | SemiJoin (L.JoinPredicate L.JoinExpr)
           | SemiJoinL (L.JoinPredicate L.JoinExpr)
           | AntiJoin (L.JoinPredicate L.JoinExpr)
           | AntiJoinL (L.JoinPredicate L.JoinExpr)
           | Unconcat
           | Dist
           | DistL
           deriving (Eq, Generic)

instance Show Prim2 where
    show Group           = "group"
    show GroupL          = "groupᴸ"
    show Sort            = "sort"
    show SortL           = "sortᴸ"
    show Dist            = "dist"
    show DistL           = "distᴸ"
    show Restrict        = "restrict"
    show RestrictL       = "restrictᴸ"
    show Unconcat        = "unconcat"
    show Pair            = "pair"
    show PairL           = "pairᴸ"
    show Append          = "append"
    show AppendL         = "appendᴸ"
    show Index           = "index"
    show IndexL          = "indexᴸ"
    show Zip             = "zip"
    show ZipL            = "zipᴸ"
    show Cons            = "cons"
    show ConsL           = "consᴸ"
    show CartProduct     = "⨯"
    show CartProductL    = "⨯ᴸL"
    show NestProduct     = "▽"
    show NestProductL    = "▽ᴸ"
    show (ThetaJoin p)   = printf "⨝_%s" (pp p)
    show (ThetaJoinL p)  = printf "⨝ᴸ_%s" (pp p)
    show (NestJoin p)    = printf "△_%s" (pp p)
    show (NestJoinL p)   = printf "△ᴸ_%s" (pp p)
    show (SemiJoin p)    = printf "⋉_%s" (pp p)
    show (SemiJoinL p)   = printf "⋉ᴸ_%s" (pp p)
    show (AntiJoin p)    = printf "▷_%s" (pp p)
    show (AntiJoinL p)   = printf "▷ᴸ_%s" (pp p)

data Prim3 = Combine
    deriving (Eq, Generic)

instance Show Prim3 where
    show Combine = "combine"

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
