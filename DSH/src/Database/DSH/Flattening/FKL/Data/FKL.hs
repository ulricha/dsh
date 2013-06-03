{-# LANGUAGE DeriveGeneric #-}
module Database.DSH.Flattening.FKL.Data.FKL where

import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.Common.Data.Val(Val())
import Database.DSH.Flattening.Common.Data.Type(Typed, typeOf, Type)

import GHC.Generics (Generic)

type DataColumn = String 

type TypedColumn = (DataColumn, Type)

type Key = [DataColumn]

-- | Data type expr represents flat kernel language.
data Expr = Table   Type String [TypedColumn] [Key]
          | PApp1   Type Prim1 Expr
          | PApp2   Type Prim2 Expr Expr 
          | PApp3   Type Prim3 Expr Expr Expr
          | CloApp  Type Expr Expr
          | CloLApp Type Expr Expr
          | If      Type Expr Expr Expr -- | If expr1 then expr2 else expr3
          | BinOp   Type Op Expr Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
          | Const   Type Val  -- | Constant value
          | Var     Type String  -- | Variable lifted to level i
          | Clo     Type String [String] String Expr Expr -- When performing normal function application ignore the first value of the freeVars!!!
          | AClo    Type String [String] String Expr Expr
    deriving (Eq, Generic)

data Prim1 = LengthPrim Type
           | LengthLift Type
           | NotPrim Type
           | NotVec Type
           | ConcatLift Type
           | Fst Type
           | Snd Type
           | FstL Type
           | SndL Type
           | Sum Type
           | Avg Type
           | SumL Type
           | AvgL Type
           | Minimum Type
           | MinimumL Type
           | Maximum Type
           | MaximumL Type
           | The Type
           | TheL Type
           | Concat Type
           | QuickConcat Type
           | IntegerToDouble Type
           | IntegerToDoubleL Type
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
    deriving (Eq, Generic)
    
instance Show Prim1 where
    show (LengthPrim _) = "lengthPrim"
    show (LengthLift _) = "lengthLift"
    show (NotPrim _)    = "notPrim"
    show (NotVec _)     = "notVec"
    show (ConcatLift _) = "concatLift"
    show (Fst _)        = "fst"
    show (Snd _)        = "snd"
    show (FstL _)       = "fstL"
    show (SndL _)       = "sndL"
    show (Concat _)     = "concat"
    show (QuickConcat _) = "quickConcat"
    show (Sum _)        = "sum"
    show (Avg _)        = "avg"
    show (SumL _)       = "sumL"
    show (AvgL _)       = "avgL"
    show (The _)        = "the"
    show (TheL _)       = "theL"
    show (Minimum _)    = "minimum"
    show (MinimumL _)   = "minimumL"
    show (Maximum _)    = "maximum"
    show (MaximumL _)   = "maximumL"
    show (IntegerToDouble _) = "integerToDouble"
    show (IntegerToDoubleL _) = "integerToDoubleL"
    show (Tail _)       = "tail"
    show (TailL _)      = "tailL"
    show (Reverse _)    = "reverse"
    show (ReverseL _)   = "reverseL"
    show (And _)        = "and"
    show (AndL _)       = "andL"
    show (Or _)         = "or"
    show (OrL _)        = "orL"
    show (Init _)       = "init"
    show (InitL _)      = "initL"
    show (Last _)       = "last"
    show (LastL _)      = "lastL"
    show (Nub _)        = "nub"
    show (NubL _)       = "nubL"
    
data Prim2 = GroupWithKeyS Type
           | GroupWithKeyL Type
           | SortWithS Type
           | SortWithL Type
           | Dist Type
           | Dist_L Type
           | Restrict Type
           | Unconcat Type
           | Pair Type
           | PairL Type
           | Append Type
           | AppendL Type
           | Index Type
           | IndexL Type
           | Take Type
           | TakeL Type
           | Drop Type
           | DropL Type
           | Zip Type
           | ZipL Type
           | CartProduct Type
           | CartProductL Type
           | TakeWithS Type
           | TakeWithL Type
           | DropWithS Type
           | DropWithL Type
    deriving (Eq, Generic)

instance Show Prim2 where
    show (GroupWithKeyS _) = "groupWithKeyS"
    show (GroupWithKeyL _) = "groupWithKeyL"
    show (SortWithS _)  = "sortWithS"
    show (SortWithL _)  = "sortWithL" 
    show (Dist _)       = "dist"
    show (Dist_L _)     = "dist_L"
    show (Restrict _)   = "restrict"
    show (Unconcat _)   = "unconcat"
    show (Pair _)       = "pair"
    show (PairL _)      = "pairL"
    show (Append _)     = "append"
    show (AppendL _)    = "appendL"
    show (Index _)      = "index"
    show (IndexL _)     = "indexL"
    show (Take _)       = "take"
    show (TakeL _)      = "takeL"
    show (Drop _)       = "drop"
    show (DropL _)      = "dropL"
    show (Zip _)        = "zip"
    show (ZipL _)       = "zipL"
    show (TakeWithL _)  = "takeWithL"
    show (TakeWithS _)  = "takeWithS"
    show (DropWithL _)  = "dropWithL"
    show (DropWithS _)  = "dropWithS"
    show (CartProduct _) = "cartProduct"
    show (CartProductL _) = "cartProductL"

data Prim3 = Combine Type
    deriving (Eq, Generic)

instance Show Prim3 where
    show (Combine _) = "combine"

instance Typed Expr where
    typeOf (Table t _ _ _) = t
    typeOf (PApp1 t _ _) = t
    typeOf (PApp2 t _ _ _) = t
    typeOf (PApp3 t _ _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
    typeOf (CloApp t _ _) = t
    typeOf (CloLApp t _ _) = t
    typeOf (Clo t _ _ _ _ _) = t
    typeOf (AClo t _ _ _ _ _) = t
