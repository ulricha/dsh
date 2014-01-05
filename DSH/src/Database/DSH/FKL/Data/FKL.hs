{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.FKL.Data.FKL where

import           Text.Printf

import Database.DSH.Common.Data.Op
import Database.DSH.Common.Data.Expr
import Database.DSH.Common.Data.JoinExpr
import Database.DSH.Common.Data.Val(Val())
import Database.DSH.Common.Data.Type(Typed, typeOf, Type)

import GHC.Generics (Generic)

-- | Data type expr represents flat kernel language.
data Expr = Table   Type String [Column] [Key]
          | PApp1   Type Prim1 Expr
          | PApp2   Type Prim2 Expr Expr 
          | PApp3   Type Prim3 Expr Expr Expr
          | CloApp  Type Expr Expr
          | CloLApp Type Expr Expr
          | If      Type Expr Expr Expr -- | If expr1 then expr2 else expr3
          | BinOp   Type Op Expr Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
          | Const   Type Val  -- | Constant value
          | Var     Type Ident  -- | Variable lifted to level i
          | Clo     Type Ident [Ident] Ident Expr Expr -- When performing normal function application ignore the first value of the freeVars!!!
          | AClo    Type Ident [Ident] Ident Expr Expr
    deriving (Eq, Generic)

data Prim1 = FLength Type
           | FLengthL Type
           | FNot Type
           | FNotL Type
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
           | FIntegerToDouble Type
           | FIntegerToDoubleL Type
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
    deriving (Eq, Generic)
    
instance Show Prim1 where
    show (FLength _)     = "length"
    show (FLengthL _)    = "lengthL"
    show (FNot _)        = "not"
    show (FNotL _)       = "notL"
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
    show (FIntegerToDouble _) = "integerToDouble"
    show (FIntegerToDoubleL _) = "integerToDoubleL"
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
           | FTake Type
           | FTakeL Type
           | FDrop Type
           | FDropL Type
           | FZip Type
           | FZipL Type
           | FCartProduct Type
           | FCartProductL Type
           | FEquiJoin JoinExpr JoinExpr Type
           | FEquiJoinL JoinExpr JoinExpr Type
           | FNestJoin JoinExpr JoinExpr Type
           | FNestJoinL JoinExpr JoinExpr Type
           | FSemiJoin JoinExpr JoinExpr Type
           | FSemiJoinL JoinExpr JoinExpr Type
           | FAntiJoin JoinExpr JoinExpr Type
           | FAntiJoinL JoinExpr JoinExpr Type
           | FTakeWith Type
           | FTakeWithL Type
           | FDropWith Type
           | FDropWithL Type
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
    show (FTake _)            = "take"
    show (FTakeL _)           = "takeL"
    show (FDrop _)            = "drop"
    show (FDropL _)           = "dropL"
    show (FZip _)             = "zip"
    show (FZipL _)            = "zipL"
    show (FTakeWithL _)       = "takeWithL"
    show (FTakeWith _)        = "takeWithS"
    show (FDropWithL _)       = "dropWithL"
    show (FDropWith _)        = "dropWithS"
    show (FCartProduct _)     = "cartProduct"
    show (FCartProductL _)    = "cartProductL"
    show (FEquiJoin e1 e2 _)  = printf "equiJoinS(%s, %s)" (show e1) (show e2)
    show (FEquiJoinL e1 e2 _) = printf "equiJoinL(%s, %s)" (show e1) (show e2)
    show (FNestJoin e1 e2 _)  = printf "nestJoinS(%s, %s)" (show e1) (show e2)
    show (FNestJoinL e1 e2 _) = printf "nestJoinL(%s, %s)" (show e1) (show e2)
    show (FSemiJoin e1 e2 _)  = printf "semiJoinS(%s, %s)" (show e1) (show e2)
    show (FSemiJoinL e1 e2 _) = printf "semiJoinL(%s, %s)" (show e1) (show e2)
    show (FAntiJoin e1 e2 _)  = printf "antiJoinS(%s, %s)" (show e1) (show e2)
    show (FAntiJoinL e1 e2 _) = printf "antiJoinL(%s, %s)" (show e1) (show e2)

data Prim3 = FCombine Type
    deriving (Eq, Generic)

instance Show Prim3 where
    show (FCombine _) = "combine"

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
