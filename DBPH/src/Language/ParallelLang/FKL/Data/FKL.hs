{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val(Val())
import Language.ParallelLang.Common.Data.Type(Typed, typeOf)

type DataColumn = String 

type TypedColumn t = (DataColumn, t)

type Key = [DataColumn]

-- | Data type expr represents flat kernel language.
data Expr t where
    Table   :: t -> String -> [TypedColumn t] -> [Key] -> Expr t
    Labeled :: String -> Expr t -> Expr t -- | Constructor for debugging purposes
    Pair    :: t -> Expr t -> Expr t -> Expr t
    PApp1   :: t -> Prim1 t -> Expr t -> Expr t
    PApp2   :: t -> Prim2 t -> Expr t -> Expr t -> Expr t
    PApp3   :: t -> Prim3 t -> Expr t -> Expr t -> Expr t -> Expr t
    CloApp  :: t -> Expr t -> Expr t -> Expr t
    CloLApp :: t -> Expr t -> Expr t -> Expr t
    Let     :: t -> String -> Expr t -> Expr t -> Expr t -- | Let a variable have value expr1 in expr2
    If      :: t -> Expr t -> Expr t -> Expr t -> Expr t -- | If expr1 then expr2 else expr3
    BinOp   :: t -> Op -> Expr t -> Expr t -> Expr t -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const   :: t -> Val -> Expr t -- | Constant value
    Var     :: t -> String -> Expr t -- | Variable lifted to level i
    Nil     :: t -> Expr t -- | []
    Clo     :: t -> String -> [(String, Expr t)] -> String -> Expr t -> Expr t -> Expr t -- When performing normal function application ignore the first value of the freeVars!!!
    AClo    :: t -> String -> Expr t -> [(String, Expr t)] -> String -> Expr t -> Expr t -> Expr t
    deriving Eq

data Prim1 t = LengthPrim t
             | LengthLift t 
             | NotPrim t 
             | NotVec t
             | ConcatLift t
             | Fst t
             | Snd t
             | FstL t
             | SndL t
    deriving Eq
    
instance Show (Prim1 t)where
    show (LengthPrim _) = "lengthPrim"
    show (LengthLift _) = "lengthLift"
    show (NotPrim _)    = "notPrim"
    show (NotVec _)     = "notVec"
    show (ConcatLift _) = "concatLift"
    show (Fst _)        = "fst"
    show (Snd _)        = "snd"
    show (FstL _)       = "fstL"
    show (SndL _)       = "sndL"
    
data Prim2 t = GroupWithS t
             | GroupWithL t 
             | Index t
             | Dist t
             | Dist_L t
             | Restrict t
             | Extract t
             | BPermute t
    deriving Eq

instance Show (Prim2 t) where
    show (GroupWithS _) = "groupWithS"
    show (GroupWithL _) = "groupWithL" 
    show (Index _)      = "index"
    show (Dist _)       = "dist"
    show (Dist_L _)     = "dist_L"
    show (Restrict _)   = "restrict"
    show (Extract _)    = "extract"
    show (BPermute _)   = "bPermute"

data Prim3 t = Combine t 
             | Insert t
    deriving Eq

instance Show (Prim3 t) where
    show (Combine _) = "combine"
    show (Insert _)  = "insert"

instance Typed Expr t where
    -- typeOf (App t _ _) = t
    typeOf (Table t _ _ _) = t
    typeOf (PApp1 t _ _) = t
    typeOf (PApp2 t _ _ _) = t
    typeOf (PApp3 t _ _ _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
    typeOf (Nil t) = t
    typeOf (Labeled _ e) = typeOf e
    typeOf (CloApp t _ _) = t
    typeOf (CloLApp t _ _) = t
    typeOf (Clo t _ _ _ _ _) = t
    typeOf (AClo t _ _ _ _ _ _) = t
    typeOf (Pair t _ _) = t

