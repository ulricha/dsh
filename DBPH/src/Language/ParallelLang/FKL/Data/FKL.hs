{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val(Val())
import Language.ParallelLang.Common.Data.Type(Typed, typeOf, Type)

type DataColumn = String 

type TypedColumn = (DataColumn, Type)

type Key = [DataColumn]

-- | Data type expr represents flat kernel language.
data Expr where
    Table   :: Type -> String -> [TypedColumn] -> [Key] -> Expr
    Labeled :: String -> Expr -> Expr -- | Constructor for debugging purposes
    Pair    :: Type -> Expr -> Expr -> Expr
    PApp1   :: Type -> Prim1 -> Expr -> Expr
    PApp2   :: Type -> Prim2 -> Expr -> Expr -> Expr
    PApp3   :: Type -> Prim3 -> Expr -> Expr -> Expr -> Expr
    CloApp  :: Type -> Expr -> Expr -> Expr
    CloLApp :: Type -> Expr -> Expr -> Expr
    Let     :: Type -> String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
    If      :: Type -> Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
    BinOp   :: Type -> Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const   :: Type -> Val -> Expr -- | Constant value
    Var     :: Type -> String -> Expr -- | Variable lifted to level i
    Nil     :: Type -> Expr -- | []
    Clo     :: Type -> String -> [(String, Expr)] -> String -> Expr -> Expr -> Expr  -- When performing normal function application ignore the first value of the freeVars!!!
    AClo    :: Type -> String -> Expr -> [(String, Expr)] -> String -> Expr -> Expr -> Expr 
    deriving Eq

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
           | SumL Type
           | The Type
           | TheL Type
           | Concat Type
    deriving Eq
    
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
    show (Sum _)        = "sum"
    show (SumL _)       = "sumL"
    show (The _)        = "the"
    show (TheL _)       = "theL"
    
    
data Prim2 = GroupWithS Type
           | GroupWithL Type
           | SortWithS Type
           | SortWithL Type
           | Index Type
           | Dist Type
           | Dist_L Type
           | Restrict Type
           | BPermute Type
           | Unconcat Type
    deriving Eq

instance Show Prim2 where
    show (GroupWithS _) = "groupWithS"
    show (GroupWithL _) = "groupWithL"
    show (SortWithS _)  = "sortWithS"
    show (SortWithL _)  = "sortWithL" 
    show (Index _)      = "index"
    show (Dist _)       = "dist"
    show (Dist_L _)     = "dist_L"
    show (Restrict _)   = "restrict"
    show (BPermute _)   = "bPermute"
    show (Unconcat _)   = "unconcat"

data Prim3 = Combine Type
    deriving Eq

instance Show Prim3 where
    show (Combine _) = "combine"

instance Typed Expr where
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

