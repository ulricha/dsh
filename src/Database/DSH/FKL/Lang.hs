{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE StandaloneDeriving #-}

module Database.DSH.FKL.Lang where

import qualified Database.DSH.Common.Lang   as L
import           Database.DSH.Common.Type   (Type, Typed, typeOf)

import           GHC.Generics               (Generic)

---------------------------------------------------------------------------------
-- Natural numbers that encode lifting levels

data Nat = Zero | Succ Nat

intFromNat :: Nat -> Int
intFromNat Zero     = 0
intFromNat (Succ n) = 1 + intFromNat n

-- | 'LiftedN' defines an FKL dialect in which primitives and
-- operators might be lifted to arbitrary levels.
data LiftedN p = LiftedN Nat p

-- | 'Lifted' defines an FKL dialect in which primitives and operators
-- occur either unlifted or lifted once.
data Lifted p = Lifted p
              | NotLifted p
              deriving (Show)

data LExpr = LTable   Type String [L.Column] L.TableHints
           | LPApp1   Type (LiftedN Prim1) LExpr
           | LPApp2   Type (LiftedN Prim2) LExpr LExpr
           | LPApp3   Type (LiftedN Prim3) LExpr LExpr LExpr
           | LIf      Type LExpr LExpr LExpr
           | LBinOp   Type (LiftedN L.ScalarBinOp) LExpr LExpr
           | LUnOp    Type (LiftedN L.ScalarUnOp) LExpr
           | LConst   Type L.Val
           | LVar     Type L.Ident

data Expr = Table   Type String [L.Column] L.TableHints
          | PApp1   Type (Lifted Prim1) Expr
          | PApp2   Type (Lifted Prim2) Expr Expr
          | PApp3   Type (Lifted Prim3) Expr Expr Expr
          | If      Type Expr Expr Expr
          | BinOp   Type (Lifted L.ScalarBinOp) Expr Expr
          | UnOp    Type (Lifted L.ScalarUnOp) Expr
          | Const   Type L.Val
          | QuickConcat Type Expr
          | UnConcat Int Type Expr Expr

-- | QuickConcat does not unsegment the vector. That is:
-- the descriptor might not be normalized and segment
-- descriptors other than 1 might occur. This is propably
-- ok when we know that a concated vector will be
-- unconcated again. We know this statically when
-- introducing concat/unconcat for higher-lifted
-- primitives.

data Prim1 = Length
           | Concat
           | Fst
           | Snd
           | Sum
           | Avg
           | Minimum
           | Maximum
           | The
           | Tail
           | Reverse
           | And
           | Or
           | Init
           | Last
           | Nub
           | Number
           | Transpose
           | Reshape Integer
    deriving (Show, Eq, Generic)

data Prim2 = Group
           | Sort
           | Restrict
           | Pair
           | Append
           | Index
           | Zip
           | Cons
           | CartProduct
           | NestProduct
           | ThetaJoin (L.JoinPredicate L.JoinExpr)
           | NestJoin (L.JoinPredicate L.JoinExpr)
           | SemiJoin (L.JoinPredicate L.JoinExpr)
           | AntiJoin (L.JoinPredicate L.JoinExpr)
           | Dist
           deriving (Show, Eq, Generic)

data Prim3 = Combine
    deriving (Show, Eq, Generic)

instance Typed LExpr where
    typeOf (LTable t _ _ _)    = t
    typeOf (LPApp1 t _ _)      = t
    typeOf (LPApp2 t _ _ _)    = t
    typeOf (LPApp3 t _ _ _ _)  = t
    typeOf (LIf t _ _ _)       = t
    typeOf (LBinOp t _ _ _)    = t
    typeOf (LUnOp t _ _)       = t
    typeOf (LConst t _)        = t
    typeOf (LVar t _)          = t

instance Typed Expr where
    typeOf (Table t _ _ _)    = t
    typeOf (PApp1 t _ _)      = t
    typeOf (PApp2 t _ _ _)    = t
    typeOf (PApp3 t _ _ _ _)  = t
    typeOf (If t _ _ _)       = t
    typeOf (BinOp t _ _ _)    = t
    typeOf (UnOp t _ _)       = t
    typeOf (Const t _)        = t
    typeOf (QuickConcat t _)  = t
    typeOf (UnConcat _ t _ _) = t
