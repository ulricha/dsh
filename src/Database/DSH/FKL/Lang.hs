{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE StandaloneDeriving #-}

module Database.DSH.FKL.Lang where

import           Text.Printf

import qualified Database.DSH.Common.Lang   as L
import           Database.DSH.Common.Pretty
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

data Expr = Table   Type String [L.Column] L.TableHints
          | PApp1   Type (LiftedN Prim1) Expr
          | PApp2   Type (LiftedN Prim2) Expr Expr
          | PApp3   Type (LiftedN Prim3) Expr Expr Expr
          | If      Type Expr Expr Expr
          | BinOp   Type (LiftedN L.ScalarBinOp) Expr Expr
          | UnOp    Type (LiftedN L.ScalarUnOp) Expr
          | Const   Type L.Val
          | Var     Type L.Ident

data FExpr = FTable   Type String [L.Column] L.TableHints
           | FPApp1   Type (Lifted Prim1) FExpr
           | FPApp2   Type (Lifted Prim2) FExpr FExpr
           | FPApp3   Type (Lifted Prim3) FExpr FExpr FExpr
           | FIf      Type FExpr FExpr FExpr
           | FBinOp   Type (Lifted L.ScalarBinOp) FExpr FExpr
           | FUnOp    Type (Lifted L.ScalarUnOp) FExpr
           | FConst   Type L.Val
           | FQuickConcat Type FExpr
           | FUnConcat Type FExpr FExpr

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
