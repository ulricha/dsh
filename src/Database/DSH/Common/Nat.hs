{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Common.Nat where

import Database.DSH.Common.Impossible

-- | Natural numbers that encode lifting levels
data Nat = Zero | Succ Nat deriving (Show, Eq)

instance Ord Nat where
    Zero    <= Succ _  = True
    Succ n1 <= Succ n2 = n1 <= n2
    _       <= _       = False

(.-) :: Nat -> Nat -> Maybe Nat
n1      .- Zero    = Just n1
Succ n1 .- Succ n2 = n1 .- n2
Zero    .- Succ _  = Nothing

intFromNat :: Nat -> Int
intFromNat Zero     = 0
intFromNat (Succ n) = 1 + intFromNat n

-- | Indexes of tuple fields
data TupleIndex = First | Next TupleIndex deriving (Show, Eq)

tupleIndex :: TupleIndex -> Int
tupleIndex First    = 1
tupleIndex (Next f) = 1 + tupleIndex f

intIndex :: Int -> TupleIndex
intIndex i
    | i < 1     = $impossible
    | i > 1     = Next $ (intIndex $ i - 1)
    | otherwise = First
