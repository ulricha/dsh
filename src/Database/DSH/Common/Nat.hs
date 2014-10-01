module Database.DSH.Common.Nat where

import Control.Exception

-- | Natural numbers that encode lifting levels
data Nat = Zero | Succ Nat deriving (Show, Eq)

intFromNat :: Nat -> Int
intFromNat Zero     = 0
intFromNat (Succ n) = 1 + intFromNat n

-- | Indexes of tuple fields
data TupleIndex = First | Next TupleIndex deriving (Show, Eq)

tupleIndex :: TupleIndex -> Int
tupleIndex First    = 1
tupleIndex (Next f) = 1 + tupleIndex f

intIndex :: Int -> TupleIndex 
intIndex i = assert (i >= 1) $
    if i > 1
    then Next $ (intIndex $ i - 1)
    else First
