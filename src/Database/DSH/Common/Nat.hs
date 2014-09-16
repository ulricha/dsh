module Database.DSH.Common.Nat where

-- | Natural numbers that encode lifting levels
data Nat = Zero | Succ Nat

intFromNat :: Nat -> Int
intFromNat Zero     = 0
intFromNat (Succ n) = 1 + intFromNat n
