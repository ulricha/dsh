{-# Language ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# Options -fno-warn-incomplete-patterns -fno-warn-orphans #-}

module Ferry.Class where
  
import Database.HDBC

import Ferry.Data
import Ferry.Evaluate

class QA a where
  reify :: a -> Type
  toNorm :: a -> Norm
  fromNorm :: Norm -> a

toQ   :: (QA a) => a -> Q a
toQ = Q . normToExp . toNorm

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) = evaluate c a >>= (return . fromNorm)
  

instance QA () where
  reify _ = UnitT
  toNorm _ = UnitN
  fromNorm (UnitN) = ()

instance QA Bool where
  reify _ = BoolT
  toNorm b = BoolN b
  fromNorm (BoolN b) = b
  
instance QA Char where
  reify _ = CharT
  toNorm c = CharN c  
  fromNorm (CharN c) = c

instance QA Int where
  reify _ = IntT
  toNorm i = IntN i
  fromNorm (IntN i) = i

instance (QA a,QA b) => QA (a,b) where
  reify _ = TupleT (reify (undefined :: a)) (reify (undefined :: b))
  toNorm (a,b) = TupleN (toNorm a) (toNorm b)
  fromNorm (TupleN a b) = (fromNorm a,fromNorm b)

instance (QA a) => QA [a] where
  reify _ = ListT (reify (undefined :: a))
  toNorm as = ListN (map toNorm as)
  fromNorm (ListN as) = map fromNorm as
  
class BasicType a where
  
instance BasicType () where
instance BasicType Int where
instance BasicType Bool where
instance BasicType Char where

-- * Refering to Real Database Tables

class (QA a) => TA a where
  table :: String -> Q [a]
  table s = Q (TableE s (reify (undefined :: a)))

instance TA () where
instance TA Int where
instance TA Bool where
instance TA Char where
instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

-- * Eq, Ord, Show and Num Instances for Databse Queries

instance Show (Q Int) where
  show _ = "Query"

instance Eq (Q Int) where
  (==) _ _ = undefined

instance Num (Q Int) where
  (+) (Q e1) (Q e2) = Q (AppE (AppE (VarE "add") e1) e2)
  (*) (Q e1) (Q e2) = Q (AppE (AppE (VarE "mul") e1) e2)
  abs (Q e1) = Q (AppE (VarE "abs") e1)
  negate (Q e1) = Q (AppE (VarE "negate") e1)
  fromInteger i = toQ (fromIntegral i)
  signum (Q e1) = Q (AppE (VarE "signum") e1)

-- * Support for View Patterns

class View a b | a -> b where
  view :: a -> b

instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
  view (Q a) = (Q (AppE (VarE "proj_2_1") a), Q (AppE (VarE "proj_2_2") a))