{-# Language ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# Options -fno-warn-incomplete-patterns -fno-warn-orphans #-}

module Ferry.Class where
  
import Database.HDBC

import Ferry.Data
import Ferry.Evaluate

class QA a where
  reify :: a -> Type
  fromN :: Norm -> a
  toQ   :: a -> Q a

  fromQ :: IConnection conn => conn -> Q a -> IO a
  fromQ c (Q a) = evaluate c a >>= (return . fromN)
  

instance QA () where
  reify _ = UnitT
  fromN (UnitN) = ()
  toQ _ = Q UnitE
  
instance QA Bool where
  reify _ = BoolT
  fromN (BoolN b) = b
  toQ a = Q (BoolE a)
  
instance QA Char where
  reify _ = CharT
  fromN (CharN c) = c
  toQ a = Q (CharE a)

instance QA Int where
  reify _ = IntT
  fromN (IntN i) = i
  toQ a = Q (IntE a)

instance (QA a,QA b) => QA (a,b) where
  reify _ = TupleT [reify (undefined :: a), reify (undefined :: b)]
  fromN (TupleN a b []) = (fromN a,fromN b)
  toQ (a,b) = Q (TupleE (forget $ toQ $ a) (forget $ toQ $ b) [])

instance (QA a) => QA [a] where
  reify _ = ListT (reify (undefined :: a))
  fromN (ListN as) = map fromN as
  toQ as = Q (ListE (map (forget . toQ) as))  
  
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

instance Show (Q a) where
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