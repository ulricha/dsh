{-# LANGUAGE TemplateHaskell, 
             ViewPatterns,
             ScopedTypeVariables, 
             MultiParamTypeClasses, 
             FunctionalDependencies, 
             FlexibleInstances, 
             DeriveDataTypeable, 
             TypeOperators, 
             DefaultSignatures, 
             FlexibleContexts,
             TypeFamilies,
             UndecidableInstances,
             DeriveGeneric #-}

module Database.DSH.Generic where
    
import Database.DSH.Impossible


import Database.DSH.Data hiding (GenericQA(..), genericReify, genericToNorm, genericFromNorm)
import GHC.Generics


class GenericQA f where
  genericReify    :: f a -> Type
  -- Reification for sum types, for all children of a sum we can use the default EXCEPT for the plus itself
  genericReify'   :: f a -> Type
  genericReify' _ = ListT $ genericReify (undefined :: f a)
  -- An empty alternative is just an empty list in normal representation EXCEPT for the case of plus itself
  emptyAlternative :: f a -> Norm
  emptyAlternative _ = ListN [] $ genericReify' (undefined :: f a)
  genericToNorm   :: f a -> Norm
  genericFromNorm :: Norm -> f a

-- Constructor without any arguments 
instance GenericQA U1 where
  genericReify _ = UnitT
  genericToNorm U1 = UnitN UnitT
  genericFromNorm (UnitN UnitT) = U1
  genericFromNorm _ = $impossible

-- Constructor with two or more arguments (b can be a product itself)
-- As an invariant a can only be a K1 ultimately (might be wrapped in a M1 node)
instance (GenericQA a, GenericQA b) => GenericQA (a :*: b) where
  genericReify _ = TupleT (genericReify (undefined :: a ())) (genericReify (undefined :: b ()))
  genericToNorm (a :*: b) = TupleN (genericToNorm a) (genericToNorm b) (genericReify (a :*: b))
  genericFromNorm (TupleN a b (TupleT _ _)) = (genericFromNorm a) :*: (genericFromNorm b)
  genericFromNorm _ = $impossible

instance (GenericQA a, GenericQA b) => GenericQA (a :+: b) where
  genericReify _ = TupleT (genericReify' (undefined :: a ()))
                          (genericReify' (undefined :: b ()))
  genericReify' _ = genericReify (undefined :: (a :+: b) ())
  emptyAlternative _ = TupleN (emptyAlternative (undefined :: a ()))
                              (emptyAlternative (undefined :: b ()))
                              (genericReify (undefined :: (a :+: b) ()))
  genericToNorm (L1 a) = TupleN (ListN [genericToNorm a] (genericReify' (undefined :: a ())))
                                (emptyAlternative (undefined :: b ()))
                                (genericReify (undefined :: (a :+: b) ()))
  genericToNorm (R1 b) = TupleN (emptyAlternative (undefined :: a ()))
                                (genericToNorm b)
                                (genericReify (undefined :: (a :+: b) ()))
  genericFromNorm (TupleN (ListN [na] _) _ _) = L1 (genericFromNorm na)
  genericFromNorm (TupleN (ListN [] _) nb _)  = R1 (genericFromNorm nb)
  genericFromNorm _ = $impossible

instance (GenericQA a) => GenericQA (M1 i c a) where
  genericReify _ = genericReify (undefined :: a ())
  genericToNorm (M1 a) = genericToNorm a
  genericFromNorm na = M1 (genericFromNorm na)

    
instance (QA a) => GenericQA (K1 i a) where
  genericReify _ = reify (undefined :: a)
  genericToNorm (K1 a) = toNorm a
  genericFromNorm na = (K1 (fromNorm na))