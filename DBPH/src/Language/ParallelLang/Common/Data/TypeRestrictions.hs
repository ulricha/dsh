{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, OverlappingInstances #-}
module Language.ParallelLang.Common.Data.TypeRestrictions where
    
import Language.ParallelLang.Common.Data.Type 

-- | Class for types that are supported internally
class QT a where
    reify :: a -> Type
    
-- | Class for types that are supported as query result types
class QT a => RT a where
    
instance QT Int where
    reify _ = intT
    
instance QT Bool where
    reify _ = boolT
    
instance QT Char where
    reify _ = stringT

instance QT String where
    reify _ = stringT
    
instance QT Double where
    reify _ = doubleT
    
instance QT () where
    reify _ = unitT

instance QT a => QT [a] where
    reify _ = listT $ reify (undefined :: a)

instance (QT a, QT b) => QT (a, b) where 
    reify _ = tupleT [reify (undefined :: a), reify (undefined :: b)]

instance (QT a, QT b, QT c) => QT (a, b, c) where
    reify _ = tupleT [reify (undefined :: a), reify (undefined :: b), reify (undefined :: c)]

instance forall a b. (QT a, QT b) => QT (a -> b) where
    reify _ = reify (undefined :: a) .-> reify (undefined :: b)
    
instance RT Int where
instance RT Bool where
instance RT Char where
instance RT String where
instance RT Double where
instance RT () where
instance (RT a, RT b) => RT (a, b) where
instance (RT a, RT b, RT c) => RT (a, b, c) where
