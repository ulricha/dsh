module Language.ParallelLang.VL.Data.VectorTypes where

import qualified Language.ParallelLang.Common.Data.Type as T

data VType =
    DescrVector
  | ValueVector
  | PrimVal
  | NestedVector Int
  | PropVector
  | Tuple [VType]
  | VectorFun VType VType
  | Tagged VType T.Type
   deriving (Eq, Show)
  
descrT :: VType
descrT = DescrVector

pValT :: VType
pValT = PrimVal

valVT :: VType
valVT = ValueVector

nVectorT :: Int -> VType
nVectorT i = NestedVector i

nVectorT' :: VType -> VType
nVectorT' (NestedVector i) = NestedVector (i + 1)
nVectorT' ValueVector      = NestedVector 2
nVectorT' (Tagged t _)     = nVectorT' t
nVectorT' _                = error $ "Not a nestable type"

tag :: VType -> T.Type -> VType
tag = Tagged

propT :: VType
propT = PropVector

tupleT :: [VType] ->VType
tupleT vs = Tuple vs

infixr 6 .~>

(.~>) :: VType -> VType -> VType
t1 .~> t2 = VectorFun t1 t2

nestingDepth :: VType -> Int
nestingDepth (Tagged t _)     = nestingDepth t
nestingDepth ValueVector      = 1
nestingDepth (NestedVector i) = i
nestingDepth _                = 0    
 
descrOrVal :: VType -> Bool
descrOrVal ValueVector = True
descrOrVal DescrVector = True
descrOrVal (NestedVector 1) = True
descrOrVal _           = False