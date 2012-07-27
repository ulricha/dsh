module Optimizer.VL.Properties.Types where

-- import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a
                    
instance Show a => Show (VectorProp a) where
  show (VProp a) = show a
  show (VPropPair a1 a2) = show (a1, a2)
  show (VPropTriple a1 a2 a3) = show (a1, a2, a3)
                    
data Schema = ValueVector Int
            | AtomicVector Int
            | DescrVector
            | RenameVector
            | PropVector
              deriving Show
                       
{-
-- newtype PredExpr = VecOp AlgNode AlgNode
                       
data Predicate = Pred VecOp DBCol DBCol
                 deriving (Show, Eq)
                       
{- Index space transformation -}
data ISTrans = PredT Predicate ISTrans
             | SelectT ISTrans
             | NumberT ISTrans
             | ConstT ISTrans
             | PosSeed AlgNode
             | DescrSeed AlgNode
             deriving Show
                      
newtype PosIS = P ISTrans deriving Show
newtype DescrIS = D ISTrans deriving Show
newtype SourceIS = S ISTrans deriving Show
newtype TargetIS = T ISTrans deriving Show
                      
data IS = DBVSpace DescrIS PosIS
        | DBPSpace
        | DescrVectorSpace DescrIS PosIS
        | RenameVectorTransform SourceIS TargetIS
        | PropVectorTransform
          deriving Show
-}
                       
data Const = Const VLVal
           | NoConst
            deriving Show 
             
data ConstDescr = ConstDescr Nat
                | NonConstDescr
                deriving Show 

data ConstPayload = ConstPL VLVal
                  | NonConstPL
                  deriving Show 
             
data ConstVec = DBVConst ConstDescr [ConstPayload]
              | DescrVecConst ConstDescr
              | RenameVecConst SourceConstDescr TargetConstDescr
              | DBPConst [ConstPayload]
              | PropVecConst SourceConstDescr TargetConstDescr
              deriving Show 
                       
newtype SourceConstDescr = SC ConstDescr deriving Show
newtype TargetConstDescr = TC ConstDescr deriving Show
                       
data BottomUpProps = BUProps { emptyProp :: VectorProp Bool 
                             , cardOneProp :: Bool 
                             , vectorSchemaProp :: VectorProp Schema } deriving (Show)
