module Optimizer.VL.Properties.Types where

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
                       
data BottomUpProps = BUProps { emptyProp :: VectorProp Bool 
                             , cardOneProp :: Bool 
                             , vectorSchemaProp :: VectorProp Schema } deriving (Show)
