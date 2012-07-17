module Optimizer.VL.Properties.Types where

data VectorSchema = ValueVector Int
                  | AtomicVector Int
                  | DescrVector
                  | RenameVector
                  | PropVector
                  | VectorPair VectorSchema VectorSchema
                  | VectorTriple VectorSchema VectorSchema VectorSchema
                    deriving (Show)

data BottomUpProps = BUProps { emptyProp :: Bool 
                             , cardOneProp :: Bool 
                             , widthProp :: Int 
                             , vectorSchemaProp :: VectorSchema } deriving (Show)
