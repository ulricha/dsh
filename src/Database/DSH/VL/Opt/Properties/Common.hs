module Database.DSH.VL.Opt.Properties.Common where

import Control.Monad

import Database.DSH.VL.Opt.Properties.Types

unpack :: Show a => String -> VectorProp a -> Either String a
unpack _ (VProp b)  = Right b
unpack moduleName p = Left $ "no single vector in " ++ moduleName ++ " " ++ (show p)

mapUnpack :: Show a => String 
             -> VectorProp a
             -> VectorProp a
             -> (a -> a -> VectorProp a) 
             -> Either String (VectorProp a)
mapUnpack moduleName e1 e2 f = let ue1 = unpack moduleName e1
                                   ue2 = unpack moduleName e2
                               in liftM2 f ue1 ue2
                                  
