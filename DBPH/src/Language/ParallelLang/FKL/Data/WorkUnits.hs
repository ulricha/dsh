{-# LANGUAGE GADTs #-}
module Language.ParallelLang.FKL.Data.WorkUnits where

import qualified Data.List as L    
    
transformUnits :: (a -> b) -> Work a -> Work b
transformUnits f (a, r) = (f a, r)

class Structural a where
--    constantS :: a -> a
    tupleS :: a -> [a]
    listS :: a -> [a]


class Structural a => Reconstructable a where
    idR :: a -> a
    idR = id
    tupleR :: [a] -> a
    listR :: [a] -> a

reconstruct :: Reconstructable a => ReconstructionPlan -> a -> a
reconstruct Id = idR
reconstruct (Tuple rs) = \x -> tupleR [reconstruct r e | (r, e) <- zip rs $ tupleS x] 
reconstruct (Map p) = \x -> listR [reconstruct p e | e <- listS x]
reconstruct Zip = \x -> listR $ map tupleR $ L.transpose $ map listS $ tupleS x 
reconstruct (Compose r1 r2) = (reconstruct r1) . reconstruct r2 

type Work a = (a, ReconstructionPlan)

data ReconstructionPlan where
    Id :: ReconstructionPlan
    Tuple :: [ReconstructionPlan] -> ReconstructionPlan
    Map :: ReconstructionPlan -> ReconstructionPlan
    Zip :: ReconstructionPlan
    Compose :: ReconstructionPlan -> ReconstructionPlan -> ReconstructionPlan
