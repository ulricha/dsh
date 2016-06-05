{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VSL
    ( module Database.DSH.VSL.Lang
    , module Database.DSH.VSL.VirtualSegmentAlgebra
    , module Database.DSH.Common.VectorLang
    ) where

import           Database.DSH.Common.VectorLang
import           Database.DSH.Translate.Vectorize
import           Database.DSH.VSL.Lang                  (VSL)
import           Database.DSH.VSL.Opt.OptimizeVSL
import           Database.DSH.VSL.Vectorize
import           Database.DSH.VSL.VirtualSegmentAlgebra

instance VectorLang VSL where
    vectorize = vectorizeDelayed
    optimizeVectorPlan = optimizeVSLDefault
