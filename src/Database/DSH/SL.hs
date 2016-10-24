{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.SL
    ( module Database.DSH.SL.Lang
    , module Database.DSH.SL.SegmentAlgebra
    , module Database.DSH.Translate.SL2Algebra
    , module Database.DSH.Common.VectorLang
    ) where

import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang              (TSL)
import           Database.DSH.SL.Opt.OptimizeSL
import           Database.DSH.SL.SegmentAlgebra
import qualified Database.DSH.SL.Vectorize         as Vectorize
import           Database.DSH.Translate.SL2Algebra (VecBuild, runVecBuild,
                                                    vl2Algebra)
import           Database.DSH.Translate.Vectorize

instance VectorLang TSL where
    vectorize = Vectorize.vectorize
    optimizeVectorPlan = optimizeSLDefault
