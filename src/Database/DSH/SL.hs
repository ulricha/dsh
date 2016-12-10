{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.SL
    ( module Database.DSH.SL.Lang
    , module Database.DSH.SL.SegmentAlgebra
    , module Database.DSH.Translate.SL2Algebra
    , module Database.DSH.Common.VectorLang
    , module Database.DSH.Common.Nat
    ) where

import           Database.DSH.Common.VectorLang
import           Database.DSH.Common.Nat
import           Database.DSH.SL.Lang              (RSL, SL, TSL)
import           Database.DSH.SL.Opt.OptimizeSL
import           Database.DSH.SL.SegmentAlgebra
import qualified Database.DSH.SL.Vectorize         as Vectorize
import           Database.DSH.Translate.SL2Algebra (VecBuild, runVecBuild,
                                                    vl2Algebra)
import           Database.DSH.Translate.Vectorize

instance VectorLang SL where
    vectorize = Vectorize.vectorize
    optimizeVectorPlan = optimizeSLDefault
