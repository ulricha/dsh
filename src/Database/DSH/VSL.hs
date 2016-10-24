{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VSL
    ( module Database.DSH.VSL.Lang
    , module Database.DSH.VSL.VirtualSegmentAlgebra
    , module Database.DSH.Common.VectorLang
    , module Database.DSH.Translate.VSL2Algebra
    ) where

import           Database.DSH.Common.VectorLang
import           Database.DSH.Translate.Vectorize
import           Database.DSH.VSL.Lang                  (VSL, TVSL, RVSL, SegmentLookup(..))
import           Database.DSH.VSL.Opt.OptimizeVSL
import           Database.DSH.VSL.Vectorize
import           Database.DSH.VSL.VirtualSegmentAlgebra
import           Database.DSH.Translate.VSL2Algebra

instance VectorLang VSL where
    vectorize = vectorizeDelayed
    optimizeVectorPlan = optimizeVSLDefault
