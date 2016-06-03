{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VSL
    ( module Database.DSH.VSL.Lang
    ) where

import           Database.DSH.VSL.Lang            (VSL)
import           Database.DSH.VSL.Opt.OptimizeVSL
import           Database.DSH.VSL.Vectorize
import           Database.DSH.Translate.Vectorize

instance VectorLang VSL where
    vectorize = vectorizeDelayed
    optimizeVectorPlan = optimizeVSLDefault
