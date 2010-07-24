{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             CPP
             #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-orphans #-}

module Ferry.Combinators.Tuples where

import Ferry.Combinators.TH

#define N 10


-- * Tuple Instances
-- $inst

{- $inst

This module offers all 'QA', 'TA' and 'View' instances for tuples up to the
defined length.

-}

$(generateDeriveQARange   4 N)
$(generateDeriveTARange   4 N)
$(generateDeriveViewRange 4 N)

-- * Tuple Projection Functions

$(generateProjRange 2 N)

-- * Tuple Construction

$(generateTupleRange 2 N)
