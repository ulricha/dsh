{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             CPP
             #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-orphans #-}

module Ferry.Tuples where

import Ferry.TH
import Ferry.Data
import Ferry.Class

#define N 16


-- * Tuple Instances
-- $inst

{- $inst

This module offers all 'QA', 'TA' and 'View' instances for tuples up to the
defined length.

-}

$(generateDeriveTupleQARange   3 N)
$(generateDeriveTupleTARange   3 N)
$(generateDeriveTupleViewRange 3 N)

-- * Tuple Projection Functions

$(generateProjRange 2 N)

fst :: (QA a, QA b) => Q (a,b) -> Q a
fst = proj_2_1

snd :: (QA a, QA b) => Q (a,b) -> Q b 
snd = proj_2_2

-- * Tuple Construction

$(generateTupleRange 2 N)

pair :: (QA a, QA b) => Q a -> Q b -> Q (a, b)
pair = tuple_2
