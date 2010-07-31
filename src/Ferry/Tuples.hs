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

$(generateDeriveQARange   3 N)
$(generateDeriveTARange   3 N)
$(generateDeriveViewRange 3 N)

-- * Tuple Projection Functions

fst :: (QA a, QA b) => Q (a,b) -> Q a
fst (Q a) = Q (AppE (VarE "fst") a)

snd :: (QA a, QA b) => Q (a,b) -> Q b 
snd (Q a) = Q (AppE (VarE "snd") a)

-- * Tuple Construction

$(generateTupleRange 2 N)

pair :: (QA a, QA b) => Q a -> Q b -> Q (a, b)
pair = tuple_2
