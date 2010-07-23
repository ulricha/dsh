{-# LANGUAGE TemplateHaskell #-}

module Ferry.Combinators.Tuples where

import Ferry.Combinators.TH

-- * Tuple Projection Functions

$(generateProjRange 2 32)

-- * Tuple Construction

$(generateTupleRange 2 32)
