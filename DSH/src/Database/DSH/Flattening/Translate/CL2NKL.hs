module Database.DSH.Flattening.Translate.CL2NKL where

import qualified Database.DSH.Flattening.CL.Lang as CL
import qualified Database.DSH.Flattening.NKL.Data.NKL as NKL

-- | Express comprehensions in NKL iteration constructs map and concatMap.
desugarComprehensions :: CL.Expr -> NKL.Expr
desugarComprehensions = undefined
