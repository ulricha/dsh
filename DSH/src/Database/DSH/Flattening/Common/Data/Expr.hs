-- | Some data types which are common to expressions in CL, NKL and FKL.
module Database.DSH.Flattening.Common.Data.Expr where

import Database.DSH.Flattening.Common.Data.Type

-- | Table columns
type Column = (String, Type)
     
-- | Table keys
type Key = [String]

-- | Identifiers
type Ident = String
