-- | Some data types which are common to expressions in CL, NKL and FKL.
module Database.DSH.Common.Data.Expr where

import Database.DSH.Common.Data.Type

-- | Table columns
type Column = (String, Type)
     
-- | Table keys
type Key = [String]

-- | Identifiers
type Ident = String
