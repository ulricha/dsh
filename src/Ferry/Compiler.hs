module Ferry.Compiler (evaluate) where

import Ferry.Data
-- import Ferry.Impossible

-- import Data.Convertible
import Database.HDBC

evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> Exp
         -> IO Norm
evaluate = undefined