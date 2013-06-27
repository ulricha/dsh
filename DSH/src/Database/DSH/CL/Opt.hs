{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt 
  ) where
       
import           Debug.Trace
import           Text.Printf
                 
import qualified Data.Set as S

import           Database.DSH.Common.Data.Val
import           Database.DSH.Common.Data.Op
import           Database.DSH.CL.Lang
       
opt :: Expr -> Expr
opt e = if (e /= e') 
        then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
        else trace (show e) e'
  where e' = e
