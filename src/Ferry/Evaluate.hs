module Ferry.Evaluate where

import Ferry.Data

type Conn = ()

evaluate :: Conn -> Exp -> IO Exp
evaluate = undefined