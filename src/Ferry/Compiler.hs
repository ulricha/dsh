module Ferry.Compiler (evaluate) where

import Ferry.Data
import Ferry.Syntax
import Ferry.Compiler.Transform
-- import Ferry.Impossible

-- import Data.Convertible
import Database.HDBC

{-
N monad, version of the state monad that can provide fresh variable names.
-}
newtype N a = N (State Int a)

unwrapN :: N a -> State Int a
unwrapN (N s) = s

instance Functor N where
    fmap f a = N $ fmap f $ unwrapN a

instance Monad N where
    s >>= m = N (unwrapN s >>= unwrapN . m)
    return = N . return
    
instance Applicative N where
  pure  = return
  (<*>) = ap

freshVar :: N String
freshVar = N $ do
                i <- get
                put (i + 1)
                return $ "__fv" ++ show i
     
runN :: N a -> a
runN = fst . (flip runState 1) . unwrapN

evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> Exp
         -> IO Norm
evaluate = undefined