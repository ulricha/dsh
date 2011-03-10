-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ) where
    
import Database.DSH.Data as D
import Database.DSH.Impossible (impossible)
import Database.HDBC

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) = evaluate c a >>= (return . fromNorm)
    
