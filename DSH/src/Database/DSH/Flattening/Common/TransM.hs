{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Database.DSH.Flattening.Common.TransM where

import Control.Applicative
import Control.Monad
import Control.Monad.State

newtype TransM a = TransM (State Int a)
    deriving (Monad, Functor)

deriving instance MonadState Int TransM

getFreshVar :: TransM String
getFreshVar = do
                v <- get
                put $ v + 1
                return $ "***_FV" ++ show v

instance Applicative TransM where
    pure  = return
    (<*>) = ap

runTransform :: TransM a -> a
runTransform (TransM e) = fst $ flip runState 0 e
