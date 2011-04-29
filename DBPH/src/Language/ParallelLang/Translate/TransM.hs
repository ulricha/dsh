{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Language.ParallelLang.Translate.TransM where

import Language.ParallelLang.Common.Data.Config

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

newtype TransM a = TransM (ReaderT Config (State (Int, [String])) a)
    deriving (Monad, Functor)

deriving instance MonadState (Int, [String]) TransM
deriving instance MonadReader Config TransM

withOpt :: Optimisation -> TransM Bool
withOpt o = do
             c <- ask
             return $ o `elem` opt c

getFreshVar :: TransM String
getFreshVar = do
                (v, l) <- get
                put (v + 1, l)
                return $ "***_FV" ++ show v

instance Applicative TransM where
    pure  = return
    (<*>) = ap

withCleanLetEnv :: TransM a -> TransM a
withCleanLetEnv e = do
                     (v, l) <- get
                     put (v, [])
                     e' <- e
                     (v', _) <- get
                     put (v', l)
                     return e'

withLetVar :: String -> TransM a -> TransM a
withLetVar n e = do
                    (v, l) <- get
                    put (v, n:l)
                    e' <- e
                    (v', _) <- get
                    put (v', l)
                    return e'

isLetVar :: String -> TransM Bool
isLetVar v = do 
                (_, vs) <- get
                return $ elem v vs
                
getLetVars :: TransM [String]
getLetVars = do
               (_, vs) <- get
               return vs
               
runTransform :: Config -> TransM a -> a
runTransform c (TransM e) = fst $ flip runState (0, []) $ runReaderT e c