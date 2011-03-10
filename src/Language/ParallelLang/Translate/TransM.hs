{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Language.ParallelLang.Translate.TransM where

import Language.ParallelLang.Common.Data.Config

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

newtype TransM a = TransM (ReaderT Config (State (Int, [String], [String])) a)
    deriving (Monad, Functor)

deriving instance MonadState (Int, [String], [String]) TransM
deriving instance MonadReader Config TransM

withOpt :: Optimisation -> TransM Bool
withOpt o = do
             c <- ask
             return $ o `elem` opt c

getFreshVar :: TransM String
getFreshVar = do
                (v, s, l) <- get
                put (v + 1, s, l)
                return $ "***_FV" ++ show v

instance Applicative TransM where
    pure  = return
    (<*>) = ap

withIterVar :: String -> TransM a -> TransM a
withIterVar n e = do
                    (v, s, l) <- get
                    put (v, n:s, l)
                    e' <- e
                    (v', _, l') <- get
                    put (v', s, l')
                    return e'

withLetVar :: String -> TransM a -> TransM a
withLetVar n e = do
                    (v, s, l) <- get
                    put (v, s, n:l)
                    e' <- e
                    (v', s', _) <- get
                    put (v', s', l)
                    return e'

isIterVar :: String -> TransM Bool
isIterVar v = do 
                (_, vs, _) <- get
                return $ elem v vs

isLetVar :: String -> TransM Bool
isLetVar v = do 
                (_, _, vs) <- get
                return $ elem v vs
                
getLetVars :: TransM [String]
getLetVars = do
               (_, _, vs) <- get
               return vs
               
getIterVars :: TransM [String]
getIterVars = do
               (_, vs, _) <- get
               return vs

runTransform :: Config -> TransM a -> a
runTransform c (TransM e) = fst $ flip runState (0, [], []) $ runReaderT e c