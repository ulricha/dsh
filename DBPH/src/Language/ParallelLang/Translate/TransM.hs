{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Language.ParallelLang.Translate.TransM where

import Control.Applicative
import Control.Monad
import Control.Monad.State

newtype TransM a = TransM (State (Int, [String]) a)
    deriving (Monad, Functor)

deriving instance MonadState (Int, [String]) TransM

getFreshVar :: TransM String
getFreshVar = do
                (v, l) <- get
                put (v + 1, l)
                return $ "***_FV" ++ show v

instance Applicative TransM where
    pure  = return
    (<*>) = ap

withClosure :: [String] -> TransM a -> TransM a
withClosure xs e = do
                    (v, l) <- get
                    put (v, xs)
                    e' <- e
                    (v', _) <- get
                    put (v', l)
                    return e'

withCleanClosureEnv :: TransM a -> TransM a
withCleanClosureEnv e = do
                     (v, l) <- get
                     put (v, [])
                     e' <- e
                     (v', _) <- get
                     put (v', l)
                     return e'

withVar :: String -> TransM a -> TransM a
withVar n e = do
                    (v, l) <- get
                    put (v, n:l)
                    e' <- e
                    (v', _) <- get
                    put (v', l)
                    return e'

isClosureVar :: String -> TransM Bool
isClosureVar v = do 
                (_, vs) <- get
                return $ elem v vs
                
getClosureVars :: TransM [String]
getClosureVars = do
               (_, vs) <- get
               return vs
               
runTransform :: TransM a -> a
runTransform (TransM e) = fst $ flip runState (0, []) e
