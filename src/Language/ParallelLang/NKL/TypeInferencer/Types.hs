{-# LANGUAGE TypeSynonymInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Language.ParallelLang.NKL.TypeInferencer.Types
    (AlgW, runAlgW, getGamma, getSubst, putSubst, freshTyVar, lookupVariable, addToEnv, 
     updateSubstitution, localAddSubstitution, applyS, applySubst) where
    
import Language.ParallelLang.Common.Data.Type

import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative hiding (Const(..))

import qualified Data.Map as M

newtype AlgW a = AlgW (ReaderT TyEnv (State (Int, Subst)) a)
    deriving (Monad, Functor)
    
deriving instance MonadState (Int, Subst) AlgW

deriving instance MonadReader (TyEnv) AlgW

instance Applicative (AlgW) where
  pure  = return
  (<*>) = ap

unpack :: AlgW a -> ReaderT TyEnv (State (Int, Subst)) a
unpack (AlgW a) = a

runAlgW :: Substitutable a => TyEnv -> AlgW a -> a
runAlgW gam a = x
   where
    (x, (_, _)) = runState (runReaderT (unpack $ applyS a) gam) (1, (M.empty))

getGamma :: AlgW TyEnv
getGamma = applyS ask
            

getSubst :: AlgW Subst
getSubst = liftM snd get

putSubst :: Subst -> AlgW ()
putSubst s = do
             (i, _) <- get
             put (i, s)

freshTyVar :: AlgW String 
freshTyVar = do
                (n, theta) <- get
                put (n + 1, theta)
                return (show n)

lookupVariable :: String -> AlgW TypeScheme
lookupVariable i = do 
                    g <- getGamma
                    return $ g i

addToEnv :: String -> TypeScheme -> AlgW a -> AlgW a
addToEnv x t a = do
                  local (\g v -> if x == v then t else g v) a

updateSubstitution :: String -> Type -> AlgW ()
updateSubstitution v t = do
                            (i, s) <- get
                            let s' = addSubstitution s v t
                            put (i, s')

localAddSubstitution :: Substitutable a => String -> Type -> AlgW a -> AlgW a
localAddSubstitution i t l = do
                            s <- getSubst
                            updateSubstitution i t
                            v <- applyS l
                            putSubst s
                            return v

applyS :: Substitutable a => AlgW a -> AlgW a
applyS v = do
             s <- getSubst
             v' <- v
             return $ apply s v'
             
applySubst :: Substitutable a => a -> AlgW a
applySubst v = applyS $ pure v