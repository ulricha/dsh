{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs         #-}

module Database.DSH.CL.Monad
    ( CompM
    , CompSM
    , runCompM
    , freshName
    , freshNameS
    , put
    , get
    , modify
    , stateful
    , liftstate
    ) where

import Control.Applicative
import Control.Monad
       
import Language.KURE

import Database.DSH.CL.Lang

--------------------------------------------------------------------------------
-- | The rewriting monad. Currently, it only provides fresh names
-- FIXME Figure out how to define a MonadCatch instance and use StateT s KureM
newtype CompM s a = CompM { compM :: s -> (s, Either String a) }

type CompSM s = CompM (Int, s)

runCompM :: CompM Int a -> Either String a
runCompM m = snd (compM m 0)

runCompM' :: s -> CompM s a -> (s, Either String a)
runCompM' s m = compM m s

instance Monad (CompM s) where
  return = returnM
  (>>=)  = bindM
  fail   = failM
  
returnM :: a -> CompM s a
returnM a = CompM (\n -> (n, Right a))
{-# INLINE returnM #-}
  
bindM :: CompM s a -> (a -> CompM s b) -> CompM s b
bindM (CompM f) gg = CompM $ \ n -> case f n of
                                    (n', Left msg) -> (n', Left msg)
                                    (n', Right a)  -> compM (gg a) n'
{-# INLINE bindM #-}                                    
                                    
failM :: String -> CompM s a
failM msg = CompM (\n -> (n, Left msg))
{-# INLINE failM #-}

instance MonadCatch (CompM s) where
    catchM = catchCompM

catchCompM :: CompM s a -> (String -> CompM s a) -> CompM s a
catchCompM (CompM st) f = CompM $ \ n -> case st n of
                                        (n', Left msg) -> compM (f msg) n'
                                        (n', Right a)  -> (n', Right a)
{-# INLINE catchCompM #-}                                        


instance Functor (CompM s) where
  fmap = liftM

instance Applicative (CompM s) where
  pure  = return
  (<*>) = ap

suggestName :: CompM Int Ident
suggestName = CompM (\n -> ((n+1), Right ("v" ++ show n)))

-- | Generate a fresh name, taking the list of in-scope names as parameter. We
-- assume that every name is bound. Therefore, a name that is not bound is
-- assumed to be fresh.
freshName :: [Ident] -> CompM Int Ident
freshName vs = do v <- suggestName
                  if v `elem` vs
                    then freshName vs
                    else return v
                    
suggestName' :: CompSM s Ident
suggestName' = CompM (\(n, s) -> ((n+1, s), Right ("v" ++ show n)))

freshNameS :: [Ident] -> CompSM s Ident
freshNameS vs = do v <- suggestName'
                   if v `elem` vs
                     then freshNameS vs
                     else return v

get :: CompSM s s
get = CompM $ \(i, s) -> ((i, s), Right s)
{-# INLINE get #-}

put :: s -> CompSM s ()
put s = CompM $ \(i, _) -> ((i, s), Right ())
{-# INLINE put #-}

modify :: (s -> s) -> CompSM s ()
modify f = CompM $ \(i, s) -> ((i, f s), Right ())
{-# INLINE modify #-}

stateful :: s -> CompSM s a -> CompM Int (s, a)
stateful s ma = CompM $ \i -> 
               case runCompM' (i, s) ma of
                   ((i', _), Left msg) -> (i', Left msg)
                   ((i', s'), Right a) -> (i', Right (s', a))
                   
liftstate :: CompM Int a -> CompSM s a
liftstate ma = CompM $ \(i, s) -> let (i', a) = runCompM' i ma
                                  in ((i', s), a)
                   

-- runCompM' (i, s) (ma :: CompM (Int, s) a) :: ((i', s'), 

{-
type FooM s = StateT s KureM

-- automatic due to StateT
-- instance Monad ...

instance MonadCatch (FooM s) where
    ma `catchM` f = StateT $ \s ->
                        let (ka, s') = runStateT ma s
                        in runKureM (return . return) undefined ka
-}                        
