{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs         #-}

module Database.DSH.Common.RewriteM
    ( RewriteM
    , RewriteStateM
    , runRewriteM
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

import Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- | The rewriting monad. Currently, it only provides fresh names
-- FIXME Figure out how to define a MonadCatch instance and use StateT s RewriteM
newtype RewriteM s a = RewriteM { compM :: s -> (s, Either String a) }

-- | A variant of RewriteM which adds extra state to the
-- name-generating counter.
type RewriteStateM s = RewriteM (Int, s)

runRewriteM :: RewriteM Int a -> Either String a
runRewriteM m = snd (compM m 0)

runRewriteM' :: s -> RewriteM s a -> (s, Either String a)
runRewriteM' s m = compM m s

instance Monad (RewriteM s) where
  return = returnM
  (>>=)  = bindM
  fail   = failM
  
returnM :: a -> RewriteM s a
returnM a = RewriteM (\n -> (n, Right a))
{-# INLINE returnM #-}
  
bindM :: RewriteM s a -> (a -> RewriteM s b) -> RewriteM s b
bindM (RewriteM f) gg = RewriteM $ \ n -> case f n of
                                    (n', Left msg) -> (n', Left msg)
                                    (n', Right a)  -> compM (gg a) n'
{-# INLINE bindM #-}                                    
                                    
failM :: String -> RewriteM s a
failM msg = RewriteM (\n -> (n, Left msg))
{-# INLINE failM #-}

instance MonadCatch (RewriteM s) where
    catchM = catchRewriteM

catchRewriteM :: RewriteM s a -> (String -> RewriteM s a) -> RewriteM s a
catchRewriteM (RewriteM st) f = RewriteM $ \ n -> case st n of
                                        (n', Left msg) -> compM (f msg) n'
                                        (n', Right a)  -> (n', Right a)
{-# INLINE catchRewriteM #-}                                        


instance Functor (RewriteM s) where
  fmap = liftM

instance Applicative (RewriteM s) where
  pure  = return
  (<*>) = ap

suggestName :: RewriteM Int Ident
suggestName = RewriteM (\n -> ((n+1), Right ("v" ++ show n)))

-- | Generate a fresh name, taking the list of in-scope names as parameter. We
-- assume that every name is bound. Therefore, a name that is not bound is
-- assumed to be fresh.
freshName :: [Ident] -> RewriteM Int Ident
freshName vs = do v <- suggestName
                  if v `elem` vs
                    then freshName vs
                    else return v
                    
suggestName' :: RewriteStateM s Ident
suggestName' = RewriteM (\(n, s) -> ((n+1, s), Right ("v" ++ show n)))

freshNameS :: [Ident] -> RewriteStateM s Ident
freshNameS vs = do v <- suggestName'
                   if v `elem` vs
                     then freshNameS vs
                     else return v
                     
get :: RewriteStateM s s
get = RewriteM $ \(i, s) -> ((i, s), Right s)
{-# INLINE get #-}

put :: s -> RewriteStateM s ()
put s = RewriteM $ \(i, _) -> ((i, s), Right ())
{-# INLINE put #-}

modify :: (s -> s) -> RewriteStateM s ()
modify f = RewriteM $ \(i, s) -> ((i, f s), Right ())
{-# INLINE modify #-}

stateful :: s -> RewriteStateM s a -> RewriteM Int (s, a)
stateful s ma = RewriteM $ \i -> 
               case runRewriteM' (i, s) ma of
                   ((i', _), Left msg) -> (i', Left msg)
                   ((i', s'), Right a) -> (i', Right (s', a))
                   
liftstate :: RewriteM Int a -> RewriteStateM s a
liftstate ma = RewriteM $ \(i, s) -> let (i', a) = runRewriteM' i ma
                                  in ((i', s), a)
                   

-- runRewriteM' (i, s) (ma :: RewriteM (Int, s) a) :: ((i', s'), 

{-
type FooM s = StateT s RewriteM

-- automatic due to StateT
-- instance Monad ...

instance MonadCatch (FooM s) where
    ma `catchM` f = StateT $ \s ->
                        let (ka, s') = runStateT ma s
                        in runRewriteM (return . return) undefined ka
-}                        
