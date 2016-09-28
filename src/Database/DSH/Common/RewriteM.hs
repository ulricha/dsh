{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | The Rewrite monad for KURE-based rewriting systems in DSH.
module Database.DSH.Common.RewriteM
    ( RewriteM
    , RewriteStateM
    , runRewriteM
    , freshName
    , freshNameS
    , tell
    , put
    , get
    , modify
    , stateful
    , liftstate
    ) where

import           Control.Monad
import           Data.Monoid
import           Language.KURE

import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- | The rewriting monad. Currently, it only provides fresh names
-- FIXME Figure out how to define a MonadCatch instance and use StateT s KureM
newtype RewriteM s w a = RewriteM { compM :: s -> (s, Either String (a, w)) }

-- | A variant of RewriteM which adds extra state to the name-generating
-- counter.
type RewriteStateM s w = RewriteM (Int, s) w

-- | Run a rewrite. Return either the error message if it fails or the rewritten
-- result and the log if it succeeds.
runRewriteM :: RewriteM Int w a -> Either String (a, w)
runRewriteM m = snd (compM m 0)

runRewriteM' :: s -> RewriteM s w a -> (s, Either String (a, w))
runRewriteM' s m = compM m s

instance Monoid w => Monad (RewriteM s w) where
  return = returnM
  {-# INLINE return #-}
  (>>=)  = bindM
  {-# INLINE (>>=) #-}
  fail   = failM
  {-# INLINE fail #-}

returnM :: Monoid w => a -> RewriteM s w a
returnM a = RewriteM (\n -> (n, Right (a, mempty)))
{-# INLINE returnM #-}

bindM :: Monoid w => RewriteM s w a -> (a -> RewriteM s w b) -> RewriteM s w b
bindM (RewriteM f) gg = RewriteM $ \ n -> case f n of
                                    (!n', Left !msg)       -> (n', Left msg)
                                    (!n', Right (!a, !w))  ->
                                        case compM (gg a) n' of
                                            (!n'', Left !msg')      -> (n'', Left msg')
                                            (!n'', Right (!b, !w')) -> (n'', Right (b, w <> w'))
{-# INLINE bindM #-}

failM :: String -> RewriteM s w a
failM msg = RewriteM (\n -> (n, Left msg))
{-# INLINE failM #-}

instance Monoid w => MonadCatch (RewriteM s w) where
    catchM = catchRewriteM
    {-# INLINE catchM #-}

catchRewriteM :: RewriteM s w a -> (String -> RewriteM s w a) -> RewriteM s w a
catchRewriteM (RewriteM st) f = RewriteM $ \ n -> case st n of
                                        (!n', Left !msg)       -> compM (f msg) n'
                                        (!n', Right (!a, !w))  -> (n', Right (a, w))
{-# INLINE catchRewriteM #-}

instance Monoid w => Functor (RewriteM s w) where
  fmap = liftM
  {-# INLINE fmap #-}

instance Monoid w => Applicative (RewriteM s w) where
  pure  = return
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

suggestName :: Monoid w => RewriteM Int w Ident
suggestName = RewriteM (\n -> (n+1, Right ("v" ++ show n, mempty)))

-- | Generate a fresh name, taking the list of in-scope names as parameter. We
-- assume that every name is bound. Therefore, a name that is not bound is
-- assumed to be fresh.
freshName :: Monoid w => [Ident] -> RewriteM Int w Ident
freshName vs = do v <- suggestName
                  if v `elem` vs
                    then freshName vs
                    else return v

suggestName' :: Monoid w => RewriteStateM s w Ident
suggestName' = RewriteM (\(!n, !s) -> ((n+1, s), Right ("v" ++ show n, mempty)))

freshNameS :: Monoid w => [Ident] -> RewriteStateM s w Ident
freshNameS vs = do v <- suggestName'
                   if v `elem` vs
                     then freshNameS vs
                     else return v

-- | Log a debug message
tell :: w -> RewriteM s w ()
tell w = RewriteM $ \s -> (s, Right ((), w))
{-# INLINE tell #-}

get :: Monoid w => RewriteStateM s w s
get = RewriteM $ \(!i, !s) -> ((i, s), Right (s, mempty))
{-# INLINE get #-}

put :: Monoid w => s -> RewriteStateM s w ()
put s = RewriteM $ \(!i, _) -> ((i, s), Right ((), mempty))
{-# INLINE put #-}

modify :: Monoid w => (s -> s) -> RewriteStateM s w ()
modify f = RewriteM $ \(!i, !s) -> ((i, f s), Right ((), mempty))
{-# INLINE modify #-}

stateful :: s -> RewriteStateM s w a -> RewriteM Int w (s, a)
stateful s ma = RewriteM $ \i ->
               case runRewriteM' (i, s) ma of
                   ((!i', _), Left !msg)        -> (i', Left msg)
                   ((!i', !s'), Right (!a, !w)) -> (i', Right ((s', a), w))

liftstate :: RewriteM Int w a -> RewriteStateM s w a
liftstate ma = RewriteM $ \(!i, !s) -> let (!i', !a) = runRewriteM' i ma
                                       in ((i', s), a)

