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

import Control.Monad
import Data.Monoid

import Language.KURE

import Database.DSH.Common.Lang(Ident)

--------------------------------------------------------------------------------
-- | The rewriting monad. Currently, it only provides fresh names
-- FIXME Figure out how to define a MonadCatch instance and use StateT s KureM
newtype CompM s w a = CompM { compM :: s -> (s, Either String (a, w)) }

type CompSM s w = CompM (Int, s) w

runCompM :: CompM Int w a -> Either String (a, w)
runCompM m = snd (compM m 0)

runCompM' :: s -> CompM s w a -> (s, Either String (a, w))
runCompM' s m = compM m s

instance Monoid w => Monad (CompM s w) where
    return = returnM
    (>>=)  = bindM
    fail   = failM

instance Monoid w => Functor (CompM s w) where
    fmap = liftM

instance Monoid w => Applicative (CompM s w) where
    pure  = return
    (<*>) = ap

returnM :: Monoid w => a -> CompM s w a
returnM a = CompM (\n -> (n, Right (a, mempty)))
{-# INLINE returnM #-}

bindM :: Monoid w => CompM s w a -> (a -> CompM s w b) -> CompM s w b
bindM (CompM f) gg = CompM $ \ n -> case f n of
                                    (n', Left msg) -> (n', Left msg)
                                    (n', Right (a, w))  ->
                                        case compM (gg a) n' of
                                            (n'', Left msg') -> (n'', Left msg')
                                            (n'', Right (b, w')) -> (n'', Right (b, w <> w'))
{-# INLINE bindM #-}

failM :: String -> CompM s w a
failM msg = CompM (\n -> (n, Left msg))
{-# INLINE failM #-}

instance Monoid w => MonadCatch (CompM s w) where
    catchM = catchCompM

catchCompM :: CompM s w a -> (String -> CompM s w a) -> CompM s w a
catchCompM (CompM st) f = CompM $ \ n -> case st n of
                                        (n', Left msg) -> compM (f msg) n'
                                        (n', Right a)  -> (n', Right a)
{-# INLINE catchCompM #-}

suggestName :: Monoid w => CompM Int w Ident
suggestName = CompM (\n -> (n+1, Right ("v" ++ show n, mempty)))

-- | Generate a fresh name, taking the list of in-scope names as parameter. We
-- assume that every name is bound. Therefore, a name that is not bound is
-- assumed to be fresh.
freshName :: Monoid w => [Ident] -> CompM Int w Ident
freshName vs = do v <- suggestName
                  if v `elem` vs
                    then freshName vs
                    else return v

suggestName' :: Monoid w => CompSM s w Ident
suggestName' = CompM (\(n, s) -> ((n+1, s), Right ("v" ++ show n, mempty)))

freshNameS :: Monoid w => [Ident] -> CompSM s w Ident
freshNameS vs = do v <- suggestName'
                   if v `elem` vs
                     then freshNameS vs
                     else return v

get :: Monoid w => CompSM s w s
get = CompM $ \(i, s) -> ((i, s), Right (s, mempty))
{-# INLINE get #-}

put :: Monoid w => s -> CompSM s w ()
put s = CompM $ \(i, _) -> ((i, s), Right ((), mempty))
{-# INLINE put #-}

modify :: Monoid w => (s -> s) -> CompSM s w ()
modify f = CompM $ \(i, s) -> ((i, f s), Right ((), mempty))
{-# INLINE modify #-}

stateful :: s -> CompSM s w a -> CompM Int w (s, a)
stateful s ma = CompM $ \i ->
               case runCompM' (i, s) ma of
                   ((i', _), Left msg) -> (i', Left msg)
                   ((i', s'), Right (a, w)) -> (i', Right ((s', a), w))

liftstate :: CompM Int w a -> CompSM s w a
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
