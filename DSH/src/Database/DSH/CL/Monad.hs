module Database.DSH.CL.Monad(CompM, runCompM, freshName) where

import Control.Applicative
import Control.Monad

import Language.KURE

import Database.DSH.CL.Lang

--------------------------------------------------------------------------------
-- | The rewriting monad. Currently, it only provides fresh names
-- FIXME Figure out how to define a MonadCatch instance and use StateT s KureM
newtype CompM a = CompM {compM :: Int -> (Int, Either String a)}

runCompM :: CompM a -> Either String a
runCompM m = snd (compM m 0)

instance Monad CompM where
  return a = CompM (\n -> (n,Right a))
  (CompM f) >>= gg = CompM $ \ n -> case f n of
                                    (n', Left msg) -> (n', Left msg)
                                    (n', Right a)  -> compM (gg a) n'
  fail msg = CompM (\ n -> (n, Left msg))

instance MonadCatch CompM where

  (CompM st) `catchM` f = CompM $ \ n -> case st n of
                                        (n', Left msg) -> compM (f msg) n'
                                        (n', Right a)  -> (n', Right a)

instance Functor CompM where
  fmap = liftM

instance Applicative CompM where
  pure  = return
  (<*>) = ap

suggestName :: CompM Ident
suggestName = CompM (\n -> ((n+1), Right ("v" ++ show n)))

-- | Generate a fresh name, taking the list of in-scope names as parameter. We
-- assume that every name is bound. Therefore, a name that is not bound is
-- assumed to be fresh.
freshName :: [Ident] -> CompM Ident
freshName vs = do v <- suggestName
                  if v `elem` vs
                    then freshName vs
                    else return v

