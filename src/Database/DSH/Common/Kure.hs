module Database.DSH.Common.Kure
  ( -- * Debugging combinators
    prettyR
  , debug
  , debugPretty
  , debugMsg
  , debugOpt
  , debugPipeR
  , debugTrace
  , debugShow
  ) where

import Language.KURE
import Database.DSH.Common.Pretty
import Control.Arrow

--------------------------------------------------------------------------------
-- Simple debugging combinators

-- | Trace output of the value being rewritten; use for debugging only.
prettyR :: (Monad m, Pretty a) => String -> Rewrite c m a
#ifdef DEBUGCOMP
prettyR msg = acceptR (\a -> trace (msg ++ pp a) True)
#else
prettyR _ = idR
#endif

debug :: Pretty a => String -> a -> b -> b
#ifdef DEBUGCOMP
debug msg a b = trace ("\n" ++ msg ++ " =>\n" ++ pp a) b
#else
debug _ _ b = b
#endif

debugPretty :: (Pretty a, Monad m) => String -> a -> m ()
debugPretty msg a = debug msg a (return ())

debugMsg :: Monad m => String -> m ()
#ifdef DEBUGCOMP
debugMsg msg = trace msg $ return ()
#else
debugMsg _ = return ()
#endif

debugOpt :: Pretty e => e -> Either String e -> e
debugOpt origExpr mExpr = 
#ifdef DEBUGCOMP
    trace (showOrig origExpr)
    $ either (flip trace origExpr) (\e -> trace (showOpt e) e) mExpr

  where
    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) '=' ++ "\n"

    showOrig :: Pretty e => e -> String
    showOrig e = padSep "Original Query" ++ pp e ++ padSep ""

    showOpt :: Pretty e => e -> String
    showOpt e = padSep "Optimized Query" ++ pp e ++ padSep ""
#else
    either (const origExpr) id mExpr
#endif

debugPipeR :: (Monad m, Pretty a) => Rewrite c m a -> Rewrite c m a
debugPipeR r = prettyR "Before >>>>>>"
               >>> r
               >>> prettyR ">>>>>>> After"

debugTrace :: Monad m => String -> Rewrite c m a
#ifdef DEBUGCOMP
debugTrace msg = trace msg idR
#else
debugTrace _ = idR
#endif

debugShow :: (Monad m, Pretty a) => String -> Rewrite c m a
#ifdef DEBUGCOMP
debugShow msg = prettyR (msg ++ "\n")
#else
debugShow _ = idR
#endif

