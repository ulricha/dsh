module Database.DSH.Common.Kure
  ( -- * Logging
    LogC
  , logR
    -- * Debugging combinators
  , prettyR
  , debug
  , debugPretty
  , debugMsg
  , debugOpt
  , debugPipeR
  , debugTrace
  , debugShow
  ) where

#ifdef DEBUGCOMP
import Debug.Trace
import Text.Printf
#endif

import Language.KURE
import qualified Data.Sequence                as S

import Database.DSH.Common.Pretty
import Database.DSH.Common.RewriteM
import Control.Arrow
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

--------------------------------------------------------------------------------
-- Rewrite logging

type LogC = S.Seq String

logR :: Pretty a => String -> Rewrite c (RewriteM s LogC) a
logR rewriteName = do
    e <- idR
    let msg = char '=' P.<+> braces (text rewriteName) P.<$> pretty e
    constT $ tell $ S.singleton $ pp msg
    return e

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

debugOpt :: Pretty e => String -> e -> Either String e -> e
#ifdef DEBUGCOMP
debugOpt stage origExpr mExpr =
    trace (showOrig origExpr)
    $ either (flip trace origExpr) (\e -> trace (showOpt e) e) mExpr

  where
    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) '=' ++ "\n"

    showOrig :: Pretty e => e -> String
    showOrig e = padSep (printf "Original Query (%s)" stage) ++ pp e ++ padSep ""

    showOpt :: Pretty e => e -> String
    showOpt e = padSep (printf "Optimized Query (%s)" stage) ++ pp e ++ padSep ""
#else
debugOpt _stage origExpr =
    either (const origExpr) id
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

