module Database.DSH.Common.Kure
  ( -- * Logging
    RewriteLog
  , logR
  ) where

import qualified Data.Sequence                as S
import           Language.KURE
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.RewriteM

--------------------------------------------------------------------------------
-- Rewrite logging

type RewriteLog = S.Seq String

logR :: Pretty a => String -> Rewrite c (RewriteM s RewriteLog) a -> Rewrite c (RewriteM s RewriteLog) a
logR rewriteName r = do
    e <- idR
    e' <- r
    let ruleMsg = white (char '=' P.<+> braces (enclose space space (text rewriteName)))
        msg     = pretty e P.<$> ruleMsg P.<$> pretty e'
    constT $ tell $ S.singleton $ pp msg
    return e'

