module QQ.ListQuoter where

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH
-- import Language.Haskell.Exts.InternalParser

quoteListCompr :: String -> TH.ExpQ
quoteListCompr = transform . parseCompr

quoteListComprPat :: String -> TH.PatQ
quoteListComprPat = undefined

transform e = let r = show e
	       in TH.litE $ TH.stringL r

parseCompr :: String -> Exp
parseCompr = fromParseResult . parseExp . expand

expand :: String -> String
expand e = '[':(e ++ "]")
ferryHaskell :: QuasiQuoter
ferryHaskell = QuasiQuoter quoteListCompr quoteListComprPat 
