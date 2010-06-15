module QQ.ListQuoter where

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH

quoteListCompr :: String -> TH.ExpQ
quoteListCompr = transform . parseCompr

quoteListComprPat :: String -> TH.PatQ
quoteListComprPat = undefined

transform e = let r = translateExtsToTH e
	       in case r of
	           Left e -> error "Jikes"
		   Right e -> return e

parseCompr :: String -> Exp
parseCompr = fromParseResult . parseExp

ferryHaskell :: QuasiQuoter
ferryHaskell = QuasiQuoter quoteListCompr quoteListComprPat 
