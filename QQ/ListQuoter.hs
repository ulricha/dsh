module QQ.ListQuoter where

import Prelude hiding (unzip)
import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH
import Language.Haskell.Exts.Build
import GHC.Exts


quoteListCompr :: String -> TH.ExpQ
quoteListCompr = transform . parseCompr

quoteListComprPat :: String -> TH.PatQ
quoteListComprPat = undefined

transform e = case translateExtsToTH $ translateListCompr e of
                Left err -> error $ show err
                Right e -> return e

parseCompr :: String -> Exp
parseCompr = fromParseResult . parseExp . expand

expand :: String -> String
expand e = '[':(e ++ "]")
ferryHaskell :: QuasiQuoter
ferryHaskell = QuasiQuoter quoteListCompr quoteListComprPat 

fh :: QuasiQuoter
fh = ferryHaskell


variablesFromLst :: [QualStmt] -> Pat
variablesFromLst [x]    = variablesFrom x
variablesFromLst (x:xs) = PTuple [variablesFrom x, variablesFromLst xs]

variablesFrom :: QualStmt -> Pat
variablesFrom (QualStmt (Generator loc p e)) = p

patToExp :: Pat -> Exp
patToExp (PVar x)    = var x
patToExp (PTuple xs) = Tuple $ map patToExp xs
patToExp p           = error $ "Pattern not suppoted by ferry: " ++ show p

translateListCompr :: Exp -> Exp
translateListCompr (ListComp e q) = let lambda = makeLambda (variablesFromLst $ reverse q) undefined e
                                    in mapF lambda (normaliseQuals q)
translateListCompr l              = error $ "Expr not supported by Ferry: " ++ show l

normaliseQuals :: [QualStmt] -> Exp
normaliseQuals = normaliseQuals' . reverse

{-
The list of qualifiers is provided in reverse order
-}
normaliseQuals' :: [QualStmt] -> Exp
normaliseQuals' [q]    = normaliseQual q
normaliseQuals' ((QualStmt (Generator s p e)):ps) = let pPat = variablesFromLst ps
                                                        qLambda = makeLambda p s $ Tuple [patToExp p, patToExp pPat]
                                                        pLambda = makeLambda pPat s $ mapF qLambda e
                                                     in concatF (mapF pLambda $ normaliseQuals' ps) 

normaliseQual :: QualStmt -> Exp
normaliseQual (QualStmt (Generator l p e)) = e

makeLambda :: Pat -> SrcLoc -> Exp -> Exp
makeLambda p s b = Lambda s [p] b

mapV :: Exp
mapV = var $ name "map"

concatV :: Exp
concatV = var $ name "concat"

mapF :: Exp -> Exp -> Exp
mapF f l = flip app l $ app mapV f

concatF :: Exp -> Exp
concatF = app concatV
