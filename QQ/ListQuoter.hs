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
variablesFrom (QualStmt (Qualifier e)) = PApp (Special UnitCon) []
variablesFrom (QualStmt (LetStmt (BDecls [PatBind s p t r b]))) = p
variablesFrom (QualStmt e)  = error $ "Not supported yet: " ++ show e

patToExp :: Pat -> Exp
patToExp (PVar x)    = var x
patToExp (PTuple xs) = Tuple $ map patToExp xs
patToExp (PApp (Special UnitCon) []) = Con $ Special UnitCon    
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
normaliseQuals' (q:ps) = let qn = normaliseQual q
                             qv = variablesFrom q
                             pn = normaliseQuals' ps
                             pv = variablesFromLst ps
                          in combine pn pv qn qv

combine :: Exp -> Pat -> Exp -> Pat -> Exp
combine p pv q qv = let qLambda = makeLambda qv undefined $ Tuple [patToExp qv, patToExp pv]
                        pLambda = makeLambda pv undefined $ mapF qLambda q
                     in concatF (mapF pLambda p)

normaliseQual :: QualStmt -> Exp
normaliseQual (QualStmt (Generator l p e)) = e
normaliseQual (QualStmt (Qualifier e)) = If e (listE [Con $ Special UnitCon]) eList
normaliseQual (QualStmt (LetStmt (BDecls bi@[PatBind s p t r b]))) = listE [letE bi (patToExp p)] 
normaliseQual (QualStmt e) = error $ "Not supported (yet): " ++ show e

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
