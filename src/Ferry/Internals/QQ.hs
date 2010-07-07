{-# LANGUAGE TemplateHaskell #-}

module Ferry.Internals.QQ (qc) where

import Ferry.Internals.Impossible

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Build

import qualified Data.Set as S

quoteListCompr :: String -> TH.ExpQ
quoteListCompr = transform . parseCompr

quoteListComprPat :: String -> TH.PatQ
quoteListComprPat = undefined

transform :: Exp -> TH.ExpQ
transform e = case translateExtsToTH $ translateListCompr e of
                Left err -> error $ show err
                Right e1 -> return e1

parseCompr :: String -> Exp
parseCompr = fromParseResult . exprParser 

exprParser :: String -> ParseResult Exp
exprParser = parseExpWithMode (defaultParseMode {extensions = [TransformListComp]}) . expand 

expand :: String -> String
expand e = '[':(e ++ "]")

ferryHaskell :: QuasiQuoter
ferryHaskell = QuasiQuoter quoteListCompr quoteListComprPat 

qc :: QuasiQuoter
qc = ferryHaskell

-- fp :: QuasiQuoter
-- fp = QuasiQuoter (return . TH.LitE . TH.StringL . show . parseCompr) undefined

variablesFromLsts :: [[QualStmt]] -> Pat
variablesFromLsts [] = $impossible
variablesFromLsts [x]    = variablesFromLst $ reverse x 
variablesFromLsts (x:xs) = PTuple [variablesFromLst $ reverse x, variablesFromLsts xs]
 

variablesFromLst :: [QualStmt] -> Pat
variablesFromLst ((ThenTrans _):xs) = variablesFromLst xs
variablesFromLst ((ThenBy _ _):xs) = variablesFromLst xs
variablesFromLst ((GroupBy _):xs) = variablesFromLst xs
variablesFromLst ((GroupUsing _):xs) = variablesFromLst xs
variablesFromLst ((GroupByUsing _ _):xs) = variablesFromLst xs
variablesFromLst [x]    = variablesFrom x
variablesFromLst (x:xs) = PTuple [variablesFrom x, variablesFromLst xs]
variablesFromLst []     = PWildCard

variablesFrom :: QualStmt -> Pat
variablesFrom (QualStmt (Generator _ p _)) = p
variablesFrom (QualStmt (Qualifier _)) = PApp (Special UnitCon) []
variablesFrom (QualStmt (LetStmt (BDecls [PatBind _ p _ _ _]))) = p
variablesFrom (QualStmt e)  = error $ "Not supported yet: " ++ show e
variablesFrom _ = $impossible

patToExp :: Pat -> Exp
patToExp (PVar x)    = var x
patToExp (PTuple xs) = Tuple $ map patToExp xs
patToExp (PApp (Special UnitCon) []) = Con $ Special UnitCon    
patToExp p           = error $ "Pattern not suppoted by ferry: " ++ show p

translateListCompr :: Exp -> Exp
translateListCompr (ListComp e q) = let lambda = makeLambda (variablesFromLst $ reverse q) (SrcLoc "" 0 0) e
                                     in mapF lambda (normaliseQuals q)
translateListCompr (ParComp e qs) = let lambda = makeLambda (variablesFromLsts qs) (SrcLoc "" 0 0) e
                                     in mapF lambda (normParallelCompr qs)
translateListCompr l              = error $ "Expr not supported by Ferry: " ++ show l

normParallelCompr :: [[QualStmt]] -> Exp
normParallelCompr [] = $impossible 
normParallelCompr [x] = normaliseQuals x
normParallelCompr (x:xs) = zipF (normaliseQuals x) (normParallelCompr xs)

normaliseQuals :: [QualStmt] -> Exp
normaliseQuals = normaliseQuals' . reverse

{-
The list of qualifiers is provided in reverse order
-}
normaliseQuals' :: [QualStmt] -> Exp
normaliseQuals' ((ThenTrans e):ps) = app e $ normaliseQuals' ps
normaliseQuals' ((ThenBy ef ek):ps) = let pv = variablesFromLst ps
                                          ks = makeLambda pv undefined ek
                                       in app (app ef ks) $ normaliseQuals' ps
normaliseQuals' ((GroupBy e):ps)    = normaliseQuals' ((GroupByUsing e groupWithF):ps)
normaliseQuals' ((GroupByUsing e f):ps) = let pVar = variablesFromLst ps
                                              lambda = makeLambda pVar (SrcLoc "" 0 0) e
                                           in mapF (unzipB pVar) (app (app f lambda) $ normaliseQuals' ps)
normaliseQuals' ((GroupUsing e):ps) = let pVar = variablesFromLst ps
                                       in mapF (unzipB pVar) (app e (normaliseQuals' ps))
normaliseQuals' [q]    = normaliseQual q
normaliseQuals' []     = listE [Con $ Special UnitCon]
normaliseQuals' (q:ps) = let qn = normaliseQual q
                             qv = variablesFrom q
                             pn = normaliseQuals' ps
                             pv = variablesFromLst ps
                          in combine pn pv qn qv

combine :: Exp -> Pat -> Exp -> Pat -> Exp
combine p pv q qv = let qLambda = makeLambda qv (SrcLoc "" 0 0) $ Tuple [patToExp qv, patToExp pv]
                        pLambda = makeLambda pv (SrcLoc "" 0 0) $ mapF qLambda q
                     in concatF (mapF pLambda p)

normaliseQual :: QualStmt -> Exp
normaliseQual (QualStmt (Generator _ _ e)) = e
normaliseQual (QualStmt (Qualifier e)) = If e (listE [Con $ Special UnitCon]) eList
normaliseQual (QualStmt (LetStmt (BDecls bi@[PatBind _ p _ _ _]))) = listE [letE bi (patToExp p)] 
normaliseQual (QualStmt e) = error $ "Not supported (yet): " ++ show e
normaliseQual _ = $impossible

makeLambda :: Pat -> SrcLoc -> Exp -> Exp
makeLambda p s b = Lambda s [p] b

patV :: String -> Pat
patV = PVar . name

varV :: String -> Exp
varV = var . name

-- patF :: String -> Exp
-- patF = 

mapV :: Exp
mapV = var $ name "Ferry.map"

concatV :: Exp
concatV = var $ name "Ferry.concat"

fstV :: Exp
fstV = var $ name "Ferry.fst"

sndV :: Exp
sndV = var $ name "Ferry.snd"

mapF :: Exp -> Exp -> Exp
mapF f l = flip app l $ app mapV f

concatF :: Exp -> Exp
concatF = app concatV

unzipV :: Exp
unzipV = var $ name "Ferry.unzip"

unzipF :: Exp -> Exp
unzipF = app unzipV

zipV :: Exp
zipV = var $ name "Ferry.zip"

zipF :: Exp -> Exp -> Exp
zipF x y = app (app zipV x) y

fstF :: Exp -> Exp
fstF = app fstV

sndF :: Exp -> Exp
sndF = app sndV

sortWithF :: Exp
sortWithF = var $ name "Ferry.sortWith"

groupWithF :: Exp
groupWithF = var $ name "Ferry.groupWith"

unzipB :: Pat -> Exp
unzipB PWildCard   = makeLambda PWildCard (SrcLoc "" 0 0) $ Con $ Special UnitCon
unzipB p@(PVar x)  = makeLambda p (SrcLoc "" 0 0) $ var x
unzipB p@(PTuple [xp, yp]) = let (e:x:y:_) = freshVar $ freeInPat p
                                 ePat = patV e
                                 xUnfold = unzipB xp
                                 yUnfold = unzipB yp
                                 lamPat = PTuple[patV x, patV y]
                                 xBody = varV x
                                 yBody = varV y
                                 eArg = varV e
                                 xLambda = makeLambda lamPat (SrcLoc "" 0 0) xBody
                                 yLambda = makeLambda lamPat (SrcLoc "" 0 0) yBody
                              in makeLambda ePat (SrcLoc "" 0 0) $ 
                                        Tuple [ app xUnfold $ mapF xLambda eArg
                                              , app yUnfold $ mapF yLambda eArg ]
unzipB _ = $impossible

                               
freeInPat :: Pat -> S.Set String
freeInPat PWildCard = S.empty
freeInPat (PVar (Ident x))  = S.singleton x
freeInPat (PTuple x) = S.unions $ map freeInPat x
freeInPat _ = $impossible

freshVar :: S.Set String -> [String]
freshVar s = ["__v" ++ show c | c <- [1::Int ..], S.member ("__v" ++ show c) s]
