{-# LANGUAGE TemplateHaskell #-}

module Ferry.Internals.QQ (qc, fp, rw) where

import Ferry.Internals.Impossible

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty

import Data.Generics

import qualified Data.Set as S
import qualified Data.List as L

--REMOVE!!!
import Debug.Trace
import System.IO.Unsafe

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

fp :: QuasiQuoter
fp = QuasiQuoter (return . TH.LitE . TH.StringL . show . parseCompr) undefined

rw :: QuasiQuoter
rw = QuasiQuoter (return . TH.LitE . TH.StringL . prettyPrint . translateListCompr . parseCompr) undefined

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
variablesFrom (QualStmt (Qualifier _)) = PWildCard
variablesFrom (QualStmt (LetStmt (BDecls [PatBind _ p _ _ _]))) = p
variablesFrom (QualStmt e)  = error $ "Not supported yet: " ++ show e
variablesFrom _ = $impossible

patToExp :: Pat -> Exp
patToExp (PVar x)    = var x
patToExp (PTuple [x, y]) = pairF (patToExp x) $ patToExp y
patToExp (PApp (Special UnitCon) []) = Con $ Special UnitCon    
patToExp p           = error $ "Pattern not suppoted by ferry: " ++ show p

translateListCompr :: Exp -> Exp
translateListCompr (ListComp e q) = let pat = variablesFromLst $ reverse q
                                        (x:_) = freshVar $ freeInPat pat
                                        e' = insertProjections (makeProjections pat x) e 
                                        lambda = makeLambda (patV x) (SrcLoc "" 0 0) e'
                                     in mapF lambda (normaliseQuals q)
translateListCompr (ParComp e qs) = let pat = variablesFromLsts qs
                                        (x:_) = freshVar $ freeInPat pat
                                        e' = insertProjections (makeProjections pat x) e 
                                        lambda = makeLambda (patV x) (SrcLoc "" 0 0) e'
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
normaliseQuals' []     = consF unit nilF
normaliseQuals' (q:ps) = let qn = normaliseQual q
                             qv = variablesFrom q
                             pn = normaliseQuals' ps
                             pv = variablesFromLst ps
                          in combine pn pv qn qv

combine :: Exp -> Pat -> Exp -> Pat -> Exp
combine p pv q qv = let qLambda = makeLambda qv (SrcLoc "" 0 0) $ pairF (patToExp qv) $ patToExp pv
                        pLambda = makeLambda pv (SrcLoc "" 0 0) $ mapF qLambda q
                     in concatF (mapF pLambda p)

normaliseQual :: QualStmt -> Exp
normaliseQual (QualStmt (Generator _ _ e)) = e
normaliseQual (QualStmt (Qualifier e)) = If e (consF unit nilF) nilF
normaliseQual (QualStmt (LetStmt (BDecls bi@[PatBind _ p _ _ _]))) = flip consF nilF $ letE bi $ patToExp p
normaliseQual (QualStmt e) = error $ "Not supported (yet): " ++ show e
normaliseQual _ = $impossible

makeLambda :: Pat -> SrcLoc -> Exp -> Exp
makeLambda p s b = let proj = makeProjections' p
                       var = case proj of
                                [] -> p
                                ((x,_):_) -> patV x
                       lambda = Lambda s [var] b
                    in insertProjections proj lambda

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

unit :: Exp
unit = var $ name "Ferry.unit"

fstV :: Exp
fstV = var $ name "Ferry.fst"

sndV :: Exp
sndV = var $ name "Ferry.snd"

pairV :: Exp
pairV = var $ name "Ferry.pair"

pairF :: Exp -> Exp -> Exp
pairF e1 e2 = flip app e2 $ app pairV e1

mapF :: Exp -> Exp -> Exp
mapF f l = flip app l $ app mapV f

consF :: Exp -> Exp -> Exp
consF hd tl = flip app tl $ app consV hd

nilF :: Exp
nilF = nilV

concatF :: Exp -> Exp
concatF = app concatV

nilV :: Exp
nilV = var $ name "Ferry.nil"

consV :: Exp
consV = var $ name "Ferry.cons"

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
unzipB PWildCard   = paren $ makeLambda PWildCard (SrcLoc "" 0 0) $ unit
unzipB p@(PVar x)  = paren $ makeLambda p (SrcLoc "" 0 0) $ var x
unzipB p@(PTuple [xp, yp]) = let (e:x:y:_) = freshVar $ freeInPat p
                                 ePat = patV e
                                 eArg = varV e
                                 xUnfold = unzipB xp
                                 yUnfold = unzipB yp                                 
                              in paren $ makeLambda ePat (SrcLoc "" 0 0) $ 
                                          pairF (app xUnfold $ paren $ mapF fstV eArg) (app yUnfold $ mapF sndV eArg)
unzipB _ = $impossible

freeInPat :: Pat -> S.Set String
freeInPat PWildCard = S.empty
freeInPat (PVar (Ident x))  = S.singleton x
freeInPat (PTuple x) = S.unions $ map freeInPat x
freeInPat _ = $impossible

freshVar :: S.Set String -> [String]
freshVar s = ["__v" ++ show c | c <- [1::Int ..], not (S.member ("__v" ++ show c) s)]

makeProjections' :: Pat -> [(String, Exp)]
makeProjections' PWildCard = []
makeProjections' (PVar (Ident x)) = [(x, varV x)]
makeProjections' (PTuple [x, y]) = let xProj = map (\(v, e) -> (v, app fstV e)) $ makeProjections' x
                                       yProj = map (\(v, e) -> (v, app sndV e)) $ makeProjections' y
                                    in case xProj of
                                         [] -> case yProj of
                                                ((v, p):_) -> altProj yProj v
                                                [] -> []
                                         ((v, p):_) -> altProj xProj v ++ altProj yProj v
    where
     altProj :: [(String, Exp)] -> String -> [(String, Exp)]
     altProj proj v = map (\(y, pr) -> (y, everywhere (mkT (repl y v)) pr)) proj
     repl :: String -> String -> Exp -> Exp
     repl v n' r@(Var (UnQual (Ident n))) | n == v    = Var $ UnQual $ Ident n'
                                          | otherwise = r
     repl _ _ e                                       = e

makeProjections :: Pat -> String-> [(String, Exp)]
makeProjections PWildCard _ = []
makeProjections (PVar (Ident x)) e = [(x, varV e)]
makeProjections (PTuple [x,y]) v = (map (\(v, e) -> (v, app fstV e)) $ makeProjections x v) ++ (map (\(v, e) -> (v, app sndV e)) $ makeProjections y v)
makeProjections _ _ = $impossible 

insertProjections :: [(String, Exp)] -> Exp -> Exp
insertProjections p = everywhere (mkT (insert' p))
 where
    insert' :: [(String, Exp)] -> Exp -> Exp
    insert' assocs v@(Var (UnQual (Ident n))) = case L.lookup n assocs of
                                                Nothing -> v
                                                (Just e) -> e 
    insert' _ e                               = e