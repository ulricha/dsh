{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module Ferry.QQ (qc) where

import Paths_Ferry as Ferry
import Ferry.Impossible

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Quote
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.SyntaxTrees.ExtsToTH
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Build
-- import Language.Haskell.Exts.Pretty

import Control.Monad
import Control.Monad.State 
import Control.Applicative

import Data.Generics

import qualified Data.List as L
import Data.Version (showVersion)

combinatorMod :: ModuleName
combinatorMod = ModuleName "ferry.Combinators"

classMod :: ModuleName
classMod = ModuleName "ferry.Class"

{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N = State Int

instance Applicative (State s) where
  pure  = return
  (<*>) = ap

freshVar :: N String
freshVar = do
             i <- get
             put (i + 1)
             return $ "ferryFreshNamesV" ++ show i
     
runN :: N a -> a
runN = fst . flip runState 1


quoteListCompr :: String -> TH.ExpQ
quoteListCompr = transform . parseCompr

quoteListComprPat :: String -> TH.PatQ
quoteListComprPat = undefined

transform :: Exp -> TH.ExpQ
transform e = case translateExtsToTH . runN $ translateListCompr e of
                Left err -> error $ show err
                Right e1 -> return $ globalQuals e1

parseCompr :: String -> Exp
parseCompr = fromParseResult . exprParser

exprParser :: String -> ParseResult Exp
exprParser = parseExpWithMode (defaultParseMode {extensions = [TransformListComp, ViewPatterns]}) . expand

expand :: String -> String
expand e = '[':(e ++ "]")

ferryHaskell :: QuasiQuoter
ferryHaskell = QuasiQuoter quoteListCompr quoteListComprPat

qc :: QuasiQuoter
qc = ferryHaskell

fp :: QuasiQuoter
fp = QuasiQuoter (return . TH.LitE . TH.StringL . show . parseCompr) undefined

rw :: QuasiQuoter
rw = QuasiQuoter (return . TH.LitE . TH.StringL . show . translateExtsToTH . runN . translateListCompr . parseCompr) undefined

translateListCompr :: Exp -> N Exp
translateListCompr (ListComp e q) = do
                                     let pat = variablesFromLst $ reverse q
                                     lambda <- makeLambda pat (SrcLoc "" 0 0) e
                                     (mapF lambda) <$> normaliseQuals q
translateListCompr l              = error $ "Expr not supported by Ferry: " ++ show l

-- Transforming qualifiers

normaliseQuals :: [QualStmt] -> N Exp
normaliseQuals = normaliseQuals' . reverse

normaliseQuals' :: [QualStmt] -> N Exp
normaliseQuals' ((ThenTrans e):ps) = paren . (app e) <$> normaliseQuals' ps
normaliseQuals' ((ThenBy ef ek):ps) = do
                                        let pv = variablesFromLst ps
                                        ks <- makeLambda pv (SrcLoc "" 0 0) ek
                                        app (app ef ks) <$> normaliseQuals' ps
normaliseQuals' ((GroupBy e):ps)    = normaliseQuals' ((GroupByUsing e groupWithF):ps)
normaliseQuals' ((GroupByUsing e f):ps) = do 
                                            let pVar = variablesFromLst ps
                                            lambda <- makeLambda pVar (SrcLoc "" 0 0) e
                                            unzipped <- unzipB pVar
                                            (\x -> mapF unzipped (app (app f lambda) x)) <$> normaliseQuals' ps
normaliseQuals' ((GroupUsing e):ps) = let pVar = variablesFromLst ps
                                       in mapF <$> unzipB pVar <*> (app e <$> normaliseQuals' ps)
normaliseQuals' [q]    = normaliseQual q
normaliseQuals' []     = pure $ consF unit nilF
normaliseQuals' (q:ps) = do
                          qn <- normaliseQual q
                          let qv = variablesFrom q
                          pn <- normaliseQuals' ps
                          let pv = variablesFromLst ps
                          combine pn pv qn qv
                          
normaliseQual :: QualStmt -> N Exp
normaliseQual (QualStmt (Generator _ _ e)) = pure $ e
normaliseQual (QualStmt (Qualifier e)) = pure $ boolF (consF unit nilF) nilF e
normaliseQual (QualStmt (LetStmt (BDecls bi@[PatBind _ p _ _ _]))) = pure $ flip consF nilF $ letE bi $ patToExp p
normaliseQual _ = $impossible

combine :: Exp -> Pat -> Exp -> Pat -> N Exp
combine p pv q qv = do
                     qLambda <- makeLambda qv (SrcLoc "" 0 0) $ fromViewF (tuple [patToExp qv, patToExp pv])
                     pLambda <- makeLambda pv (SrcLoc "" 0 0) $ mapF qLambda q
                     pure $ concatF (mapF pLambda p)
                     
unzipB :: Pat -> N Exp
unzipB PWildCard   = paren <$> makeLambda PWildCard (SrcLoc "" 0 0) unit
unzipB p@(PVar x)  = paren <$> makeLambda p (SrcLoc "" 0 0) (var x)
unzipB p@(PTuple [xp, yp]) = do
                              e <- freshVar
                              let ePat = patV e
                              let eArg = varV e
                              xUnfold <- unzipB xp
                              yUnfold <- unzipB yp
                              (<$>) paren $ makeLambda ePat (SrcLoc "" 0 0) $
                                             fromViewF $ tuple [app xUnfold $ paren $ mapF fstV eArg, app yUnfold $ mapF sndV eArg]
unzipB _ = $impossible


patV :: String -> Pat
patV = PVar . name

varV :: String -> Exp
varV = var . name

-- Building and converting patterns

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

makeLambda :: Pat -> SrcLoc -> Exp -> N Exp
makeLambda p s b = do
                     (p', e') <- mkViewPat p b
                     pure $ Lambda s [p'] e'


mkViewPat :: Pat -> Exp -> N (Pat, Exp)
mkViewPat p@(PVar _)  e = return $ (p, e)
mkViewPat PWildCard   e = return $ (PWildCard, e)
mkViewPat (PTuple ps) e = do
                               x <- freshVar
                               (pr, e') <- foldl viewTup (pure $ ([], e)) ps
                               let px = PVar $ name x
                               let vx = var $ name x
                               let er = caseE (app viewV vx) [alt (SrcLoc "" 0 0) (PTuple $ reverse pr) e']
                               return (px, er) 
                           
mkViewPat (PList ps)  e = do
                            x <- freshVar
                            let px = PVar $ name x
                            let vx = var $ name x
                            let er = caseE (app viewV vx) [alt (SrcLoc "" 0 0) (PList ps) e]
                            return (px, er)
mkViewPat (PParen p)  e = do
                            (p', e') <- mkViewPat p e
                            return (PParen p', e')
mkViewPat p           e = do
                            x <- freshVar
                            let px = PVar $ name x
                            let vx = var $ name x
                            let er = caseE (app viewV vx) [alt (SrcLoc "" 0 0) p e]
                            return (px, er)

viewTup :: N ([Pat], Exp) -> Pat -> N ([Pat], Exp)
viewTup r p = do
                    (rp, re) <- r
                    (p', e') <- mkViewPat p re
                    return (p':rp, e')

viewV :: Exp
viewV = var $ name $ "view"

patToExp :: Pat -> Exp
patToExp (PVar x)                    = var x
patToExp (PTuple [x, y])             = fromViewF $ tuple [patToExp x, patToExp y]
patToExp (PApp (Special UnitCon) []) = unit
patToExp PWildCard                   = unit
patToExp p                           = error $ "Pattern not suppoted by ferry: " ++ show p

-- Ferry Combinators

fstV :: Exp
fstV = qvar combinatorMod $ name "fst"

sndV :: Exp
sndV = qvar combinatorMod $ name "snd"

mapV :: Exp
mapV = qvar combinatorMod $ name "map"

mapF :: Exp -> Exp -> Exp
mapF f l = flip app l $ app mapV f

unit :: Exp
unit = qvar combinatorMod $ name "unit"

consF :: Exp -> Exp -> Exp
consF hd tl = flip app tl $ app consV hd

nilF :: Exp
nilF = nilV

nilV :: Exp
nilV = qvar combinatorMod $ name "nil"

consV :: Exp
consV = qvar combinatorMod $ name "cons"

fromViewV :: Exp
fromViewV = qvar classMod $ name "fromView"

fromViewF :: Exp -> Exp
fromViewF e1 =  app fromViewV e1

concatF :: Exp -> Exp
concatF = app concatV

concatV :: Exp
concatV = qvar combinatorMod $ name "concat"

boolF :: Exp -> Exp -> Exp -> Exp
boolF t e c = app (app ( app (qvar combinatorMod $ name "bool") t) e) c 

groupWithF :: Exp
groupWithF = qvar combinatorMod $ name "groupWith"

-- Generate proper global names from pseudo qualified variables
toNameG :: TH.Name -> TH.Name
toNameG n@(TH.Name (TH.occString -> occN) (TH.NameQ (TH.modString -> m))) =
  if "ferry" `L.isPrefixOf` m 
      then let pkgN = "Ferry-" ++ showVersion (Ferry.version)
               modN =  (:) 'F' $ tail m
            in TH.mkNameG_v pkgN modN occN
      else n
toNameG n = n

globalQuals :: TH.Exp -> TH.Exp
globalQuals = everywhere (mkT toNameG)
