{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Frontend.TupleTypes where

import           Control.Applicative
import           Data.List
import           Text.Printf

import           Language.Haskell.TH

--------------------------------------------------------------------------------
-- Tuple Accessors

-- | Generate all constructors for a given tuple width.
mkTupElemCons :: Name -> Name -> Int -> Q [Con]
mkTupElemCons aTyVar bTyVar width = do
    boundTyVars <- mapM (\i -> newName $ printf "t%d" i) [1..width-1]
    mapM (mkTupElemCon aTyVar bTyVar boundTyVars width) [1..width]

mkTupType :: Int -> Int -> [Name] -> Name -> Type
mkTupType elemIdx width boundTyVars bTyVar =
    let elemTys = map VarT $ take (elemIdx - 1) boundTyVars 
                             ++ [bTyVar] 
                             ++ drop (elemIdx - 1) boundTyVars
    in foldl' AppT (TupleT width) elemTys
    
mkTupElemCon :: Name -> Name -> [Name] -> Int -> Int -> Q Con
mkTupElemCon aTyVar bTyVar boundTyVars width elemIdx = do
    let binders   = map PlainTV boundTyVars
    let tupleType = mkTupType elemIdx width boundTyVars bTyVar
    let conName       = mkName $ printf "Tup%d_%d" width elemIdx
    let ctx       = [EqualP (VarT aTyVar) tupleType]
    return $ ForallC binders ctx (NormalC conName [])

-- | Generate the complete type of tuple acccessors for all tuple
-- widths.
-- 
-- @
-- data TupElem a b where 
--     Tup2_1 :: TupElem (a, b) a 
--     Tup2_2 :: TupElem (a, b) b 
--     Tup3_1 :: TupElem (a, b, c) a 
--     Tup3_2 :: TupElem (a, b, c) b 
--     Tup3_3 :: TupElem (a, b, c) c 
--     ...
-- @
-- 
-- Due to the lack of support for proper GADT syntax in TH, we have
-- to work with explicit universal quantification:
-- 
-- @
-- data TupElem a b =
--     | forall d. a ~ (b, d) => Tup2_1
--     | forall d. a ~ (d, b) => Tup2_2
-- 
--     | forall d e. a ~ (b, d, e) => Tup3_1
--     | forall d e. a ~ (d, b, e) => Tup3_2
--     | forall d e. a ~ (d, e, b) => Tup3_3
--     ...
-- @
mkTupElemType :: Int -> Q [Dec]
mkTupElemType maxWidth = do
    let tyName = mkName "TupElem"

    aTyVar <- newName "a"
    bTyVar <- newName "b"
    let tyVars = map PlainTV [aTyVar, bTyVar]

    cons   <- concat <$> mapM (mkTupElemCons aTyVar bTyVar) [2..maxWidth]

    return $ [DataD [] tyName tyVars cons []]
 
