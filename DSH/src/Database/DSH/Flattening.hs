{-# LANGUAGE TemplateHaskell #-}
-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ, debugVec, debugPlan, debugSQL, debugNKL) where

import Language.ParallelLang.DBPH hiding (SQL)

import Database.DSH.ExecuteFlattening
import Database.DSH.CompileFlattening

import Database.DSH.Data
import Database.HDBC

import Control.Monad.State

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) =  do
                   (q, _s) <- liftM nkl2SQL $ toNKL c a
                   executeQuery c $ SQL q
                
debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = liftM show $ toNKL c e

debugVec :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugVec c (Q e) = liftM nkl2Vec $ toNKL c e

debugPlan :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlan c (Q e) = liftM (show . fst . nkl2Alg) $ toNKL c e

debugSQL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugSQL c (Q e) = liftM (show . fst . nkl2SQL) $ toNKL c e
