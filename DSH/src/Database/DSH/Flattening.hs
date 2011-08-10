{-# LANGUAGE TemplateHaskell #-}
-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ, debugPlan, debugSQL, debugNKL, debugFKL, debugFKL', debugX100, debugX100Dot) where

import Language.ParallelLang.DBPH hiding (SQL)

import Database.DSH.ExecuteFlattening
import Database.DSH.CompileFlattening

import Database.DSH.Data
import Database.HDBC

import Control.Monad.State

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) =  do
                   (q, t) <- liftM nkl2SQL $ toNKL c a
                   executeQuery c t $ SQL q
                
debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = liftM show $ toNKL c e

debugFKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL c (Q e) = liftM nkl2fkl $ toNKL c e

debugFKL' :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL' c (Q e) = liftM nkl2fkl' $ toNKL c e

    
{-
debugVec :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugVec c (Q e) = liftM nkl2Vec $ toNKL c e
-}

debugX100 :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugX100 c (Q e) = liftM (show . (\(x,_) -> x) . nkl2X100Alg) $ toNKL c e

debugX100Dot :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugX100Dot c (Q e) = liftM nkl2X100Dot $ toNKL c e

debugPlan :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlan c (Q e) = liftM (show . (\(x,_) -> x) . nkl2Alg) $ toNKL c e

debugSQL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugSQL c (Q e) = liftM (show . (\(x,_) -> x) . nkl2SQL) $ toNKL c e