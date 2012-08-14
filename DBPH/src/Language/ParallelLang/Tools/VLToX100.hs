module Main where

import Data.Functor
import Control.Monad

import System.IO
import System.Exit
import System.Environment
import System.Console.GetOpt
  
import qualified Data.Map as M
  
import qualified Data.ByteString.Lazy.Char8 as BL
  
import Language.ParallelLang.Translate.VL2Algebra
import Language.ParallelLang.Translate.FKL2VL()
  
import Database.Algebra.Dag
import qualified Database.Algebra.VL.Render.JSON as VLJSON
import qualified Database.Algebra.X100.JSON as X100JSON

data Options = Options { optDagFile    :: IO BL.ByteString 
                       , optShapeFile  :: FilePath
                       , optOutputFile :: IO Handle }
  
startOptions :: Options
startOptions = Options { optDagFile    = BL.readFile "query_vl.plan" 
                       , optShapeFile  = "query_shape.plan" 
                       , optOutputFile = return stdout }
               
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option "d" ["dag"]
      (ReqArg (\arg opt -> return opt { optDagFile = BL.readFile arg })
       "FILE")
      "DAG input file"
  , Option "s" ["shape"]
      (ReqArg (\arg opt -> return opt { optShapeFile = arg })
       "FILE")
      "Shape input file"
  , Option "o" ["output"]
      (ReqArg (\arg opt -> return opt { optOutputFile = openFile arg WriteMode})
       "FILE")
      "Output file for the X100 plan"
  , Option "h" ["help"]
      (NoArg
         (\_ -> do 
             prg <- getProgName
             hPutStrLn stderr (usageInfo prg options)
             exitWith ExitSuccess))
      "Show help"
  ]
  
main :: IO ()
main = do
    args <- getArgs 
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optDagFile    = readDagFile 
                , optShapeFile  = shapeFile 
                , optOutputFile = outputFile      } = opts 
    
    (_, rs, nm) <- liftM VLJSON.deserializePlan $ readDagFile
    shape <- read <$> readFile shapeFile
    outputHandle <- outputFile
    
    let (x100Dag, x100Shape) = vlDagtoX100Dag (mkDag nm rs) (importShape shape)
    BL.hPut outputHandle $ X100JSON.serializePlan (M.empty, rootNodes x100Dag, nodeMap x100Dag)
    writeFile ("x100_" ++ shapeFile) $ show $ exportShape x100Shape

    
