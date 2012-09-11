module Main where

import System.IO
import System.Exit
import System.Environment
import System.Console.GetOpt
import qualified Data.Map as M
import qualified Data.ByteString.Lazy as B
  
import qualified Database.Algebra.Dag as Dag
import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data
import Database.Algebra.VL.Render.JSON

import Optimizer.VL.OptimizeVL
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.TopDown
  
data Options = Options { optInput :: IO B.ByteString }
               
startOptions :: Options
startOptions = Options { optInput = B.getContents }
               
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option "i" ["input"]
      (ReqArg (\arg opt -> return opt { optInput = B.readFile arg })
       "FILE")
      "Input file"
  , Option "h" ["help"]
      (NoArg
         (\_ -> do 
             prg <- getProgName
             hPutStrLn stderr (usageInfo prg options)
             exitWith ExitSuccess))
      "Show help"
  ]
  
inferProperties :: DefaultRewrite VL (NodeMap Properties)
inferProperties = do
  to <- topsort
  bu <- infer (inferBottomUpProperties to)
  td <- infer (inferTopDownProperties bu to)
  return $ M.intersectionWith Properties bu td
  
main :: IO ()
main = do
    args <- getArgs
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optInput = input } = opts
    
    plan <- input
    
    let (_, rs, m) = deserializePlan plan
        d = Dag.mkDag m rs
        (_, propertyMap, _) = runDefaultRewrite inferProperties d
        tagMap = M.map renderProperties propertyMap
    B.putStr $ serializePlan (tagMap, rs, m)
