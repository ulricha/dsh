module Main where

import System.IO
import System.Exit
import System.Environment
import System.Console.GetOpt
import qualified Data.Map as M
import qualified Data.ByteString.Lazy as B
  
import Database.Algebra.Dag
import Database.Algebra.Rewrite(Log, runRewrite)
import Database.Algebra.VL.Data
import Database.Algebra.VL.Render.JSON

import Optimizer.VL.OptimizeVL
import Optimizer.VL.Rewrite.Common
import Optimizer.VL.Properties.Types
  
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
  
optimize :: AlgebraDag VL -> [RewriteClass]-> (AlgebraDag VL, Log)
optimize = runPipeline
       
main :: IO ()
main = do
    args <- getArgs
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optInput = input } = opts
    
    plan <- input
    
    let (_, rs, m) = deserializePlan plan
        (_, propertyMap, _) = runRewrite inferBottomUp (mkDag m rs)
        tagMap = M.map renderBottomUpProps propertyMap
    B.putStr $ serializePlan (tagMap, rs, m)
