module Main where

import System.IO
import System.Exit
import System.Environment
import System.Console.GetOpt
import qualified Data.Foldable as F
import qualified Data.ByteString.Lazy as B

import Database.Algebra.Dag
import Database.Algebra.Rewrite(Log)
import Database.Algebra.X100.Normalize
import Database.Algebra.VL.Data
import Database.Algebra.VL.Render.JSON

import Optimizer.VL.OptimizeVL
  
data Options = Options { optVerbose        :: Bool
                       , optInput          :: IO B.ByteString
                       , optPipelineString :: Maybe String
                       }
               
startOptions :: Options
startOptions = Options { optVerbose          = False
                       , optInput            = B.getContents
                       , optPipelineString   = Nothing
                       }
               
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option "v" ["verbose"]
      (NoArg (\opt -> return opt { optVerbose = True })) 
      "Enable verbose messages"
  , Option "i" ["input"]
      (ReqArg (\arg opt -> return opt { optInput = B.readFile arg })
       "FILE")
      "Input file"
  , Option "p" ["pipeline"]
      (ReqArg (\arg opt -> return opt { optPipelineString = Just arg })
       "PIPELINE")
      "String description of the optimization pipeline" 
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
    let Options { optVerbose = verbose
                , optInput = input
                , optPipelineString = mPipelineString } = opts
    
    plan <- input
    let pipeline = case mPipelineString of
          Just s ->
            case assemblePipeline s of
              Just p -> p
              Nothing -> error "invalid optimization string"
          Nothing -> defaultPipeline
    
    let (tags, rs, m) = deserializePlan plan
        (dag', rewriteLog) = optimize (mkDag m rs) pipeline 
        m' = nodeMap dag'
        rs' = rootNodes dag'
    if verbose then F.mapM_ (\l -> hPutStrLn stderr l) rewriteLog else return ()
    B.putStr $ serializePlan (tags, rs', m')


