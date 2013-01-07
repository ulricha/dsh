module Main where

import qualified Data.ByteString.Lazy                             as B
import qualified Data.Foldable                                    as F
import           Data.Functor
import           System.Console.GetOpt
import           System.Environment
import           System.Exit
import           System.IO

import qualified Database.Algebra.Dag                             as D
import           Database.Algebra.VL.Data
import           Database.Algebra.VL.Render.JSON

import           Database.DSH.Flattening.Common.Data.QueryPlan
import           Database.DSH.Flattening.Optimizer.Common.Rewrite
import           Database.DSH.Flattening.Optimizer.VL.OptimizeVL

data Options = Options { optVerbose        :: Bool
                       , optDebug          :: Bool
                       , optInput          :: IO B.ByteString
                       , optTopShape          :: String
                       , optPipelineString :: Maybe String
                       }

startOptions :: Options
startOptions = Options { optVerbose          = False
                       , optDebug            = False
                       , optInput            = B.getContents
                       , optTopShape            = "query_shape.plan"
                       , optPipelineString   = Nothing
                       }

options :: [OptDescr (Options -> IO Options)]
options =
  [ Option "v" ["verbose"]
      (NoArg (\opt -> return opt { optVerbose = True }))
      "Enable verbose messages"
  , Option "" ["debug"]
      (NoArg (\opt -> return opt { optDebug = True }))
      "Enable verbose messages"
  , Option "i" ["input"]
      (ReqArg (\arg opt -> return opt { optInput = B.readFile arg })
       "FILE")
      "Input file"
  , Option "s" ["shape"]
      (ReqArg (\arg opt -> return opt { optTopShape = arg })
       "FILE")
      "TopShape input file"
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

optimize :: D.AlgebraDag VL -> TopShape -> [RewriteClass]-> Bool -> (D.AlgebraDag VL, Log, TopShape)
optimize = runPipeline

main :: IO ()
main = do
    args <- getArgs
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optVerbose = verbose
                , optInput = input
                , optDebug = debugFlag
                , optTopShape = shapeFile
                , optPipelineString = mPipelineString } = opts

    plan <- input
    shape <- read <$> readFile shapeFile
    let pipeline = case mPipelineString of
          Just s ->
            case assemblePipeline s of
              Just p -> p
              Nothing -> error "invalid optimization string"
          Nothing -> defaultPipeline

    let (tags, rs, m) = deserializePlan plan
        (dag', rewriteLog, shape') = optimize (D.mkDag m rs) shape pipeline debugFlag
        m' = D.nodeMap dag'
        rs' = D.rootNodes dag'
    if verbose then F.mapM_ (\l -> hPutStrLn stderr l) rewriteLog else return ()
    B.putStr $ serializePlan (tags, rs', m')
    writeFile ("opt_" ++ shapeFile) $ show shape'


