module Main where

import           System.Console.GetOpt
import           System.Environment
import           System.Exit
import           System.IO

import           Data.Aeson
import           Data.ByteString.Lazy.Char8 (pack)
import qualified Data.IntMap                as M
import           Data.Maybe

import           Database.Algebra.Dag

import           Database.DSH.VL.Render.Dot

data Options = Options { optInput      :: IO String
                       , optReuse      :: Bool
                       , optRootNodes  :: Maybe [Int]
                       , optProperties :: Bool
                       }

startOptions :: Options
startOptions = Options { optInput            = getContents
                       , optReuse            = False
                       , optRootNodes        = Nothing
                       , optProperties       = False
                       }

options :: [OptDescr (Options -> IO Options)]
options =
  [ Option "i" ["input"]
      (ReqArg (\arg opt -> return opt { optInput = readFile arg })
       "FILE")
      "Input file"
  , Option "n" ["rootnodes"]
      (ReqArg (\arg opt -> return opt { optRootNodes = Just $ read arg })
       "ROOTNODES")
      "List of root nodes to use (must be in Haskell list syntax)"
  , Option "p" ["properties"]
      (NoArg (\opt -> return opt { optProperties = True }))
      "Infer properties and display them"
  , Option "h" ["help"]
      (NoArg
         (\_ -> do
             prg <- getProgName
             hPutStrLn stderr (usageInfo prg options)
             exitWith ExitSuccess))
      "Show help"
  ]

{-
propertyTags :: [AlgNode] -> NodeMap X100Algebra -> NodeMap [Tag] -> NodeMap [Tag]
propertyTags rs nm tags =
  let dag = normalizePlan $ mkDag nm rs
      topsorted = topsort dag
      bu = inferBottomUpProperties topsorted dag
      td = inferTopDownProperties bu topsorted dag
      buDocs = M.map renderBottomUpProps bu
      tdDocs = M.map renderTopDownProps td
      tagDocs = M.map (vcat . ((map text) . nub)) tags
      propsRendered = M.map render $ M.unionWith ($$) tagDocs $ M.unionWith ($$) buDocs tdDocs
      in M.map (\s -> [s]) propsRendered
-}

main :: IO ()
main = do
    args <- getArgs
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optInput = input
                , optRootNodes = mRootNodes } = opts

    plan <- input

    let dag = fromJust $ decode $ pack plan

    let rs' = fromMaybe (rootNodes dag) mRootNodes
    {-
        tags' = if printProperties
                then propertyTags rs' m tags
                else tags
-}

    putStr $ renderVLDot M.empty rs' (nodeMap dag)
