module Main where

import System.IO
import System.Exit
import System.Environment
import System.Console.GetOpt

import Data.ByteString.Lazy.Char8 (pack)
  
import Data.Maybe

import Database.DSH.VL.Render.JSON
import Database.DSH.VL.Render.Dot
  
data Options = Options { optInput          :: IO String
                       , optReuse          :: Bool
                       , optRootNodes      :: Maybe [Int]
                       , optProperties      :: Bool
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
  
main :: IO ()
main = do
    args <- getArgs 
    let (actions, _, _) = getOpt RequireOrder options args
    opts <- foldl (>>=) (return startOptions) actions
    let Options { optInput = input
                , optRootNodes = mRootNodes } = opts
    
    plan <- input
    
    let (tags, rs, m) = deserializePlan $ pack plan
    
    let rs' = fromMaybe rs mRootNodes
    
    putStr $ renderVLDot tags rs' m
