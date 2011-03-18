module Main where

import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.Exit


import Language.ParallelLang.Translate.NKL2FKL
import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.NKL.Parser.Parser
import Language.ParallelLang.Common.Data.Config
import Language.ParallelLang.NKL.TypeInferencer.TypeInferencer
import Language.ParallelLang.NKL.TypeInferencer.Types
import Language.ParallelLang.Common.Data.Type 
import Language.ParallelLang.Common.Data.Prelude
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Translate.RewritePhases
import Language.ParallelLang.Translate.Vectorise 

import Language.ParallelLang.Translate.Detupler


import Language.ParallelLang.NKL.Eval
import Language.ParallelLang.NKL.Render.Hs.NKL2HS
import Language.ParallelLang.Translate.Vec2Algebra

-- | Description of the options for the compiler 'Mode'
options :: [OptDescr (Config -> Config)]
options = [ Option ['o']["opt"]
                (NoArg (\o -> o {opt = allOpts}))
                    "Enable all optimisations",
            Option ['l']["letOpt"]
                    (NoArg (\o -> o {opt = LetOpt : (opt o)}))
                        "Optimise let iteration",
            Option ['f']["funOpt"]
                    (NoArg (\o -> o {opt = FnOpt : (opt o)}))
                        "Optimise lifting of function bodies",
            Option ['r']["reduceRepl"]
                    (NoArg (\o -> o {opt = LetOpt : RedRepl : (opt o)}))
                        "Reduce replication",
            Option ['t']["type"]
                    (NoArg (\o -> o {tyInf = True}))
                        "Print type of program to console",
            Option ['e']["eval"]
                    (NoArg (\o -> o {evalHs = True}))
                        "Evaluate program with Haskell and print result to console",
            Option ['h']["haskell"]
                    (NoArg (\o -> o {printHs = True}))
                        "Transform given program into a valid Haskell 98 program",
            Option ['d']["detuple"]
                    (NoArg (\o -> o {detupling = True, opt = RewriteOpt : (opt o)}))
                        "Flatten the given program and then detuple",
            Option ['v']["vectorise"]
                    (NoArg (\o -> o {vectorise = True, detupling = True, opt = RewriteOpt : (opt o)}))
                        "Vectorise the given program",
            Option ['z']["trivialLet"]
                    (NoArg (\o -> o {opt = LetSimple : (opt o)}))
                        "Remove let bindings of trivial expressions",
            Option ['p']["permute"]
                    (NoArg (\o -> o {opt = RewriteOpt : PermuteOpt : (opt o)}))
                        "Remove lifted index-dist structures in favor of bPermute", 
            Option ['w']["rewrite"]
                    (NoArg (\o -> o {opt = RewriteOpt : (opt o)}))
                        "Enable rewrite rules"
          ]

-- | Process the arguments given to the compiler
processArgs :: String -> [String] -> IO (Config, [String])
processArgs progName args =
  case getOpt Permute options args of
    (oargs, nonopts, []    ) -> return (foldl (flip ($)) defaultConfig oargs, nonopts)
    (_    , _      , errors) -> ioError $ userError $ "\n" ++ (concat errors) ++ usageInfo header options
  where
    header = "\nUsage: " ++ progName
             ++ " [OPTION...] [FILES], with the following options:"


    
main :: IO ()
main =
    do
        args <- getArgs
        progName <- getProgName
        (conf, files) <- processArgs progName args
        mapM_ (handleFile conf) files
        return ()

{-
Temporary pipeline, if we are going to pursue a full translation to the database (or better when we now a bit more specific how) 
this should be merged into Ferryc. Or will at least have to adopt a similar structure, and might share large parts with ferryc.
-}        
handleFile :: Config -> String -> IO ()
handleFile c n = do 
                  let (file, _) = splitExtension n
                  f <- readFile n
                  let ast = parseProgram n f
                  let tyAst = runAlgW preludeEnv $ algW ast
                  case tyInf c of
                      True -> do
                                putStrLn $ "Inferred type: " ++ (show $ typeOf $ snd tyAst)
                                exitSuccess
                      _ -> return ()
                  let hs = programToHs tyAst
                  case printHs c of
                      True -> do
                                writeFile (file ++ ".hs") hs
                      _    -> return ()
                  case evalHs c of
                      True -> do
                                r <- evalExpr hs
                                putStrLn r
                                exitSuccess
                      _ -> return () 
                  
                  let ir = do
                             r <- flatTransform tyAst
                             dr <- withOpt RewriteOpt  
                             r' <- if dr 
                                     then runRWPhase1 r
                                     else return r
                             if detupling c
                                   then do 
                                          r'' <- normTuples r' 
                                          if dr 
                                             then runRWPhase2 r''
                                             else return r''
                                   else return r'
                  if vectorise c
                       then do
                              let (fs, b) = runTransform c $ runVectorise =<< ir
                              let output = "let\n" ++ foldr (\x y -> show x ++ "\n" ++ y) [] fs ++ "in\n" ++ show b
                              writeFile (file ++ ".vec") output
                       else do
                                let (fs, b) = runTransform c ir
                                let output = "let\n" ++ foldr (\x y -> show x ++ "\n" ++ y) [] fs ++ "in\n" ++ show b
                                writeFile (file ++ ".out") output
