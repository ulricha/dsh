module Language.ParallelLang.Common.Data.Config where
    
data Config = Config {opt :: [Optimisation], tyInf :: Bool, evalHs :: Bool, printHs :: Bool, detupling :: Bool, vectorise :: Bool, algebra :: Bool, algOut :: Bool, pathfinder :: Bool}

data Optimisation = LetOpt
                  | FnOpt
                  | RedRepl
                  | LetSimple
                  | PermuteOpt
                  | RewriteOpt
    deriving Eq

allOpts :: [Optimisation]
allOpts = [LetOpt, FnOpt, RedRepl, LetSimple, PermuteOpt, RewriteOpt]

defaultConfig :: Config
defaultConfig = Config [] False False False False False False False False

normalCompilation :: Config
normalCompilation = Config allOpts False False False True True True True True