module Language.ParallelLang.NKL.Eval where
    
import Language.Haskell.Interpreter

evalExpr :: String -> IO String
evalExpr e = do
                
                o <- runInterpreter $ evalExpr' e
                case o of 
                    Left err -> error $ show err
                    Right v -> return v

evalExpr' :: String -> InterpreterT IO String                    
evalExpr' e = do
                setImportsQ [("Prelude", Nothing)]
                eval e