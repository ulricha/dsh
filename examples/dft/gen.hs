module Main where
       
import System.Environment
import System.IO
import Control.Monad
import Text.Printf

vec1 :: Int -> [(Integer, Double, Double)]
vec1 n = zipWith (\p (r, i) -> (p, r, i)) [1..] v
  where
    v = (1.0, 0.0) : (take (n - 1) $ repeat (0.0, 0.0))

renderVec :: [(Integer, Double, Double)] -> [String]
renderVec vec = map (\(p, r, i) -> printf "%d,%f,%f" p r i) vec

main :: IO ()
main = do
    [n] <- getArgs
    let vec = renderVec $ vec1 $ read n
    let f   = "vec1_" ++ n ++ ".dat"
    withFile f WriteMode $ \h -> 
        (forM_ vec $ \x -> hPutStrLn h x)
    
