module Main where

import Control.Concurrent.ParallelIO
import System.Process

-- Mondays from Mon, 10 Dec 2007 04:00:00 GMT
--         to   Mon, 08 Nov 2010 04:00:00 GMT
days :: [Double]
days = take 153 (iterate (+ 7 * 24 * 60 * 60) 1197259200)

main :: IO ()
main = do
  parallel_ $ map (\d -> rawSystem "dsh-wikipedia-centralities-day" [show d,"+RTS","-c"]) days
  stopGlobalPool
  