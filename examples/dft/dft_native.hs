-- Naive native DFT implementation
-- Source: http://www.skybluetrades.net/blog/posts/2013/11/13/data-analysis-fft-1.html

import Prelude hiding (length, sum, map, zipWith, (++))
import Data.Complex
import Data.Vector

i :: Complex Double
i = 0 :+ 1

omega :: Int -> Complex Double
omega n = cis (2 * pi / fromIntegral n)

dft, idft :: Vector (Complex Double) -> Vector (Complex Double)
dft = dft' 1 1
idft v = dft' (-1) (1.0 / (fromIntegral $ length v)) v

dft' :: Int -> Double -> Vector (Complex Double) -> Vector (Complex Double)
dft' sign scale h = generate bigN (((scale :+ 0) *) . doone)
  where bigN = length h
        w = omega bigN
        doone n = sum $
                  zipWith (*) h $ generate bigN (\k -> w^^(sign*n*k))

defuzz :: Vector (Complex Double) -> Vector (Complex Double)
defuzz = map (\(r :+ i) -> df r :+ df i)
  where df x = if abs x < 1.0E-6 then 0 else x

