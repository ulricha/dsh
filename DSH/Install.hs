#!/usr/bin/env runhaskell

import System.Process

install = main

main = do
  _ <- rawSystem "cabal" ["clean"]
  _ <- rawSystem "cabal" ["update"]
  _ <- rawSystem "cabal" ["install"]
  _ <- rawSystem "cabal" ["clean"]
  return ()