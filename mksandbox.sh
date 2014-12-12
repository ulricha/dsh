#!/bin/bash

cabal sandbox delete
cabal sandbox init

cabal sandbox add-source $HOME/work/dev/TableAlgebra
cabal sandbox add-source $HOME/work/dev/x100client
cabal install --dependencies-only --extra-lib-dirs $HOME/software/x100/lib --disable-library-profiling --disable-executable-profiling
cabal configure --disable-library-profiling --disable-executable-profiling 

