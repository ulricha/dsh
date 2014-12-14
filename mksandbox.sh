#!/bin/bash

cabal sandbox delete
cabal sandbox init

cabal sandbox add-source $HOME/work/dev/algebra-dag
cabal sandbox add-source $HOME/work/dev/algebra-sql
#cabal sandbox add-source $HOME/work/dev/algebra-x100
#cabal sandbox add-source $HOME/work/dev/x100client
cabal install --dependencies-only --disable-library-profiling --disable-executable-profiling # --extra-lib-dirs $HOME/software/x100/lib
cabal configure --disable-library-profiling --disable-executable-profiling 

