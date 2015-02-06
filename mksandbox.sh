#!/bin/bash

cabal sandbox delete
cabal sandbox init

cabal sandbox add-source $HOME/work/dev/algebra-dag
cabal install --dependencies-only
cabal configure

