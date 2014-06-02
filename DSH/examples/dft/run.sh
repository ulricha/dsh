#!/bin/sh

PREFIX=$1

rm *.vwq
ghc --make dft.hs
./dft
vldot -i ${PREFIX}_vl.plan | dot -Tpdf -o vl.pdf
x100dot -i ${PREFIX}_x100.plan | dot -Tpdf -o x100.pdf
x100dot -i ${PREFIX}_opt_x100.plan | dot -Tpdf -o x100_opt.pdf
x100gen -i ${PREFIX}_x100.plan
x100gen -i ${PREFIX}_opt_x100.plan
