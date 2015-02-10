#!/bin/bash

./dist/build/vldot/vldot -i q_vl.plan | dot -Tpdf -o q_vl.pdf
./dist/build/vldot/vldot -i q_opt_vl.plan | dot -Tpdf -o q_opt_vl.pdf
.cabal-sandbox/bin/tadot -i q_ta.plan | dot -Tpdf -o q_ta.pdf
.cabal-sandbox/bin/tadot -i q_opt_ta.plan | dot -Tpdf -o q_opt_ta.pdf
