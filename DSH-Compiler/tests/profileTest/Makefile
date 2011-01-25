main: clean
		cd ../..; cabal clean; cabal install; cd tests/profileTest;
		mkdir tmp
		ghc --make -i../../src/ -i../../dist/build/autogen -outputdir tmp -O3 -Wall -fforce-recomp dsh3-1 -o main
		ghc --make -i../../src/ -i../../dist/build/autogen -outputdir tmp -O3 -Wall -fforce-recomp -osuf p_o -prof -auto -auto-all dsh3-1 -o main
		time ./main +RTS -p -hc -RTS >> /dev/null
		hp2ps main.hp
		open main.ps


all: main

clean:
		rm -rf tmp .hpc *.html *.tix main 