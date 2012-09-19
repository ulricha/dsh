all: cabal
		ghc -Wall -O3 -fno-warn-orphans --make Main.hs -o Main
		./Main

hpc: cabal
		mkdir tmp
		ghc -Wall -i../src -i../dist/build/autogen -outputdir tmp -fforce-recomp -O3 -fhpc --make Main.hs -o Main
		./Main
		hpc report Main
		hpc markup Main

cabal: clean
		cd ..; cabal install; cd tests;

clean:
		rm -rf tmp .hpc *.html *.tix *.o *.hi Main