all: cabal
		ghc -Wall -O3 -cpp --make Main.hs -o Main 
		./Main

dbph: cabal
		ghc -Wall -O3 -cpp -DisDBPH --make Main.hs -o Main 
		./Main
hpc: cabal
		mkdir tmp
		ghc -Wall -i../src -i../dist/build/autogen -outputdir tmp -fforce-recomp -O3 -fhpc --make Main.hs -o Main
		./Main
		hpc report Main
		hpc markup Main

cabal: clean
		cd ..; cabal clean; cabal install; cd tests;

clean:
		rm -rf tmp .hpc *.html *.tix *.o *.hi Main