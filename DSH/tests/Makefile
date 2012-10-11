all: cabal
		ghc --make Main.hs -o Main
		./Main

hpc: cabal
		mkdir tmp
		ghc -i../src -i../dist/build/autogen -outputdir tmp -fforce-recomp -fhpc --make Main.hs -o Main
		./Main
		hpc report Main
		hpc markup Main

cabal: clean
		cabal install HDBC-PostgreSQL
		cabal install derive
		cd ..; cabal install; cd tests;

clean:
		rm -rf tmp .hpc *.html *.tix *.o *.hi Main