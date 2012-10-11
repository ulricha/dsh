all: cabal
		ghc --make Main.hs -o Main
		./Main

cabal: clean
		cabal install quickcheck
		cabal install hdbc-postgresql
		cabal install derive
		cd ..; cabal install; cd tests;

clean:
		rm -rf tmp .hpc *.html *.tix *.o *.hi Main