all: cabal
		ghc -Wall -O3 -cpp --make Main.hs -o Main 
		./Main -s5

dbph: cabal
		ghc -Wall -O3 -cpp -DisDBPH --make Main.hs -o Main 
		./Main -s5

x100: cabal
		ghc -Wall -O3 -cpp -DisX100 --make Main.hs -o Main 
		./Main -s5
map: clean
		cd ..; cabal clean; cabal install -fmap; cd tests;
		ghc -Wall -O3 -cpp -DisDBPH --make Main.hs -o Main 
		./Main -s5

hpc: cabal
		mkdir tmp
		ghc -Wall -i../src -i../dist/build/autogen -outputdir tmp -fforce-recomp -O3 -fhpc --make Main.hs -o Main
		./Main -s5
		hpc report Main
		hpc markup Main

cabal: clean
		#cd ..; cabal clean; cabal install; cd tests;

clean:
		rm -rf tmp .hpc *.html *.tix *.o *.hi Main