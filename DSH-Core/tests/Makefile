all: clean
		cd ..; cabal clean; cabal install; cd tests;
		mkdir tmp
		ghc -i../src -i../dist/build/autogen -outputdir tmp -fforce-recomp -O3 -fhpc --make Main.hs -o Main
		./Main
		hpc report Main
		hpc markup Main

clean:
		rm -rf tmp .hpc *.html *.tix Main