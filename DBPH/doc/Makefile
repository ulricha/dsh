# Author: Jeroen Weijers
# Use this makefile template for compiling lhs2tex projects
# Replace occurences of word Template with the file you want to compile

commonFiles := $(wildcard ./common/*)
ltxFiles := $(wildcard *.ltx)
fmtFiles := $(wildcard ./fmt/*.fmt)
dbphFiles := $(shell find ../src)

all : ./build/Flattening.pdf

build :
	mkdir -p build

./build/Flattening.pdf : ./build/Flattening.tex  $(commonFiles) Flattening.bib
	pdflatex -output-directory=./build -halt-on-error ./build/Flattening.tex
	bibtex ./build/Flattening
	pdflatex -output-directory=./build -halt-on-error ./build/Flattening.tex
	pdflatex -output-directory=./build -halt-on-error ./build/Flattening.tex
	pdflatex -output-directory=./build -halt-on-error ./build/Flattening.tex

./build/Flattening.tex : build $(ltxFiles) $(commonFiles) $(fmtFiles) $(dbphFiles)
	rm -f ./build/Flattening.tex
	echo $(ltxFiles)
	echo  
	lhs2TeX --poly -v --path=:fmt:$(shell find ../src -type d  | tr '\n' ':') ./Flattening.ltx >> ./build/Flattening.tex

clean :
	rm -r ./build

.PHONY : clean all
