#!/bin/bash
set -e
agda --latex thesis.lagda.tex
agda --latex FirstOrder.lagda.tex
agda --latex HigherOrder.lagda.tex
agda --latex ScopedAlgebras.lagda.tex
cd latex
lualatex -shell-escape thesis.tex
biber thesis
lualatex -shell-escape thesis.tex
cd ..
