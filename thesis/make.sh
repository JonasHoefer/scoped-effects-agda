#!/bin/bash
set -e
agda --latex thesis.lagda.tex
agda --latex FirstOrder.lagda.tex
cd latex
biber thesis
lualatex -shell-escape thesis.tex
cd ..
