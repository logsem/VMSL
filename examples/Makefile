TEX = pdflatex --shell-escape -synctex=1 -interaction=nonstopmode

.PHONY: all clean

all : main.pdf

main.pdf : main.tex
	latexmk -pdf -pdflatex="$(TEX)" -use-make main.tex

clean:
	latexmk -CA
	rm -rf _minted-main
