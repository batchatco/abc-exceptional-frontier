# Build the manuscript with a containerized TeX Live (no local LaTeX install needed).
#
#   make            build main.pdf
#   make clean      remove LaTeX aux files (keep the PDF)
#   make realclean  remove aux files and the PDF

DOC       ?= main
RUNNER    ?= podman
TEX_IMAGE ?= texlive/texlive:latest-small

MOUNT   = --security-opt label=disable -v "$(CURDIR)":/work -w /work
TEX     = $(RUNNER) run --rm $(MOUNT) $(TEX_IMAGE)
LATEXMK = latexmk -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all pdf clean realclean

all: pdf

pdf: $(DOC).pdf

$(DOC).pdf: $(DOC).tex $(DOC).bib
	$(TEX) $(LATEXMK) $(DOC).tex

clean:
	$(TEX) latexmk -c $(DOC).tex

realclean:
	$(TEX) latexmk -C $(DOC).tex
