NDGP: NDGP.pdf

NDGP.pdf: NDGP.tex
	latexmk -pdf NDGP

NDGP.tex: NDGP.lhs
	lhs2TeX --agda NDGP.lhs -o NDGP.tex
