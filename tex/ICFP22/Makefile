
.PHONY: NDGP
NDGP: NDGP.pdf

NDGP.pdf: tex
	latexmk -pdf NDGP

.PHONY: watch
watch: tex
	latexmk -pdf -pvc NDGP

.PHONY: tex
tex: NDGP.lhs
	lhs2TeX --agda NDGP.lhs -o NDGP.tex

.PHONY: clean
clean:
	latexmk -C NDGP
	rm NDGP.tex
