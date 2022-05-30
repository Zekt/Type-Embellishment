AGDA_BIN    ?= agda
RTS_OPTIONS ?= +RTS -M8G -H3.5G -A128M -s -RTS
AGDA_EXEC   = $(AGDA_BIN) $(RTS_OPTIONS)

library: Library.agda
	$(AGDA_EXEC) -i. -isrc Library.agda -vprofile:7

example1: ExamplesByMacro.agda
	$(AGDA_EXEC) -i. -isrc ExamplesByMacro.agda -vprofile:7

example2: ExamplesByHand.agda
	$(AGDA_EXEC) -i. -isrc ExamplesByHand.agda -vprofile:7

test: Everything.agda
	$(AGDA_EXEC) -i. -isrc README.agda -vprofile:7

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
# The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# command `cabal install` is needed by cabal-install <= 2.4.*. I did
# not found any problem running both commands with different versions
# of cabal-install. See Issue #1001.
	cabal run GenerateEverything

benchmark : 
	$(AGDA_EXEC) Benchmark.agda  -i. -vprofile.definitions:10
	rm _build/*/agda/Benchmark.agdai

clean :
	find . -type f -name '*.agdai' -delete
