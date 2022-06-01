AGDA_BIN    ?= agda
RTS_OPTIONS ?= +RTS -M8G -H3.5G -A128M -s -RTS
AGDA_EXEC   = $(AGDA_BIN) $(RTS_OPTIONS)

everything: Everything.agda
	$(AGDA_EXEC) -i. -isrc Everything.agda --profile=internal

library: Library.agda
	$(AGDA_EXEC) -i. -isrc Library.agda --profile=internal

example1: ExamplesByMacro.agda
	$(AGDA_EXEC) -i. -isrc ExamplesByMacro.agda --profile=internal

example2: ExamplesByHand.agda
	$(AGDA_EXEC) -i. -isrc ExamplesByHand.agda --profile=internal

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
# The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# command `cabal install` is needed by cabal-install <= 2.4.*. I did
# not found any problem running both commands with different versions
# of cabal-install. See Issue #1001.
	cabal run GenerateEverything

example1-defs : 
	rm -rf _build/*/agda/src/WithMacros
	$(AGDA_EXEC) ExamplesByMacro.agda  -i. --profile=definitions

example2-defs : 
	rm -rf _build/*/agda/src/WithoutMacros
	$(AGDA_EXEC) ExamplesByHand.agda  -i. --profile=definitions

benchmark : 
	$(AGDA_EXEC) Benchmark.agda  -i. --profile=definitions
	rm _build/*/agda/Benchmark.agdai

clean :
	find . -type f -name '*.agdai' -delete
