AGDA_BIN    ?= agda
RTS_OPTIONS ?= +RTS -M8.5G -s -RTS -vprofile:7 -vprofile.definitions:10
AGDA_EXEC   = $(AGDA_BIN) $(RTS_OPTIONS)

test: Everything.agda
	$(AGDA_EXEC) -i. -isrc README.agda

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
# The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# command `cabal install` is needed by cabal-install <= 2.4.*. I did
# not found any problem running both commands with different versions
# of cabal-install. See Issue #1001.
	cabal run GenerateEverything

clean :
	find . -type f -name '*.agdai' -delete
