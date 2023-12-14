PRECISA_PATH ?= $(CURDIR)/deps/precisa
CABAL ?= cabal

all: build-reflow

checkout-submodules:
	git submodule update --init --recursive

build-precisa: checkout-submodules
	@( \
		cd $(PRECISA_PATH); \
		$(MAKE) configure-precisa; \
	)
	@( \
		cp $(PRECISA_PATH)/PRECiSA/cabal.project.local .; \
		$(CABAL) v2-install precisa --overwrite-policy=always; \
	)

build-reflow: build-precisa
	@( \
		$(CABAL) v2-install reflow --overwrite-policy=always; \
	)
