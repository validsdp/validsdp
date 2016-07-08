NAME = soswitness
MODULES = \
src/soswitness.ml4 \
src/soswitness.mllib \
theories/soswitness.v \
test-suite/soswitnesstac.v

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -I src -I $(shell ocamlfind query zarith) -I $(shell ocamlfind query glpk) -I $(shell ocamlfind query osdp) \
                     -Q theories $(NAME) \
		     $(MODULES) \
		     -o $@
	sed -e 's/-linkall -shared -o $$@ $$</-linkall -shared -o $$@ zarith.cmxa glpk.cmxa osdp.cmxa $$</' -i $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: coq clean install
