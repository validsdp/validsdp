NAME = ValidSDP
MODULES = \
src/soswitness.ml4 \
src/soswitness.mllib \
theories/soswitness.v \
test-suite/soswitnesstac.v

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -I src -I $(shell ocamlfind query zarith) -I $(shell ocamlfind query osdp) \
                     -Q theories $(NAME) \
		     $(MODULES) \
		     -o $@  #  -I $(shell ocamlfind query glpk)
	sed -e 's/-linkall -shared -o $$@ $$</-linkall -shared -o $$@ zarith.cmxa osdp.cmxa $$</' -i $@  # glpk.cmxa

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: coq clean install
