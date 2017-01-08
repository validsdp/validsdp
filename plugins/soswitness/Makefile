NAME = ValidSDP
MODULES =\
  src/soswitness.ml4\
  src/soswitness.mllib\
  theories/soswitness.v\
  test-suite/soswitnesstac.v

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	@ocamlfind query zarith >/dev/null
	@ocamlfind query osdp >/dev/null
#	@ocamlfind query glpk >/dev/null
	coq_makefile -I src \
	  -I "$(shell ocamlfind query zarith)" -I "$(shell ocamlfind query ocplib-simplex)" -I "$(shell ocamlfind query osdp)" \
	  -Q theories $(NAME) $(MODULES) -o $@
	sed -e 's/-linkall -shared -o $$@ $$</-linkall -shared -o $$@ zarith.cmxa ocplibSimplex.cmxa osdp.cmxa $$</' -i $@
#	& glpk.cmxa

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

dist: $(MODULES) Makefile
	T=$$(mktemp -d ../../dist1.XXX) && S=$$T/validsdp/plugins/soswitness && mkdir -p $$S && rsync -R $^ $$S && rm -f ../../dist1 && ln -rsv $$T ../../dist1

.PHONY: all clean install dist
