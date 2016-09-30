EXSML = $(shell find . -name "ex*.ml" )
EXS = $(EXSML:.ml=)

all: $(EXS)

ex%: ex%.ml
	ocamlfind ocamlopt -linkpkg -package osdp -o $@ $<

clean:
	rm -f *~ $(EXS) *.cmi *.cmx *.o

.PHONY: clean
