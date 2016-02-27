OCAMLBUILD=ocamlbuild -classic-display -no-links

trmx:
	$(OCAMLBUILD) main.native
	cp _build/main.native $@

clean:
	$(OCAMLBUILD) -clean
	rm -f *~

.PHONY: trmx clean
