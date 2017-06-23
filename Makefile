# Developer Makefile, for preparing an archive

all::
	@echo 'You can run:'
	@echo '    "make dist" to create a tarball'
	@echo '    "make external" to build extra Coq dependencies'
	@echo '    "make install" to build and install ValidSDP'

DIST1 = dist1
DIST2 = dist2

external::
	@echo Cloning external dependencies...
	git submodule update --init
	@echo Installing external dependencies...
	( cd external/paramcoq && make && make install )
	( cd external/CoqEAL/theory && make && make install )
	( cd external/CoqEAL/refinements && make && make install )
	( cd external/multinomials && make && make install )

install::
	$(MAKE) -C plugins/soswitness
	$(MAKE) -C plugins/soswitness install
	$(MAKE) -C plugins/theories
	$(MAKE) -C plugins/theories install

dist:: AUTHORS README
	$(MAKE) -C plugins/soswitness dist
	$(MAKE) -C theories dist
	T=$$(mktemp -d dist.XXX) && S=validsdp && mkdir -p $$T/$$S && rsync -R $^ $$T/$$S && rsync -av $(DIST1)/$$S $(DIST2)/$$S $$T; echo '\n'See $$T/$$S'\n'
	$(RM) -r $$(readlink $(DIST1)) $$(readlink $(DIST2))
	$(RM) $(DIST1) $(DIST2)
