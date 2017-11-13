# Developer Makefile, for preparing an archive

all::
	@echo "You can run: make dist"

DIST1 = dist1
DIST2 = dist2

dist:: AUTHORS README
	$(MAKE) -C plugins/soswitness dist
	$(MAKE) -C theories dist
	T=$$(mktemp -d dist.XXX) && S=validsdp && mkdir -p $$T/$$S && rsync -R $^ $$T/$$S && rsync -av $(DIST1)/$$S $(DIST2)/$$S $$T; echo '\n'See $$T/$$S'\n'
	$(RM) -r $$(readlink $(DIST1)) $$(readlink $(DIST2))
	$(RM) $(DIST1) $(DIST2)
