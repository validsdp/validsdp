# Developer Makefile, for preparing an archive

all::
	@echo "You can run: make dist"

dist:: AUTHORS README
	T=$$(mktemp -d dist0.XXX)/validsdp && mkdir -p $$T && rsync -R $^ $$T; echo '\n'Target is $$T
	$(MAKE) -C plugins/soswitness dist
	$(MAKE) -C theories dist
