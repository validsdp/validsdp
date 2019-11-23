COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

all install html gallinahtml doc deps.dot deps.png: $(COQ_MAKEFILE)
	$(COQ_MAKE) $@

%.vo: %.v
	$(COQ_MAKE) $@

clean:
	-$(COQ_MAKE) clean
	$(RM) depend depend.dot depend.png depend.map

distclean: clean
	$(RM) -r autom4te.cache
	$(RM) config.log config.status configure
	$(RM) _CoqProject
	$(RM) $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	$(RM) *~ .*.aux .lia.cache

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@


FILES = ../AUTHORS ../LICENSE Makefile Makefile.coq.local _CoqProject.in\
  README.md

# This must be disabled to cope with the distributed (stable) tarballs
# configure: configure.ac
# 	./autogen.sh

_CoqProject: _CoqProject.in configure
	./configure

-include $(COQ_MAKEFILE).conf

# Create a tarball dist.YYYY-MM-DD.XXX/libvalidsdp-a.b.c.tar.gz
# containing libvalidsdp-a.b.c/ with $(FILES), configure, and the *.v
dist: configure $(COQMF_VFILES)
	export T=$$(readlink -f $$(mktemp -d dist.$$(date -I).XXX)) && export S=@PACKAGE_TARNAME@-@PACKAGE_VERSION@ && mkdir -p $$T/$$S && rsync -rlpgoDvR $(FILES) $^ $$T/$$S && (cd $$T && tar cvzf $$S.tar.gz $$S); echo '\n'See $$T/'\n'

.PHONY: all plugin install html gallinahtml doc clean distclean dist
