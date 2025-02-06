# Makefile for libValidSDP

COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

all install html gallinahtml doc deps.dot deps.png: $(COQ_MAKEFILE) Makefile
	$(COQ_MAKE) $@

%.vo: %.v
	$(COQ_MAKE) $@

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@

clean:
	-$(COQ_MAKE) clean
	$(RM) depend depend.dot depend.png depend.map

distclean: clean
	$(RM) -r autom4te.cache
	$(RM) config.log config.status configure
	$(RM) _CoqProject Makefile
	$(RM) $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	$(RM) *~ .*.aux .lia.cache


FILES = ../AUTHORS ../LICENSE Makefile.in Makefile.coq.local _CoqProject.in\
  README.md ../coq-libvalidsdp.opam

-include $(COQ_MAKEFILE).conf

.PHONY: all plugin install html gallinahtml doc clean distclean dist
