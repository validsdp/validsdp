COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

all install html gallinahtml deps.dot deps.png doc dist clean: $(COQ_MAKEFILE)
	$(COQ_MAKE) $@

%.vo: %.v
	$(COQ_MAKE) $@

clean:
	-$(COQ_MAKE) clean
	$(RM) $(COQ_MAKEFILE) depend depend.dot depend.png depend.html makedot dependtodot.cm*

distclean: clean
	rm -rf autom4te.cache config.status $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf *~ .*.aux .lia.cache

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@

.PHONY: all test clean distclean install html gallinahtml doc dist
