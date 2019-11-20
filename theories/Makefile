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

test:
	$(COQ_MAKE) $@

clean:
	-$(COQ_MAKE) clean
	$(RM) $(COQ_MAKEFILE) depend depend.dot depend.png depend.map makedot

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@

.PHONY: all test clean install html gallinahtml doc dist
