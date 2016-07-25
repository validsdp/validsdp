COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

all install html gallinahtml deps.dot deps.png doc: $(COQ_MAKEFILE)
	$(COQ_MAKE) $@

clean:
	-$(COQ_MAKE) clean
	$(RM) $(COQ_MAKEFILE)

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@

.PHONY: all install clean
