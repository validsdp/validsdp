# Makefile for ValidSDP

COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

PLUGDIR := plugins/soswitness

MODULE_SDPA := $(PLUGDIR)/test-suite/soswitnesstac_sdpa.v

ifeq (,true)
MODULES := $(MODULE_SDPA)
else
MODULES :=
endif

all plugin test install html gallinahtml doc deps.dot deps.png: $(COQ_MAKEFILE) Makefile
	$(COQ_MAKE) $@

%.vo: %.v
	$(COQ_MAKE) $@

# This rule could be moved to Makefile.coq.local
$(PLUGDIR)/src/soswitness.mlg: $(PLUGDIR)/src/soswitness_v820.mlg
	$(RM) $@
	cp -f -- $< $@
	chmod a-w $@

$(COQ_MAKEFILE): $(COQ_PROJ) $(MODULES) $(PLUGDIR)/src/soswitness.mlg
	$(COQBIN)coq_makefile -f $< $(MODULES) -o $@
	# FIXME: This sed hack is fragile (if we do "make -B" for example)

FILES = AUTHORS LICENSE Makefile Makefile.coq.local _CoqProject\
  README.md coq-validsdp.opam install_sdpa_on_debian_10.sh

help:
	@echo $(SOSWITNESS_DIR)
	@echo "You can run:"
	@echo "    'make' to build ValidSDP"
	@echo "    'make plugin' to only build the soswitness plugin"
	@echo "    'make install' to install ValidSDP"
	@echo "    'make test' to run several tests"
	@echo "    'make doc' to build the documentation of the library"

.PHONY: all plugin test install html gallinahtml doc help clean distclean dist
