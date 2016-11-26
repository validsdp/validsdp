# Parameters

# Paths to various tools
COQCOMMAND = coqc
PVS50COMMAND = $(HOME)/pvs50/proveit
DIR_NLC = $(HOME)/forge/git-anon/nl-certify
HLCOMMAND = $(HOME)/forge/git-anon/hol-light/dmtcp-multi-ineqs/dmtcp_restart_script.sh

# SDP solver for OSDP (Sdpa | Csdp | Mosek)
NAME = Sdpa

# Timeout in s
TIMEOUT = 900
# Memlimit in MB
MEMLIMIT = 4096

# End of parameters

NLC = $(DIR_NLC)/nlcertify
NLC_PARAM = $(DIR_NLC)/param.transc
NLC_PATT := =INPUT=
NLC_INEQ = $(abspath ./input.ineq)

EXSML = $(shell find . -name "*.ml" | grep -v "parse.ml" | grep -v "fs...bis.ml" | grep -v "fs884.ml" | grep -v "_build/")
EXS = $(EXSML:.ml=)
LOGS_OSDP = $(EXSML:.ml=_${NAME}_${TIMEOUT}s.log)
LOGS_COQ = $(EXSML:.ml=_Coq_${TIMEOUT}s.log)
LOGS_BERNSTEIN = $(EXSML:.ml=_Bernstein_${TIMEOUT}s.log)
LOGS_MC11 = $(EXSML:.ml=_MC11_${TIMEOUT}s.log)
LOGS_NLCNOCOQ = $(EXSML:.ml=_nlcnocoq_${TIMEOUT}s.log)
LOGS_NLCCOQ = $(EXSML:.ml=_nlccoq_${TIMEOUT}s.log)
LOGS_TAYLOR = $(EXSML:.ml=_Taylor_${TIMEOUT}s.log)

all: logs

logs: logs_osdp logs_coq logs_bernstein logc_MC11 logs_nlcnocoq logs_nlccoq logs_taylor

logs_osdp: $(LOGS_OSDP)

logs_coq: $(LOGS_COQ)

logs_bernstein: $(LOGS_BERNSTEIN)

logs_MC11: $(LOGS_MC11)

logs_nlcnocoq: $(LOGS_NLCNOCOQ)

logs_nlccoq: $(LOGS_NLCCOQ)

logs_taylor: $(LOGS_TAYLOR)

%_${NAME}_${TIMEOUT}s.log: %.ml
	rm -f $@
	sed -e "s/solver = [^ ]*/solver = Osdp.Sdp.$(NAME)/" -i $<
	ocamlbuild -use-ocamlfind -pkg osdp $(<:.ml=.native)
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k ./$(<:.ml=.native) > $@ 2>&1 || true

%_Coq_${TIMEOUT}s.log: %.v
	rm -f $@
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(COQCOMMAND) $< > $@ 2>&1 || true

%_Bernstein_${TIMEOUT}s.log: %.pvs
	rm -f $@ $(<:.pvs=.summary)
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(PVS50COMMAND) $< > $@ 2>&1 || true

%_MC11_${TIMEOUT}s.log: %.sage
	rm -f $@
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k sage $< > $@ 2>&1 || true

%_nlcnocoq_${TIMEOUT}s.log: $(NLC_INEQ)
	rm -f $@
	perl -w -p -e 's|$(NLC_PATT)|$(NLC_INEQ)|;' ./param.transc.nocoq > $(NLC_PARAM)
	cd $(DIR_NLC) && runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(NLC) $(@:_nlcnocoq_${TIMEOUT}s.log=) > $(abspath $@) 2>&1 || true

%_nlccoq_${TIMEOUT}s.log: $(NLC_INEQ)
	rm -f $@
	perl -w -p -e 's|$(NLC_PATT)|$(NLC_INEQ)|;' ./param.transc.coq > $(NLC_PARAM)
	cd $(DIR_NLC) && runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(NLC) $(@:_nlccoq_${TIMEOUT}s.log=) > $(abspath $@) 2>&1 || true

%_Taylor_${TIMEOUT}s.log: %.hl
	rm -f $@
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(HLCOMMAND) < $< > $@ 2>&1 || true

clean:
	rm -rf _build *~ *.native *.cmi *.cmx *.o *.vo *.glob sdp_problem.dat-s sdp_problem.result *.log pvsbin .*.aux *.prf *.summary

.PHONY: clean
