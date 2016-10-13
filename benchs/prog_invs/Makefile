# Parameters

COQCOMMAND = coqc

# SDP solver for OSDP (Sdpa | Csdp | Mosek)
NAME = Sdpa

# Timeout in s
TIMEOUT = 900
# Memlimit in MB
MEMLIMIT = 4096

# End of parameters
EXSML = $(shell find . -name "ex*.ml" | grep -v "_build/")
EXS = $(EXSML:.ml=)
LOGS_OSDP = $(EXSML:.ml=_${NAME}_${TIMEOUT}s.log)
LOGS_COQ = $(EXSML:.ml=_Coq_${TIMEOUT}s.log)
LOGS_MC11 = $(EXSML:.ml=_MC11_${TIMEOUT}s.log)

all: logs

logs: logs_osdp logs_coq logc_MC11

logs_osdp: $(LOGS_OSDP)

logs_coq: $(LOGS_COQ)

logs_MC11: $(LOGS_MC11)

%_${NAME}_${TIMEOUT}s.log: %.ml
	rm -f $@
	sed -e "s/solver = [^ ]*/solver = Osdp.Sdp.$(NAME)/" -i $<
	ocamlbuild -use-ocamlfind -pkg osdp $(<:.ml=.native)
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k ./$(<:.ml=.native) > $@ 2>&1 || true

%_Coq_${TIMEOUT}s.log: %.v
	rm -f $@
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k $(COQCOMMAND) $< > $@ 2>&1 || true

%_MC11_${TIMEOUT}s.log: %.sage
	rm -f $@
	runlim -s ${MEMLIMIT} -t ${TIMEOUT} -k sage $< > $@ 2>&1 || true

clean:
	rm -rf _build *~ *.native *.cmi *.cmx *.o *.vo *.glob sdp_problem.dat-s sdp_problem.result

.PHONY: clean
