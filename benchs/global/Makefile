COQCOMMAND = coqc
PVS50COMMAND = ../pvs50/proveit

NAME = Sdpa

# Timeout in s
TIMEOUT = 900
# Memlimit in MB
MEMLIMIT = 7168

EXSML = $(shell find . -name "*.ml" | grep -v "parse.ml" | grep -v "_build/")
EXS = $(EXSML:.ml=)
LOGS = $(EXSML:.ml=_${NAME}_${TIMEOUT}s.log)
LOGS_COQ = $(EXSML:.ml=_Coq_${TIMEOUT}s.log)
LOGS_BERNSTEIN = $(EXSML:.ml=_Bernstein_${TIMEOUT}s.log)

all: logs

logs: $(LOGS)

logs_coq: $(LOGS_COQ)

logs_bernstein: $(LOGS_BERNSTEIN)

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

clean:
	rm -rf _build *~ *.native *.cmi *.cmx *.o *.vo *.glob

.PHONY: clean
