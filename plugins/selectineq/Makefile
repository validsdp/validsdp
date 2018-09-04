%: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

-include Makefile.coq

dist:
	T=$$(mktemp -d ../../dist3.XXX) && S=$$T/plugins/selectineq && mkdir -p $$S && rsync -rlpgoDvR Makefile _CoqProject $(ALLSRCFILES) $$S && rm -f ../../dist3 && ln -rsv $$T ../../dist3
