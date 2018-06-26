VS:=$(wildcard *.v)

.PHONY: coq src clean

ARGS := -R . ProcKami -R ../Kami Kami -R ../bbv bbv

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(VS) -o Makefile.coq.all

src: Makefile.coq.src
	$(MAKE) -f Makefile.coq.src

Makefile.coq.src: Makefile $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(VS) -o Makefile.coq.src

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~ *.v.d *.vo *.~ *.glob
	rm -f Makefile.* Makefile.*.* Target.*
