PREFIX = $(HOME)
CC = cc
OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLFIND = ocamlfind

OCAMLPKG = -package zarith
OCAMLFLAGS = # -I +zarith
OCAMLLIBS = unix.cma
OCAMLOPTLIBS = unix.cmxa

SRCS = store.ml cycle.ml bexpr.ml

all: rho bpoly bmono

opt: rho bpoly; @true

install: opt test bmono
	install rho.opt $(PREFIX)/bin/rho
	install bpoly.opt $(PREFIX)/bin/bpoly
	install bmono $(PREFIX)/bin/bmono

# tests for bpoly and cycle finding implementation
test: opt
	./bpoly.opt -t

rho: rho.opt; @true 
rho.bin: store.cmo cycle.cmo rho.ml
	$(OCAMLC) -pp camlp4o $(OCAMLFLAGS) $(OCAMLLIBS) -o $@ $^
rho.opt: store.cmx cycle.cmx rho.ml
	$(OCAMLOPT) -pp camlp4o $(OCAMLFLAGS) $(OCAMLOPTLIBS) -o $@ $^

bpoly: bpoly.bin bpoly.opt; @true
bpoly.bin: store.cmo cycle.cmo bexpr.cmo arithexp.cmo bpoly.ml
	$(OCAMLFIND) $(OCAMLC) $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLLIBS) zarith.cma -o $@ $^
bpoly.opt: store.cmx cycle.cmx bexpr.cmx arithexp.cmx bpoly.ml
	$(OCAMLFIND) $(OCAMLOPT) -O3 $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLOPTLIBS) zarith.cmxa -o $@ $^

arithexp: arithexp.cmx arithexp.cmo; @true

arithexp.cmx: arithexp.ml
	$(OCAMLOPT) -pp camlp4o $(OCAMLFLAGS) $(OCAMLOPTLIBS) $^
arithexp.cmo: arithexp.ml
	$(OCAMLC) -pp camlp4o $(OCAMLFLAGS) $(OCAMLLIBS) $^

bmono: bmono.c
	$(CC) -O2 -o $@ $^

depend: $(SRCS)
	$(OCAMLDEP) $^ > depend

-include depend

.SUFFIXES: .ml .mli .mly .mll .cmo .cmx .cmi
.ml.cmo: ; $(OCAMLFIND) $(OCAMLC) $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLLIBS) -c $<
.ml.cmx: ; $(OCAMLFIND) $(OCAMLOPT) $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLOPTLIBS) -c $<
.mli.cmi: ; $(OCAMLC) $(OCAMLFLAGS) $(OCAMLLIBS) -c $<
.mly.ml: ; $(OCAMLYACC) -v $<
.mly.mli: ; $(OCAMLYACC) $<
.mll.ml: ; $(OCAMLLEX) $<

clean:;	rm -rf *~ *.cm* *.tmp *.bin *.opt *.out *.o depend bmono
