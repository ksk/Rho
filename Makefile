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

all: rho bpoly
opt: rho.opt bpoly.opt

install: opt
	install rho.opt $(HOME)/bin/rho
	install bpoly.opt $(HOME)/bin/bpoly

rho: rho.bin rho.opt; @true
rho.bin: store.cmo cycle.cmo rho.ml
	$(OCAMLC) -pp camlp4o $(OCAMLLIBS) -o $@ $^
rho.opt: store.cmx cycle.cmx rho.ml
	$(OCAMLOPT) -pp camlp4o $(OCAMLOPTLIBS) -o $@ $^

bpoly: bpoly.bin bpoly.opt; @true
bpoly.bin: store.cmo cycle.cmo bexpr.cmo bpoly.ml
	$(OCAMLFIND) $(OCAMLC) $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLLIBS) zarith.cma -o $@ $^
bpoly.opt: store.cmx cycle.cmx bexpr.cmx bpoly.ml
	$(OCAMLFIND) $(OCAMLOPT) $(OCAMLPKG) $(OCAMLFLAGS) $(OCAMLOPTLIBS) zarith.cmxa -o $@ $^

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

clean:;	rm -rf *~ *.cm* *.tmp *.bin *.opt *.out *.o depend
