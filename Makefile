OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt

SRCS = store.ml cycle.ml

all: bin opt
bin: rho bfast blist
opt: rho.opt bfast.opt blist.opt

install: opt
	install rho.opt ${HOME}/bin/rho
	install bfast.opt ${HOME}/bin/bfast
	install blist.opt ${HOME}/bin/blist

rho: rho.bin rho.opt; @true
rho.bin: store.cmo cycle.cmo rho.ml; ${OCAMLC} -pp camlp4o -o $@ $^
rho.opt: store.cmx cycle.cmx rho.ml; ${OCAMLOPT} -pp camlp4o -o $@ $^

bfast: bfast.bin bfast.opt; @true
bfast.bin: bfast.ml; ${OCAMLC} unix.cma -o $@ $?
bfast.opt: bfast.ml; ${OCAMLOPT} unix.cmxa -o $@ $?

blist: blist.bin blist.opt; @true
blist.bin: store.cmo cycle.cmo blist.ml; ${OCAMLC} unix.cma -o $@ $^
blist.opt: store.cmx cycle.cmx blist.ml; ${OCAMLOPT} unix.cmxa -o $@ $^

depend: $(SRCS)
	$(OCAMLDEP) $^ > depend

-include depend

.SUFFIXES: .ml .mli .mly .mll .cmo .cmx .cmi
.ml.cmo: ; ${OCAMLC} ${OCAMLFLAGS} ${OCAMLLIBS} -c $<
.ml.cmx: ; $(OCAMLOPT) $(OCAMLFLAGS) $(OCAMLOPTLIBS) -c $<
.mli.cmi: ; $(OCAMLC) $(OCAMLFLAGS) $(OCAMLLIBS) -c $<
.mly.ml: ; $(OCAMLYACC) -v $<
.mly.mli: ; $(OCAMLYACC) $<
.mll.ml: ; $(OCAMLLEX) $<

clean:;	rm -rf *~ *.cm* *.tmp *.bin *.opt *.out *.o
