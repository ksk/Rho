OCAMLC = ocamlc
OCAMLCP = ocamlcp
OCAMLOPT = ocamlopt

all: bin opt
bin: rho bfast
opt: rho.opt bfast.opt

install: opt
	install rho.opt ${HOME}/bin/rho
	install bfast.opt ${HOME}/bin/bfast

rho: rho.bin; @true
rho.bin: rho.ml
	${OCAMLC} -pp camlp4o nums.cma -o $@ $?
rho.opt: rho.ml; ${OCAMLOPT} -pp camlp4o nums.cmxa -o $@ $?

bfast: bfast.bin bfast.opt; @true
bfast.bin: bfast.ml; ${OCAMLC} unix.cma -o $@ $?
bfast.opt: bfast.ml; ${OCAMLOPT} unix.cmxa -o $@ $?

clean:;	rm -rf *~ *.cm* *.tmp *.bin *.opt *.out *.o
