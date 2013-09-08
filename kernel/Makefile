ROOT := ./ynot

COQTOP = coqtop.opt
COQC   = coqc

OCAMLBUILD = ocamlbuild
OCAMLC     = ocamlc

OBJS = str.cma unix.cma ocaml/VCRCommon.cmo ocaml/VCRIOImpl.cmo .extract/Kernel.cmo ocaml/main.cmo 

include ./ynot/examples/Makefile.ynot

#sendfd.o: ./ocaml/sendfd.c
#        ocamlc -c $<

#dll_sendfd_stubs.so: sendfd.o
#        ocamlmklib  -o _wrap_stubs $<

stub : 
	mkdir -p .extract
	ocamlc -c ./ocaml/sendfd.c
	ocamlmklib  -o _sendfd_stub sendfd.o

buildall : stub build

extract: 
	ls -al 
	coq ml/ExtractRules ../../mllib/ExtractTemplate.v $(MODULES:%.v=.extract/%.ml)
	@ cp ../../mllib/ExtractTemplate.v Extract.v
	@ echo >> Extract.v
	@ if [ -f ml/ExtractRules ]; then \
            cat ml/ExtractRules >> Extract.v; \
          fi
	@ echo >> Extract.v
	@ if [ -f ml/ExtractExtra ]; then \
            cat ml/ExtractExtra >> Extract.v; \
          fi
	$(COQC) $(COQ_OPTIONS) -I . Extract
	- for x in patch/*.patch; do patch -N -p0 < $$x; done
	@ rm -f Extract.v Extract.vo .extract/*.orig .extract/*.rej

.SUFFIXES: .v .ml .vo

.v.vo: coq

