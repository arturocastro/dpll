
#OCAMLBUILDFLAGS= -I src  -lflag str.cmxa -lflag unix.cmxa
OCAMLOPT=ocamlopt
OCAMLFLAGS= -I obj/ 

all: gorrila



gorrila: obj/lib.cmi obj/lib.cmx obj/options_rnd_gen.cmi obj/options_rnd_gen.cmx obj/solver_run.cmi obj/solver_run.cmx
	ocamlopt -I obj/ unix.cmxa str.cmxa obj/lib.cmx obj/options_rnd_gen.cmx obj/solver_run.cmx -o $@ src/$@.ml 
#gorrila: src/*
#	ocamlbuild $(OCAMLBUILDFLAGS) gorrila.native
#	cp -L gorrila.native $@
#	rm gorrila.native

obj/%.cmi : src/%.mli
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 

obj/%.cmx : src/%.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<


.PHONY : clean archive

clean: 
	rm -f obj/* gorrila
#clean:
#	ocamlbuild -clean
#	rm -f gorrila gorrila.prof random_generator hard_reality hard_reality.prof test_generator_lra.prof

