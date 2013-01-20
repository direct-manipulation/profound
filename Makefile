TARGET := profound

OCB := ocamlbuild -classic-display -use-ocamlfind -no-log

.PHONY: all clean top

all:
	${OCB} ${TARGET}.cma ${TARGET}.native

clean:
	${OCB} -clean

top:
	OCAMLRUNPARAM=b ocaml
