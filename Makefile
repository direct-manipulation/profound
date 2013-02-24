TARGET := profound

OCB := ocamlbuild -use-ocamlfind

.PHONY: all clean top

all:
	${OCB} ${TARGET}.cma ${TARGET}.native

clean:
	${OCB} -clean
	${RM} version.ml

top:
	OCAMLRUNPARAM=b ocaml
