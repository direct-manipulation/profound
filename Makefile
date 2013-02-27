TARGET := profound

OCB := _build/myocamlbuild -use-ocamlfind

.PHONY: all debug clean top

all: _build/myocamlbuild
	${OCB} -no-plugin ${TARGET}.native

debug: all
	${OCB} -no-plugin ${TARGET}.cma

_build/myocamlbuild: myocamlbuild.ml
	ocamlbuild -just-plugin

clean: _build/myocamlbuild
	${OCB} -clean
	${RM} version.ml

top:
	${MAKE} debug >/dev/null 2>&1
	OCAMLRUNPARAM=b ocaml
