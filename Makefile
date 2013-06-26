# Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
# Copyright (C) 2013  Inria (Institut National de Recherche
#                     en Informatique et en Automatique)
# See LICENSE for licensing details.

TARGET := profound

OCB_FLAGS := -classic-display -j 4

OCB := _build/myocamlbuild -use-ocamlfind ${OCB_FLAGS}

.PHONY: all debug clean top

all: _build/myocamlbuild
	${OCB} -no-plugin ${TARGET}.native

debug: all
	${OCB} -no-plugin ${TARGET}.cma

_build/myocamlbuild: myocamlbuild.ml
	ocamlbuild -just-plugin

clean:
	ocamlbuild -no-plugin ${OCB_FLAGS} -clean
	${RM} version.ml

top:
	${MAKE} debug >/dev/null 2>&1
	OCAMLRUNPARAM=b ocaml
