TARGET := profound

OCB := ocamlbuild -classic-display -use-ocamlfind -no-log

.PHONY: all clean

all:
	${OCB} ${TARGET}.cma ${TARGET}.native

clean:
	${OCB} -clean
