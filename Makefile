default:
	ocamlfind ocamlopt -o aa -package z3 -linkpkg aa.ml

example:
	ocamlfind ocamlopt -o ml_example -package z3 -linkpkg ml_example.ml

.PHONY: clean
clean:
	rm -f ml_example ml_example.cm* *.log
	rm -f aa aa.cm* *.log

.PHONY: run
run:
	LD_LIBRARY_PATH=/home/w4118/.opam/system/lib/z3 ./aa

.PHONY: runex
runex:
	LD_LIBRARY_PATH=/home/w4118/.opam/system/lib/z3 ./ml_example

.PHONY: all
all: clean default