Z3_SRC_ROOT = ./z3

default:
	ocamlfind ocamlopt -o aa -package zarith -I $(Z3_SRC_ROOT)/build/api/ml \
	-cclib "-L$(Z3_SRC_ROOT)/build/ -lpthread -lstdc++ -lz3" -linkpkg z3ml.cmxa aa.ml

.PHONY: clean
clean:
	rm -f *.cm* *.log *.o *.byte aa ml_example

ml_example.byte: clean
	ocamlfind ocamlc -custom -o ml_example.byte -package zarith -I $(Z3_SRC_ROOT)/build/api/ml \
	-cclib "-L$(Z3_SRC_ROOT)/build/ -lpthread -lstdc++ -lz3" -linkpkg z3ml.cma ml_example.ml
ml_example$(EXE_EXT): clean
	ocamlfind ocamlopt -o ml_example$(EXE_EXT) -package zarith -I $(Z3_SRC_ROOT)/build/api/ml \
	-cclib "-L$(Z3_SRC_ROOT)/build/ -lpthread -lstdc++ -lz3" -linkpkg z3ml.cmxa ml_example.ml

.PHONY: run
run:
	./aa

.PHONY: run_ml_example
run_ml_example:
	./ml_example

.PHONY: all
all: clean default



