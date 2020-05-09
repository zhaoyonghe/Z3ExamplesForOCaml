# Z3 Examples For OCaml
## Description
The OCaml code in this repo reimplements the examples in this link: https://theory.stanford.edu/~nikolaj/programmingz3.html.
There is no tutorial now on the internet for z3 OCaml bindings, so this repo might be a good study material. 
## Set up the environment
### Ubuntu-18.04
First clone the z3 repo.
```
$ git clone https://github.com/Z3Prover/z3.git
```
Then on the root directory of the downloaded z3 folder, run these commands to build the source code.
```
$ sudo apt-get install ocaml opam libgmp-dev
$ opam init -y
$ eval `opam config env`; opam install zarith ocamlfind -y
$ python scripts/mk_make.py --ml --staticlib
$ set -e
$ cd build
$ eval `opam config env` 
$ make -j3
```
Then change the `Z3_SRC_ROOT` in `Makefile` to the root directory of the downloaded z3 folder so that the z3 library can be found. 
For example:
```
Z3_SRC_ROOT = ./z3
```
## A quick start
To rebuild my example code:
```
$ make all
```
To run my example code:
```
$ make run
```
To rebuild the official example code:
```
$ make ml_example
```
To run the official example code:
```
$ make run_ml_example
```
To clean the build:
```
$ make clean
```
## Other useful links on studying the z3 OCaml bindings
- https://z3prover.github.io/api/html/ml/Z3.html
- https://github.com/Z3Prover/z3/tree/master/src/api/ml
- https://github.com/Z3Prover/z3/tree/master/src/api/python/z3 (You can study the OCaml bindings by reading its python counterpart)
