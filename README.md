# RelationChangingLogicsInCoq

This repository contains the code for various on-going verification
efforts in dynamic logics, written in the [Coq](https://coq.inria.fr)
proof assistant.

The code specific to the paper _Mechanizing Bisimulation Theorems for
Relation-Changing Logics in Coq_ presented at _The 2nd Dalí Workshop_
is located in the tag **dali19**.

## How to compile

The code was tested on Coq 8.10. It requires the [Mtac2](https://github.com/Mtac2/Mtac2) and a subset of the Mathematical Components plugins. To install the dependencies it is best to use [Opam](http://opam.ocaml.org) and then type:
```bash
$ opam install coq-mathcomp-finset coq-mtac2
```

And then:
    
```
$ coq_makefile -f _CoqProject -o Makefile
$ make
```
