# RelationChangingLogicsInCoq

This repository contains the code for various on-going verification
efforts in dynamic logics, written in the [Coq](https://coq.inria.fr)
proof assistant.

The code specific to the paper _Mechanizing Bisimulation Theorems for
Relation-Changing Logics in Coq_ presented at _The 2nd Dalí Workshop_
is located in the tag **dali19**.

## How to compile utilities.v

Simply run:
    
```
$ coq_makefile -f _CoqProject -o CoqMakefile
$ mv CoqMakefile Makefile
$ make
```
