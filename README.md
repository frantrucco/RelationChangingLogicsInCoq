# RelationChangingLogicsInCoq

This repository contains the code for various on-going verification
efforts in dynamic logics, written in the [Coq](https://coq.inria.fr)
proof assistant.

The code specific to the paper _Mechanizing Bisimulation Theorems for
Relation-Changing Logics in Coq_ presented at _The 2nd Dalí Workshop_
is located in the tag **dali19**.

## How to compile

The code was tested on Coq 8.10. It requires the
[Mtac2](https://github.com/Mtac2/Mtac2) and a subset of the
Mathematical Components plugins. To install the dependencies it is
best to use [Opam](http://opam.ocaml.org) and type in a terminal
window:

```bash
$ opam repo add coq-released https://coq.inria.fr/opam/released 
$ opam install coq-mathcomp-finmap coq-mtac2
```

And then:
    
```
$ coq_makefile -f _CoqProject -o Makefile
$ make
```

## Structure of the code

In the `theories` directory you will find the following files:

- `utilities.v`: contains a series of helpful definitions. At the
   moment, it contains the following modules:

   + `Sets`: notations and missing aspects from the `Enembles` file in
     the std.
   + `Tactics`: tactics used in the development.

- `base.v`: contains the exports needed for the rest of the
  development.

- `models.v` contains the definitions for _model_, _pointed model_,
  and the like.

- `logic.v`: defines the syntax and semantics of the meta-logic in a
  _functor_ parametrized in by the set of dynamic operators and their
  corresponding _model update functions_. In order to work with this
  functor you might want to look at the file `examples.v`, if you need
  to define a new logic; or `invariance.v`, if you want to prove a
  meta-property of the meta-logic.

- `invariance.v`: the proof for the theorem of _invariance under
  bisimulation_, that is, that two bisimilar models are equivalent.

- `hennessyMilner.v`: the proof for the _Hennessy-Milner_ theorem,
  which states that, under certain conditions, two equivalent models
  are bisimilar.

- `examples.v`: instantiations with specific logics, and proof of
  logic-specific properties.
