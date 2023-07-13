Require Import 
  (* classic logic axioms *)
  logic.

(* Definition of basic modal logic as an instance of our generic notion
   of modal dynamic logic.
*)

(* Diamond of the basic modal language, as a dynamic operator.  *)
Module BmlDyn <: DYN.
  (* TODO: we need to redefine BML's diamond each time that we want to extend
     BML with some new dynamic operator *)
  Definition diamond : muf :=
    fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
      R w v /\ R = R' /\ V = V'.

  Inductive BmlDynOp := Diamond.

  Definition Dyn := BmlDynOp.

  Definition F (f: Dyn) : muf :=
    match f with
    | Diamond => diamond
    end.

End BmlDyn.
