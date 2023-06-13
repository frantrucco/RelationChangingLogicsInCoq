Require Import 
  (* classic logic axioms *)
  logic.

(* Definition of a BML + universal modality as an instance of our generic notion
   of modal dynamic logic.
*)

(* Diamond form of the universal modality, and diamond of the basic modal 
   language, as dynamic operators.  *)
Module UniDyn <: DYN.
  (* TODO: we need to redefine BML's diamond each time that we want to extend
     BML with some new dynamic operator *)
  Definition diamond : muf :=
    fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
      R w v /\ R = R' /\ V = V'.

  Inductive UniDynOp := E | Diamond.

  Definition Dyn := UniDynOp.

  Definition F (f: Dyn) : muf :=
    match f with
    | Diamond => diamond
    | E => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩ =>
            (* We do not force some constraint over v. We just
               need v : W, which is enforced by type-checking. *)
            R = R' /\ V = V'
    end.

End UniDyn.

(* We instantiate a new dynamic logic with E and Diamond as its dynamic 
   operators *)
Module UniExample.
  Module UniDynLogic := DynLogic UniDyn.
  Import UniDynLogic.
  Import UniDyn.
  
  Notation "⃟ φ" := (DynDiam Diamond φ)
                     (at level 65, right associativity).

  Notation "'E' φ" := (DynDiam E φ)
                        (at level 65, right associativity).

  (* We can force the existence of infinite decreasing chains in the accessibility
     relation, using E.  *)
  Example decreasing_chains : 
    forall W R, 
    (forall V w, ⟪ W , R , V ⟫, w |= (Top ->' E ⃟ Top)) <-> forall x, exists y, R y x.
  Proof.
  Admitted.

End UniExample.
