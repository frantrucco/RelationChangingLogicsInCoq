Require Import logic.

Definition diamond : muf :=
  fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
     R w v /\ R = R' /\ V = V'.

(* In this file we will define a number of examples of dynamic modal
   logics with concrete sets of dynamic operators and their
   corresponding model update functions.

   To achieve this goal we need to define modules that satisfy the
   signature given by the module type DYN. Once we have these modules
   we can apply the functor DynLogic to each of them to obtain the
   corresponding dynamic modal logics.

   We could define our modules directly with the type DYN.
   Unfortunately, this would restrict the interface. If the interface
   is restricted we can no longer access any local definition in the
   module that is not part of the module type.

   The other option is to ignore the type and define our module
   without any type. But we want to be sure that our implementation
   satisfies the module type DYN!

   Thankfully, Coq provides a way to do this by using a transparent
   constraint:

*)

Module SbDyn <: DYN.

Inductive SbDyn := Diamond | Sb.
Definition Dyn := SbDyn.

Import RelationClasses.

Definition rel_minus {W} (R: relation W) (w v: W) : relation W :=
  fun w' v'=>
  (w = w' /\ v = v' -> False) \/ (w <> w' \/ v <> v' -> R w' v').

Definition F (f: Dyn) : muf :=
  match f with
  | Diamond => diamond
  | Sb => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
     R w v /\ R' = rel_minus R w v /\ V' = V
  end.

End SbDyn.

Module SbExample.
Module SbDynLogic := DynLogic SbDyn.
Import SbDynLogic.
Import SbDyn.

Notation "⃟ φ" := (DynDiam Diamond φ)
                     (at level 65, right associativity).

Notation "'⃟sb' φ" := (DynDiam Sb φ)
                     (at level 65, right associativity).

Example valid_in_sb : forall (p:prop) pm, pm |= ⃟sb p ->' ⃟p.
Proof.
  move=>p [ [W R] V] /= w [ [v R'] V'] /=.
  rewrite /Ensembles.In /=.
  move => [ [ ? [ ? ?]] ?].
  eexists ⟨v, _, V⟩.
  by subst.
Qed.

End SbExample.

Module PoisonDyn <: DYN.

Inductive PoisonDyn := Diamond | Poison.
Definition Dyn := PoisonDyn.

Context (poison_atom : prop).
Notation "p∙" := poison_atom.

Definition F (d: Dyn) : muf :=
  match d with
  | Diamond => diamond
  | Poison => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
     R w v /\ R' = R /\ V' = (V ∪ ⦃(p∙, v)⦄)
  end.

End PoisonDyn.

Module PoisonDynLogic := DynLogic PoisonDyn.
Import PoisonDynLogic.
Import PoisonDyn.

Notation "⃟ φ" := (DynDiam Diamond φ)
                     (at level 65, right associativity).

Notation "'⬙' φ" := (DynDiam Poison φ)
                     (at level 65, right associativity).

Let p (n:nat) := ⦃(p∙, n)⦄.

Fixpoint delta n : form :=
  match n with
  | 0 => ⊥'
  | 1 => ⃟p∙
  | S n' => ⃟(~'p∙ /\' delta n')
  end.


Definition V0 : valuation nat := ∅.

Lemma curry : forall P Q R:Prop, (P /\ Q -> R) <-> (P -> Q -> R).
Proof. move=>P Q R. split; tauto. Qed.

Theorem notnot : forall P, (~ (~P)) <-> P.
Proof.
  move=>P.
  split; last by tauto.
  by case: (classic P).
Qed.

Lemma sat_and st φ ψ: st |= (φ /\' ψ) <-> st|=φ /\ st|=ψ.
Proof.
  split.
  - rewrite /= -curry.
    fold (not (st |= φ /\ st |= ψ )).
    fold (not (not (st |= φ /\ st |= ψ ))).
    by rewrite notnot.
  - move=>[Hφ Hψ].
    simpl.
    by apply.
Qed.

Ltac cycle_one_step :=
  split_ands; try by [];
  rewrite sat_and;
  split; first by (
  simpl;
  move=>?;
  mrun (T.select (_ ∈ _) >>= inversion);
  [mrun (T.select (_ ∈ V0) >>= inversion)
  | mrun (T.select (_ ∈ p _) >>= inversion)]).

Ltac cycle_end :=
  split_ands; try by [];
  simpl;
  by apply Union_intror.


Definition R_cycle2 : relation nat := fun n m=>
  ((n == 0) && (m == 1)) ||
  ((n == 1) && (m == 2)) ||
  ((n == 2) && (m == 1)).

Example cycle2 : ⟨0, R_cycle2, V0⟩ |= ⬙ (delta 2).
Proof.
  pose R := R_cycle2.
  pose V1 := V0 ∪ p 1.
  exists ⟨1, R, V1⟩.
  split_ands; try by [].
  exists ⟨2, R, V1⟩.
  cycle_one_step.
  exists ⟨1, R, V1⟩.
  cycle_end.
Qed.


Definition R_cycle1 : relation nat := fun n m=>
  ((n == 0) && (m == 1)) ||
  ((n == 1) && (m == 1)).

Example cycle1 : ⟨0, R_cycle1, V0⟩ |= ⬙ (delta 1).
Proof.
  pose R := R_cycle1.
  pose V1 := V0 ∪ p 1.
  exists ⟨1, R, V1⟩.
  split_ands; try by [].
  exists ⟨1, R, V1⟩.
  cycle_end.
Qed.

Definition R_cycle4 : relation nat := fun n m=>
  ((n == 0) && (m == 1)) ||
  ((n == 1) && (m == 2)) ||
  ((n == 2) && (m == 2)) ||
  ((n == 2) && (m == 1)).

Example cycle4 : ⟨0, R_cycle4, V0⟩ |= ⬙ (delta 3).
Proof.
  pose R := R_cycle4.
  pose V1 := V0 ∪ p 1.
  exists ⟨1, R, V1⟩.
  split_ands; try by [].
  exists ⟨2, R, V1⟩.
  cycle_one_step.
  exists ⟨2, R, V1⟩.
  cycle_one_step.
  exists ⟨1, R, V1⟩.
  cycle_end.
Qed.


Definition Rcycle := fun n m=>
  ((n == 0) && (m == 0)).

Example cycle' : ⟨0, Rcycle, ∅⟩ |= ⬙ p∙.
Proof.
  exists ⟨0, Rcycle, V0 ∪ p 0⟩.
  cycle_end.
Qed.
