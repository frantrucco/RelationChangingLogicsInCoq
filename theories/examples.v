Require Import logic.

Definition diamond : muf :=
  fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
     R w v /\ R = R' /\ V = V'.

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

Variable poison_atom : prop.
Notation "p∙" := poison_atom.

Definition F (d: Dyn) : muf :=
  match d with
  | Diamond => diamond
  | Poison => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
     R w v /\ R' = R /\ V' = (V ∪ ⦃(p∙, w)⦄)
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

Section WeirdExample.

Fixpoint delta n : form :=
  match n with
  | 0 => ⃟p∙
  | S n' => ⃟(~'p∙ /\' delta n')
  end.


Definition R : relation nat := fun n m=>
  ((n == 0) && (m == 1)) ||
  ((n == 1) && (m == 2)) ||
  ((n == 2) && (m == 0)).

Definition V : valuation nat := ∅.

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

Example cycle : ⟨0, R, V⟩ |= ⬙ (delta 1).
Proof.
exists ⟨1, R, V ∪ p 0⟩.
split_ands; try by [].
exists ⟨2, R, V ∪ p 0⟩.
split_ands; try by [].
rewrite sat_and.
split.
- simpl.
  move=>H.
  mrun (T.select (_ ∈ _) >>= inversion).
  * mrun (T.select (_ ∈ V) >>= inversion).
  * mrun (T.select (_ ∈ p 0) >>= inversion).
- exists ⟨0, R, V ∪ p 0⟩.
split_ands; try by [].
apply Union_intror.
by [].
Qed.

End WeirdExample.

Definition Rcycle := fun n m=>
  ((n == 0) && (m == 0)).

Example cycle' : ⟨0, Rcycle, ∅⟩ |= ⬙ p∙.
Proof.
  exists ⟨0, Rcycle, V ∪ p 0⟩.
  rewrite /Ensembles.In /=.
  split_ands; try by [].
  apply: Union_intror.
  by [].
Qed.
