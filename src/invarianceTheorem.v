From Coq.Relations Require Import Relations.

Section invarianceTheorem.

(* Syntax *)
Variable Dyn : Set.

Inductive prop : Set :=
  p : nat -> prop.

Inductive form : Type :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | DynDiam : Dyn -> form -> form.

(* Syntactic sugar *)
Definition Not (phi : form) : form :=
If phi Bottom.

Definition Top : form :=
Not Bottom.

Definition And (phi psi : form) : form :=
Not (If phi (Not psi)).

Definition Or (phi psi : form) : form :=
If (Not phi) psi.

Definition Iif (phi psi : form) : form :=
And (If phi psi) (If psi phi).

Definition DynBox (d : Dyn) (phi : form) : form :=
Not (DynDiam d (Not phi)).

(* Notation *)

Notation "p /\' q" := (And p q)
                     (at level 80, right associativity).

Notation "p \/' q" := (Or p q)
                     (at level 85, right associativity).

Notation "~' p" := (Not p)
                   (at level 70, right associativity).

Notation "p ->' q" := (If p q)
                     (at level 90, right associativity).

Notation "p <->' q" := (Iif p q)
                     (at level 95, right associativity).

Notation "<o> d phi" := (DynDiam d phi)
                        (at level 65, right associativity).

Notation "[o] d phi" := (DynBox d phi)
                        (at level 65, right associativity).

(* Semantics *)

Definition point (W: Set) : Type := (W * relation W).

Definition muf : Type := forall (W : Set),
(point W) -> (point W -> Prop).

Variable F : Dyn -> muf.

Fixpoint satisfies (W : Set) (R : W -> W -> Prop) (V : W -> prop -> Prop)
                    (w : W) (phi : form) : Prop :=
match phi with
| Atom a => V w a
| Bottom => False
| If phi1 phi2 => (satisfies W R V w phi1) -> (satisfies W R V w phi2)
| DynDiam d phi =>
    let fw := F d W in
    exists (v : W) (R' : W -> W -> Prop), fw (w, R) (v, R') /\ satisfies W R' V v phi
end.

Notation "# W , R , V >> w |= phi" := (satisfies W R V w phi) (at level 30).

(* Semantic Definitions *)
Variables W W' : Set.

Variables (V : W -> prop -> Prop) (V' : W' -> prop -> Prop).

Definition equivalent_at_points '(w, R) '(w', R') :=
forall (phi:form), (# W , R , V >> w |= phi) <-> (# W' , R' , V' >> w' |= phi).

Definition model_to_model_relation : Type :=
(point W) -> (point W') -> Prop.

Variable Z : model_to_model_relation.

Definition atomic_harmony : Prop :=
forall w S w' S', Z (w, S) (w', S') -> V w = V' w'.

Definition f_zig (f : muf) : Prop :=
forall w S w' S' v T, Z (w, S) (w', S') ->
    f W (w, S) (v, T) ->
    (exists (v' : W') T', f W' (w', S') (v', T') /\ Z (v, T) (v', T')).

Definition f_zag (f : muf) : Prop :=
forall w S w' S' v' T', Z (w, S) (w', S') ->
    f W' (w', S') (v', T') ->
    (exists (v : W) T, f W (w, S) (v, T) /\ Z (v, T) (v', T')).

Definition bisimulation : Prop := atomic_harmony /\
(forall d : Dyn, (f_zig (F d))) /\ (forall d : Dyn, (f_zag (F d))).

Definition bis_at_points (p: point W) (p': point W') : Prop :=
bisimulation /\ Z p p'.

(* Theorem *)

Theorem InvarianceUnderBisimulation :
forall (p: point W) (p': point W'),
    bis_at_points p p' -> equivalent_at_points p p'.

Proof.
  intros [w S] [w' S'].           (* name each component of the points *)
  unfold bis_at_points.                          (* unfold definitions *)
  unfold equivalent_at_points.
  unfold bisimulation.

  intros [[HAtomicHarmony [HFZig HFZag]] HZwSw'S'].
  intros phi.
  generalize dependent S'. generalize dependent S.
  generalize dependent w'. generalize dependent w.

  induction phi as [p | | phi IHphi psi IHpsi | d phi IH].
  simpl;                (* This tactic unfolds definitions *)
  intros w w' S S' HZwSw'S'.
  + rewrite (HAtomicHarmony w S w' S' HZwSw'S'). tauto.
  + tauto.
  + split;
    intros HIf Hsat;
    apply (IHpsi w w' S S' HZwSw'S');
    apply HIf;
    apply (IHphi w w' S S' HZwSw'S');
    apply Hsat.
  + split. simpl.
    - intros [v [T [HfWwSvT HsatTv]]].
      apply (HFZig d w S w' S' v T HZwSw'S') in HfWwSvT
          as [v' [T' [HfW'w'S'v'T' HZvTv'T']]].
      exists v'. exists T'.
      split.
      * assumption.
      * eapply IH. apply HZvTv'T'. assumption.
    - intros [v [T [HfWwSvT HsatTv]]].
      apply (HFZag d w S w' S' v T HZwSw'S') in HfWwSvT
          as [v' [T' [HfW'w'S'v'T' HZvTv'T']]].
      exists v'. exists T'.
      split.
      * assumption.
      * eapply IH. apply HZvTv'T'. assumption.
Qed.

End invarianceTheorem.
