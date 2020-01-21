Require Import ssreflect.
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
Definition val (W: Set) : Type := W -> prop -> Prop.

Definition point (W: Set) : Type := (W * relation W * val W).

Definition value {W} (p: point W) :=
  let '(v, _, _) := p in v.
Definition rel {W} (p: point W) :=
  let '(_, r, _) := p in r.
Definition valuation {W} (p: point W) :=
  let '(_, _, v) := p in v.

Definition muf : Type := forall (W : Set),
  point W -> (point W -> Prop).

Variable F : Dyn -> muf.

Fixpoint satisfies (W : Set) (p: point W) (phi : form) : Prop :=
  match phi with
  | Atom a => valuation p (value p) a
  | Bottom => False
  | If phi1 phi2 => (satisfies W p phi1) -> (satisfies W p phi2)
  | DynDiam d phi =>
    let fw := F d W in
    exists p', fw p p' /\ satisfies W p' phi
  end.

Notation "<< W , p >> |= phi" := (satisfies W p phi) (at level 30).

(* Semantic Definitions *)
Variables W W' : Set.

Definition equivalent_at_points p p' :=
  forall (phi:form), (<<W , p>> |= phi) <-> (<<W' , p' >> |= phi).

Definition model_to_model_relation : Type :=
  point W -> point W' -> Prop.

Variable Z : model_to_model_relation.

Definition atomic_harmony : Prop :=
  forall p p', Z p p' -> valuation p (value p) = valuation p' (value p').

Definition f_zig (f : muf) : Prop :=
  forall p q p', Z p p' ->
    f W p q ->
    (exists q', f W' p' q' /\ Z q q').

Definition f_zag (f : muf) : Prop :=
  forall p q' p', Z p p' ->
    f W' p' q' ->
    (exists q, f W p q /\ Z q q').

Definition bisimulation : Prop :=
  atomic_harmony /\
  (forall d : Dyn, (f_zig (F d))) /\ (forall d : Dyn, (f_zag (F d))).

Definition bis_at_points (p: point W) (p': point W') : Prop :=
  bisimulation /\ Z p p'.

(* Theorem *)

Theorem InvarianceUnderBisimulation :
forall (p: point W) (p': point W'),
    bis_at_points p p' -> equivalent_at_points p p'.

Proof.
  intros p p'. (* name each component of the points *)
  unfold bis_at_points.          (* unfold definitions *)
  unfold equivalent_at_points.
  unfold bisimulation.

  intros [[HAtomicHarmony [HFZig HFZag]] HZwSw'S'].
  intros phi.
  
  generalize dependent p'. generalize dependent p.
  
  induction phi as [prop | | phi IHphi psi IHpsi | d phi IH];
  simpl.                (* This tactic unfolds definitions *)
  + intros p p' HZpp'. rewrite (HAtomicHarmony _ _ HZpp'). tauto.
  + tauto.
  + intros p p'; split;
    intros HIf Hsat;
    apply (IHpsi _ _ HZwSw'S');
    apply HIf;
    apply (IHphi _ _ HZwSw'S');
    apply Hsat.
  + intros p p'. split; simpl.
    - intros [q [HfWpp' Hsatq]].
      apply (HFZig _ _ _ _ HZwSw'S') in HfWpp'
          as [q' [HfW'q'p' HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply IH. eassumption.
        assumption.
    - intros [q' [HfWpp' Hsatq']].
      apply (HFZag _ _ _ _ HZwSw'S') in HfWpp'
          as [q [HfWpq HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply IH. eassumption. assumption.
Qed.

End invarianceTheorem.
