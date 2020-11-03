Require Export models.

(* General definitions *)
Module Type DYN.
Variable Dyn : Set.
Variable F : Dyn -> muf.
End DYN.

Module DynLogic (D: DYN).

(* Syntax *)

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | Impl    : form -> form -> form
  | DynDiam : D.Dyn -> form -> form.

Coercion Atom : prop >-> form.

(* Basic notation *)
Notation "⊥'" := Bottom.

Notation "p ->' q" := (Impl p q)
                     (at level 90, right associativity).

Notation "⃟ f φ" := (DynDiam f φ)
                     (at level 65, f at level 9, right associativity).

(* Syntactic sugar *)
Definition Not (φ : form) : form := φ ->' ⊥'.

Notation "~' p" := (Not p)
                   (at level 70, right associativity).

Definition Top : form := ~'⊥'.

Notation "⊤'" := Top.

Definition And (φ ψ : form) : form := ~' (φ ->' ~'ψ).

Notation "p /\' q" := (And p q)
                     (at level 80, right associativity).

Definition Or (φ ψ : form) : form := ~'φ ->' ψ.

Notation "p \/' q" := (Or p q)
                     (at level 85, right associativity).

Definition Iif (φ ψ : form) : form := (φ ->' ψ) /\' (ψ ->' φ).

Notation "p <->' q" := (Iif p q)
                     (at level 95, right associativity).

Definition DynBox (d : D.Dyn) (φ : form) : form := ~'⃟ d ~'φ.

Notation "⃞ d φ" := (DynBox d φ)
                     (at level 65, d at level 9, right associativity).


(* Semantics *)

Reserved Notation "p |= φ" (at level 30).

Fixpoint satisfies (𝔐: pointed_model) (φ : form) : Prop :=
  match φ with
  | Atom a => (a, 𝔐.(pm_point)) ∈ 𝔐.(m_val)
  | Bottom => False
  | φ1 ->' φ2 => (𝔐 |= φ1) -> (𝔐 |= φ2)
  | ⃟f φ =>
    let fw := D.F f 𝔐.(m_states) in
    exists p', p' ∈ fw 𝔐  /\  p' |= φ
  end
where "𝔐 |= φ" := (satisfies 𝔐 φ).

Definition big_and Δ := fold_right And Top Δ.

Notation "'⋀' Δ" := (big_and Δ) (at level 0).

Lemma sat_fold_forall m Δ:
  Forall (fun φ : form => m |= φ) Δ <-> m |= ⋀Δ.
Proof.
  elim: Δ; first by simpl; tauto.
  move=>φ Δ /= ->.
  tauto.
Qed.

Theorem sat_classic : forall st φ, st |= φ \/ st |= ~' φ.
Proof. by move=>*; apply: classic. Qed.

Definition equivalent (𝔐 𝔐': pointed_model) :=
  forall (φ: form), (𝔐 |= φ) <-> (𝔐' |= φ).

Notation "m ≡ m'" := (equivalent m m') (at level 0).

(* Semantic Definitions *)
Section Bisimulation.

Context {W W' : Set}.

Definition state_model_relation : Type :=
  state_model W -> state_model W' -> Prop.

Context (Z : state_model_relation).

Definition atomic_harmony : Prop :=
  forall p p', Z p p' -> forall pr: prop,
      (pr, p.(st_point)) ∈ p.(st_val) <-> (pr, p'.(st_point)) ∈ p'.(st_val).


Definition f_zig (f : muf) : Prop :=
  forall p q p', Z p p' ->
    q ∈ f W p ->
    (exists q', q' ∈ f W' p' /\ Z q q').

Definition f_zag (f : muf) : Prop :=
  forall p q' p', Z p p' ->
    q' ∈ f W' p' ->
    (exists q, q ∈ f W p /\ Z q q').

Definition bisimulation : Prop :=
  atomic_harmony /\
  (forall d, f_zig (D.F d)) /\
  (forall d, f_zag (D.F d)).

End Bisimulation.

Definition bisimilar (𝔐 𝔐': pointed_model) : Prop :=
  exists Z, bisimulation Z /\ Z 𝔐 𝔐'.

Notation "𝔐 ⇆ 𝔐'" := (bisimilar 𝔐 𝔐') (at level 30).

Arguments state_model_relation : clear implicits.

Section Getters.

Context {W W' : Set}.
Context {Z: state_model_relation W W'}.
Context (bis: bisimulation Z).

Definition get_AH : atomic_harmony Z.
  move: bis =>[HA _].
  exact: HA.
Defined.

Definition get_Zig d : f_zig Z (D.F d).
  move: bis =>[_ [H _]].
  exact: H.
Defined.

Definition get_Zag d : f_zag Z (D.F d).
  move: bis =>[_ [_ H]].
  exact: H.
Defined.

End Getters.

End DynLogic.

(* Local Variables: *)
(* company-coq-local-symbols: ( ) *)
(* End: *)
