Require Export models.

(* When we give a mathematical definition of a concept sometimes we
   parametrize this definition by a mathematical object. So for
   instance, when we give the definition of what a formula is in a
   dynamic logic we parametrize this definition by a set of dynamic
   operators. Then, when we talk of a particular set of dynamic
   formulas we specify the set of operators we are using and by doing
   this we define a concrete set of formulas.

   Certainly it would be highly inconvenient if a proof assistant
   didn't have this particular form of abstraction. Imagine having to
   repeat all the definitions that make a dynamic logic (e.g., the set
   of formulas, the semantics, the notion of equivalent models, etc.)
   separately for each concrete dynamic logic. This would be
   innaceptable.

   One elegant solution of this problem in Coq is to use modules,
   module types and parameterized modules (aka functors).

   Modules will allows us to wrap our mathematical definitions,
   theorems and proofs and anything else that we could do in the
   toplevel. Module types specify the general shape and type
   properties of modules. A parameterized module is a module that
   depends on a parameter. This parameter must also be module.

   We now define the module type (or signature) DYN as consisting of:

   - A dynamic set of operators Dyn with type Set and

   - A function F with type (Dyn -> muf) that maps each dynamic
   operator to its corresponding model update function.

   By using this module type we can pack together these two concepts.

   A module D of module type DYN would consist of:

   - A concrete set of dynamic operators D.Dyn and

   - A concrete mapping D.F between these dynamic operators and their
   corresponding muf.

   Notice how we used the dot operator to access the components of the
   module D.

   The reader can find examples of modules of type DYN in the file
   examples.v.

*)

Module Type DYN.
Context (Dyn : Set).
Context (F : Dyn -> muf).
End DYN.

(* Here we define a parameterized module DynLogic that expects as a
   parameter a module D of module type DYN. This means that inside
   this module we can assume the existence of:

   - A set of dynamic operators D.Dyn and

   - A mapping D.F between these dynamic operators and their
   corresponding muf.

   This parameterization allows us to give all of the definitions that
   depend on D.Dyn and on D.F without assuming a particular set of
   dynamic operators. Moreover, we can later take this functor and
   apply it to a module D of type DYN to obtain a module with all the
   definitions of the concrete dynamic logic with the dynamic
   operators defined in the parameter D.

   The reader can find examples of modules that are the result of
   applications of this functor (i.e., concrete dynamic logics) in
   the file examples.v.

*)

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
