Require Export base.

(* The set of propositional variables. *)
Inductive prop : Set :=
  p : nat -> prop.

(* Valuation function *)
Definition valuation (W: Set) : Type := set (prop * W).

Structure model := {
  m_states :> Set;
  m_rel : relation m_states;
  m_val: valuation m_states
}.

Structure pointed_model := {
  pm_model :> model;
  pm_point : pm_model
}.

Structure state_model (W: Set) := {
  st_point: W;
  st_rel: relation W;
  st_val: valuation W
}.

Definition muf : Type := forall (W : Set),
  state_model W -> set (state_model W).


Notation "⟨ a , b , c ⟩" :=
  {| st_point := a; st_val := c; st_rel := b |}.

Notation "⟪ a , b , c ⟫, m" :=
  {| pm_model := {| m_states := a; m_rel := b; m_val := c |};
     pm_point := m |} (at level 0).

Arguments st_point {W}.
Arguments st_rel {W}.
Arguments st_val {W}.

Definition to_pm {W} (st: state_model W) :=
  ⟪ _, st.(st_rel), st.(st_val) ⟫, (st.(st_point)).

Coercion to_pm: state_model >-> pointed_model.

Definition to_st 𝔐 := ⟨𝔐.(pm_point), 𝔐.(m_rel), 𝔐.(m_val)⟩.

Coercion to_st: pointed_model >-> state_model.

Lemma to_st_val (𝔐: pointed_model) : m_val 𝔐 = st_val 𝔐.
  by [].
Qed.

Lemma to_st_point (𝔐: pointed_model) : pm_point 𝔐 = st_point 𝔐.
  by [].
Qed.

Lemma to_st_to_pm {W} (st: state_model W): to_st (to_pm st) = st.
  by case: st.
Defined.
