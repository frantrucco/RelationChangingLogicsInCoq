From Mtac2 Require Import Mtac2.
From Coq.Sets Require Import Constructive_sets.
From Coq.Relations Require Import Relations.
From Coq.Lists Require Import List.
From RCLIC Require Import utilities.

Require Import Classical.

Require Import ssreflect.

(* This removes the requirement to have all goals with the same
   hierarchy. For instance, without it, one must write:

   have a_hypothesis : some_prop.
   - the proof of some_prop.
   - the proof continues here.

   which is less convenient than

   have a_hypothesis : some_prop.
   - the proof of some_prop.
   the proof continues here.
*)
Set Bullet Behavior "None".


Import Tactics.
Import Sets.

(* General definitions *)

(* The set of propositional variables. *)
Inductive prop : Set :=
  p : nat -> prop.

(* Valuation function *)
Definition valuation (W: Set) : Type := W -> prop -> Prop.

Structure model := {
  m_states :> Set;
  m_rel : relation m_states;
  m_val: valuation m_states
}.

Structure pointed_model := {
  pm_model :> model;
  pm_point : pm_model.(m_states)
}.

Structure state_model (W: Set) := {
  st_point: W; st_rel: relation W; st_val: valuation W
}.

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

Definition to_st 𝕸 := ⟨𝕸.(pm_point), 𝕸.(m_rel), 𝕸.(m_val)⟩.

Coercion to_st: pointed_model >-> state_model.

Lemma to_st_val (𝕸: pointed_model) : m_val 𝕸 = st_val 𝕸.
  by [].
Qed.

Lemma to_st_point (𝕸: pointed_model) : pm_point 𝕸 = st_point 𝕸.
  by [].
Qed.

Lemma to_st_to_pm {W} (st: state_model W): to_st (to_pm st) = st.
  by case: st.
Defined.

Section InvarianceTheorem.

(* Syntax *)
Variable Dyn : Set.
Variable d : Dyn.

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | DynDiam : form -> form.

Coercion Atom : prop >-> form.

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

Definition DynBox (phi : form) : form :=
  Not (DynDiam (Not phi)).

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

Notation "⬦ phi" := (DynDiam phi)
                        (at level 65, right associativity).

Notation "◻ phi" := (DynBox phi)
                        (at level 65, right associativity).

(* Semantics *)

Definition muf : Type := forall (W : Set),
  state_model W -> set (state_model W).

Variable F : Dyn -> muf.

Fixpoint satisfies (pm: pointed_model) (phi : form) : Prop :=
  match phi with
  | Atom a => pm.(m_val) pm.(pm_point) a
  | Bottom => False
  | If phi1 phi2 => (satisfies pm phi1) -> (satisfies pm phi2)
  | DynDiam phi =>
    let fw := F d pm.(m_states) in
    exists p', p' ∈ fw pm /\ satisfies p' phi
  end.

Notation "p |= phi" := (satisfies p phi) (at level 30).

Theorem sat_classic : forall st ϕ, st |= ϕ \/ st |= ~' ϕ.
Proof.
  move=>st ϕ.
  apply: classic.
Qed.

Definition equivalent (𝕸 𝕸': pointed_model) :=
  forall (ϕ: form), (𝕸 |= ϕ) <-> (𝕸' |= ϕ).

Notation "m ≡ m'" := (equivalent m m') (at level 0).

(* Semantic Definitions *)
Section Bisimulation.

Context {W W' : Set}.

Definition state_model_relation : Type :=
  state_model W -> state_model W' -> Prop.

Context (Z : state_model_relation).

Definition atomic_harmony : Prop :=
  forall p p', Z p p' -> forall pr: prop,
      p.(st_val) p.(st_point) pr <-> p'.(st_val) p'.(st_point) pr.

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
  f_zig (F d) /\ f_zag (F d).

End Bisimulation.

Definition bisimilar (𝕸 𝕸': pointed_model) : Prop :=
  exists Z, bisimulation Z /\ Z 𝕸 𝕸'.

Notation "𝔐 ⇆ 𝔐'" := (bisimilar 𝔐 𝔐') (at level 30).


Arguments state_model_relation : clear implicits.

Section Getters.

Context {W W' : Set}.
Context {Z: state_model_relation W W'}.
Context (bis: bisimulation Z).

Definition get_HA : atomic_harmony Z.
  move: bis =>[HA _].
  exact: HA.
Defined.

Definition get_Zig : f_zig Z (F d).
  move: bis =>[_ [H _]].
  exact: H.
Defined.

Definition get_Zag : f_zag Z (F d).
  move: bis =>[_ [_ H]].
  exact: H.
Defined.

End Getters.

(* Main Theorem *)
Theorem InvarianceUnderBisimulation :
  forall 𝕸 𝕸' : pointed_model,
  𝕸 ⇆ 𝕸' -> 𝕸 ≡ 𝕸'.

Proof.
  move=> 𝕸 𝕸' bis ϕ.
  move: 𝕸 𝕸' bis.
  elim: ϕ => [prop | | ϕ IHϕ ψ IHψ | ϕ IH] /=
            𝕸 𝕸'.
  + move=> [Z [bis HZ]].
    rewrite !to_st_val !to_st_point ((get_HA bis) ?? HZ).
    tauto.
  + tauto.
  + move=>bis.
    split; move=> HIf Hsat.
    - eapply (IHψ 𝕸); first eassumption.
      apply HIf.
      by eapply (IHϕ 𝕸); eassumption.

    - eapply (IHψ 𝕸); first eassumption.
      apply HIf.
      by eapply (IHϕ 𝕸).
 
  + move=> [Z [bis HZ]]. 
    split.
 
    - move=> [q [HfWpp' Hsatq]].
      apply (get_Zig bis _ _ _ HZ) in HfWpp'
          as [q' [HfW'q'p' HZqq']].
      eexists.
      split; first eassumption.
      eapply (IH (to_pm q)); last by eassumption.
      exists Z.
      by rewrite !to_st_to_pm.
      
    - move=> [q' [HfWpp' Hsatq']].
      eapply (get_Zag bis _ _ _ HZ) in HfWpp'
          as [q [HfWpq HZqq']].
      eexists.
      split; first eassumption.
      eapply (IH (to_pm q)); last by eassumption.
      exists Z.
      by rewrite !to_st_to_pm.
Qed.

Section Satisfability.

Variable 𝕸 : model.
Variable 𝔖 : set (state_model 𝕸.(m_states)).
Variable Σ : set form.
Variable ϕ : form.

Definition sat :=
  exists st : state_model 𝕸.(m_states),
    st ∈ 𝔖 /\ (forall ϕ : form, ϕ ∈ Σ ->
    st |= ϕ).

Definition f_sat := forall Δ: finset Σ,
  exists st : state_model 𝕸, st ∈ 𝔖 /\
  Forall (fun ϕ : form=> st |= ϕ) Δ.

End Satisfability.

Arguments sat {_}.
Arguments f_sat {_}.

Section Saturation.

Variable 𝕸 : model.
Definition fw := F d 𝕸.

Definition image_iden : set (state_model 𝕸) :=
  fun (st : state_model 𝕸) =>
  (st_rel st = m_rel 𝕸 /\ st_val st = m_val 𝕸).

Definition image_fw : set (state_model 𝕸) := 
  fun (st : state_model 𝕸) =>
    (exists st': state_model 𝕸, st ∈ fw st').

Definition image := image_iden ∪ image_fw.

Definition saturation :=
  forall (Σ : set form),
  forall st : state_model 𝕸, st ∈ image ->
    (let 𝔖 := fw st in
     f_sat 𝔖 Σ -> sat 𝔖 Σ).

End Saturation.

Section HennesyMilner.

Variable 𝕸 : pointed_model.
Variable 𝕸' : pointed_model.

Hypothesis M_sat : saturation 𝕸.
Hypothesis M'_sat : saturation 𝕸'.

Let f__W := F d 𝕸.
Let f__W' := F d 𝕸'.

Definition equiv_in_image st st' :=
    st ∈ image 𝕸 /\
    st' ∈ image 𝕸' /\
    st ≡ st'.

Notation "a ↭ b" := (equiv_in_image a b) (at level 40).

Definition big_and Δ := fold_right And Top Δ.

Notation "'⋀' Δ" := (big_and Δ) (at level 0).

Lemma sat_fold_forall m Δ: 
  Forall (fun ϕ : form => m |= ϕ) Δ <-> m |= ⋀Δ.
Proof.
  elim: Δ; first by simpl; tauto.
  move=>ϕ Δ /= ->.
  tauto.
Qed.


Lemma equiv_in_image_bisimulation : bisimulation equiv_in_image.
Proof.
  split_ands.
  - move=> s s' s_s' p.
    case: s_s' =>[s_img [s'_img seqs']].
    split; intro H.
    + have sat : s |= p by assumption.
      by move/seqs': sat.
    + have sat : s' |= p by assumption.
      by move/seqs': sat.
  - move=>[s S X] [t T Y] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] tTYinsSX.
    set Σ : set form := (fun ϕ=> ⟨ t , T , Y ⟩ |= ϕ).
    have sat_big_and0 :
      forall Δ : finset Σ, ⟨t, T, Y⟩ |= ⋀Δ.
    + case.
      move=> l. simpl.
      elim: l=>[ |ϕ Δ IH] H.
      * by [].
      * simpl. simpl in H. case: H=>Hϕ HΔ.
        move/IH: HΔ {IH}=>IH.
        by apply.
    have sat_big_and :
      forall Δ : finset Σ, ⟨s, S, X⟩ |= DynDiam ⋀Δ.
    + move=>Δ.
      eexists.
      split; first by eassumption.
      by apply sat_big_and0.

    have sat_big_and' :
      forall Δ : finset Σ, ⟨s', S', X'⟩ |= DynDiam ⋀Δ
        by move=>Δ; apply/SeqS'.

    have sat_big_and'' :
      forall Δ : finset Σ, exists st', st' ∈ f__W' ⟨s', S', X'⟩ /\ st' |= ⋀Δ.
    + move=>Δ.
      move: (sat_big_and' Δ).
      simpl. move=>[st' [IH1 IH2]].
      exists st'.
      split; by assumption.

    pose 𝔖' : set (state_model _) :=
      fun st' => st' ∈ f__W' ⟨ s', S', X' ⟩ /\
              exists Δ : finset Σ, st' |= ⋀Δ.

    have f_sat' : f_sat 𝔖' Σ.
    + unfold f_sat.
      move=>Δ.
      move: (sat_big_and'' Δ)=>[st' [infw' satΔ]].
      exists st'.
      split.
      * unfold 𝔖'.
        split; first by [].
        by exists Δ.
      * apply sat_fold_forall.
        by apply satΔ.

    have f_sat'' : f_sat (f__W' ⟨ s', S', X' ⟩) Σ.
    + unfold f_sat.
      move=>Δ.
      move: (f_sat' Δ)=>[st' [ [H1 H2] H3]].
      exists st'.
      split; by [].

    unfold saturation in M'_sat.
    have sat' : sat (f__W' ⟨ s', S', X' ⟩) Σ
      by apply: M'_sat.
    case: sat'=>st' [inS H].
    exists st'.
    split.
    + by [].
    + unfold equiv_in_image.
      have tTY_img : ⟨ t, T, Y ⟩ ∈ image 𝕸.
      * apply: Union_intror.
        eexists.
        eassumption.

      have st_img : st' ∈ image 𝕸'.
      * apply: Union_intror.
        eexists.
        eassumption.

      split_ands.
      * by [].
      * by [].
      * unfold equivalent.
        move=>ϕ.
        split.
        -- move=>Ht.
           apply: H.
           by apply: Ht.
             
        -- move=>Ht.
           case: (sat_classic  ⟨ t, T, Y ⟩ ϕ); first by [].
           fold (Σ (~' ϕ)).
           move/H => /= notϕ. apply notϕ in Ht.
           contradiction.

  - unfold f_zag. move=>[s S X] [t' T' Y'] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] t'T'Y'insSX.
    set Σ : set form := (fun ϕ=> ⟨ t' , T' , Y' ⟩ |= ϕ).
    have sat_big_and0 :
      forall Δ : finset Σ, ⟨t', T', Y'⟩ |= ⋀Δ.
    + case.
      move=> l. simpl.
      elim: l=>[ |ϕ Δ IH] H.
      * by [].
      * simpl. simpl in H. case: H=>Hϕ HΔ.
        move/IH: HΔ {IH}=>IH.
        by apply.
    have sat_big_and' :
      forall Δ : finset Σ, ⟨s', S', X'⟩ |= DynDiam ⋀Δ.
    + move=>Δ.
      eexists.
      split; first by eassumption.
      by apply sat_big_and0.

    have sat_big_and :
      forall Δ : finset Σ, ⟨s, S, X⟩ |= DynDiam ⋀Δ
        by move=>Δ; apply/SeqS'.

    have sat_big_and'' :
      forall Δ : finset Σ, exists st, st ∈ f__W ⟨s, S, X⟩ /\ st |= ⋀Δ.
    + move=>Δ.
      move: (sat_big_and Δ).
      simpl. move=>[st [IH1 IH2]].
      exists st.
      split; by assumption.

    pose 𝔖 : set (state_model _) :=
      fun st => st ∈ f__W ⟨ s, S, X ⟩ /\
              exists Δ : finset Σ, st |= ⋀Δ.

    have f_sat𝔖 : f_sat 𝔖 Σ.
    + unfold f_sat.
      move=>Δ.
      move: (sat_big_and'' Δ)=>[st [infw satΔ]].
      exists st.
      split.
      * unfold 𝔖.
        split; first by [].
        by exists Δ.
      * apply sat_fold_forall.
        by apply satΔ.

    have f_sat_fw : f_sat (f__W ⟨ s, S, X ⟩) Σ.
    + unfold f_sat.
      move=>Δ.
      move: (f_sat𝔖 Δ)=>[st [ [H1 H2] H3]].
      exists st.
      split; by [].

    unfold saturation in M_sat.
    have sat_fw : sat (f__W ⟨ s, S, X ⟩) Σ
      by apply: M_sat.
    case: sat_fw=>st [inS H].
    exists st.
    split.
    + by [].
    + unfold equiv_in_image.
      have tTY_img : ⟨ t', T', Y' ⟩ ∈ image 𝕸'.
      * apply: Union_intror.
        eexists.
        eassumption.

      have st_img : st ∈ image 𝕸.
      * apply: Union_intror.
        eexists.
        eassumption.

      do 2! (split; first by []).
      unfold equivalent.
      move=>ϕ.
      split.
      * move=>Ht.
        case: (sat_classic ⟨ t', T', Y' ⟩ ϕ); first by [].
        fold (Σ (~' ϕ)).
        move/H => /= notϕ. apply notϕ in Ht.
        contradiction.

      * move=>Ht.
        apply: H.
        by apply: Ht.
Qed.     

Theorem HennesyMilner : 𝕸 ≡ 𝕸' -> 𝕸 ⇆ 𝕸'.
Proof.
  move=> Heq.
  unfold bisimilar.
  exists equiv_in_image.
  split; first by apply equiv_in_image_bisimulation.
  split_ands.
  - apply: Union_introl.
    rewrite /Ensembles.In /image_iden; tauto.
  - apply: Union_introl.
    rewrite /Ensembles.In /image_iden; tauto.
  - move: 𝕸 𝕸' Heq => [ [W R V] /= w] [ [W' R' V'] /= w'].
    by apply.
Qed.

End HennesyMilner.

End InvarianceTheorem.


(* Local Variables: *)
(* company-coq-local-symbols: ( ) *)
(* End: *)
