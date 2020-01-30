From Mtac2 Require Import Mtac2.
From Coq.Sets Require Import Constructive_sets.
From Coq.Relations Require Import Relations.
From Coq.Lists Require Import List.
From RCLIC Require Import utilities.

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
  pm_point : pm_model
}.

Structure state_model (W: Set) := {
  st_point: W; st_rel: relation W; st_val: valuation W
}.

Notation "⟨ a , b , c ⟩" := {| st_point := a; st_val := c; st_rel := b |}.

Arguments st_point {W}.
Arguments st_rel {W}.
Arguments st_val {W}.

Definition to_pm {W} (sm: state_model W) :=
  {| pm_model := {| m_rel := sm.(st_rel); m_val := sm.(st_val) |};
     pm_point := sm.(st_point) |}.

Coercion to_pm: state_model >-> pointed_model.

Definition to_st (pm: pointed_model) :=
  {| st_rel := pm.(m_rel);
     st_val := pm.(m_val);
     st_point := pm.(pm_point) |}.

Coercion to_st: pointed_model >-> state_model.

Section InvarianceTheorem.

(* Syntax *)
Variable Dyn : Set.
Variable d : Dyn.

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | And     : form -> form -> form
  | DynDiam : form -> form.

Coercion Atom : prop >-> form.

(* Syntactic sugar *)
Definition Not (phi : form) : form :=
  If phi Bottom.

Definition Top : form :=
  Not Bottom.

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

Notation "<o> d phi" := (DynDiam d phi)

                        (at level 65, right associativity).

Notation "[o] d phi" := (DynBox d phi)
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
  | And phi1 phi2 => (satisfies pm phi1) /\ (satisfies pm phi2)
  | DynDiam phi =>
    let fw := F d pm.(m_states) in
    exists p', p' ∈ fw pm /\ satisfies p' phi
  end.

Notation "p |= phi" := (satisfies p phi) (at level 30).

Definition equivalent (_M _M': pointed_model) :=
  forall (ϕ: form), (_M |= ϕ) <-> (_M' |= ϕ).

Notation "m ≡ m'" := (equivalent m m') (at level 0).

(* Semantic Definitions *)
Section Bisimulation.

Variables W W' : Set.

Definition state_model_relation : Type :=
  state_model W -> state_model W' -> Prop.

Variable Z : state_model_relation.

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

Arguments bisimulation {_ _}.

Definition bisimilar (_M _M': pointed_model) : Prop :=
  exists Z, bisimulation Z /\ Z _M _M'.

(* Main Theorem *)

Lemma to_st_val (_M: pointed_model) : m_val _M = st_val _M.
  by [].
Qed.

Lemma to_st_point (_M: pointed_model) : pm_point _M = st_point _M.
  by [].
Qed.

Definition get_HA {W W'} {Z: state_model_relation W W'} (bis: bisimulation Z) : atomic_harmony _ _ Z.
  move: bis =>[HA _].
  exact: HA.
Defined.

Definition get_Zig {W W'} {Z: state_model_relation W W'} (bis: bisimulation Z) : f_zig ?? Z (F d).
  move: bis =>[_ [H _]].
  exact: H.
Defined.

Definition get_Zag {W W'} {Z: state_model_relation W W'} (bis: bisimulation Z) : f_zag ?? Z (F d).
  move: bis =>[_ [_ H]].
  exact: H.
Defined.

Lemma to_st_to_pm {W} (st: state_model W): to_st (to_pm st) = st.
  by case: st.
Defined.

Theorem InvarianceUnderBisimulation :
  forall _M _M' : pointed_model,
  bisimilar _M _M' -> _M ≡ _M'.

Proof.
  move=> _M _M' bis ϕ.
  move: _M _M' bis.
  induction ϕ as [prop | | ϕ IHϕ ψ IHψ | ϕ IHϕ ψ IHψ | ϕ IH]; simpl;
  intros _M _M' [Z [bis HZ]].
  + rewrite !to_st_val !to_st_point ((get_HA bis) ?? HZ).
    tauto.
  + tauto.
  + split; intros HIf Hsat.
    - eapply (IHψ _M).
      unfold bisimilar. eexists. split; eassumption.
      apply HIf.
      eapply (IHϕ _M).
      unfold bisimilar. eexists. split; eassumption.
      eassumption.

    - eapply (IHψ _M).
      unfold bisimilar. eexists. split; eassumption.
      apply HIf.
      eapply (IHϕ _M).
      unfold bisimilar. eexists. split; eassumption.
      eassumption.

  + split; move=> [HIf Hsat]; split.
    - eapply (IHϕ _M).
      unfold bisimilar. eexists. split; eassumption.
      by apply HIf.
    - eapply (IHψ _M).
      unfold bisimilar. eexists. split; eassumption.
      eassumption.
    - eapply (IHϕ _M).
      unfold bisimilar. eexists. split; eassumption.
      by apply HIf.
    - eapply (IHψ _M).
      unfold bisimilar. eexists. split; eassumption.
      eassumption.
    
  + split; simpl.
    - intros [q [HfWpp' Hsatq]].
      eapply (get_Zig bis) in HfWpp'
          as [q' [HfW'q'p' HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply (IH (to_pm q)); last by eassumption.
        unfold bisimilar.
        eexists.
        split; last first.
        ++ rewrite !to_st_to_pm.
           eassumption.
        ++ assumption.
      * assumption.
    - intros [q' [HfWpp' Hsatq']].
      eapply (get_Zag bis) in HfWpp'
          as [q [HfWpq HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply (IH (to_pm q)); last by eassumption.
        unfold bisimilar.
        eexists.
        split; last first.
        ++ rewrite !to_st_to_pm.
           eassumption.
        ++ assumption.
      * assumption.
Qed.

Section Satisfability.

Variable _M : model.
Variable _S : set (state_model _M.(m_states)).
Variable Σ : set form.
Variable ϕ : form.

Definition sat :=
  exists st : state_model _M.(m_states),
    st ∈ _S /\ (forall ϕ : form, ϕ ∈ Σ ->
    st |= ϕ).

Definition f_sat := forall Δ: finset Σ,
  exists st : state_model _M, st ∈ _S /\
  Forall (fun ϕ : form=> st |= ϕ) Δ.

End Satisfability.

Arguments sat {_}.
Arguments f_sat {_}.

Section Saturation.

Variable _M : model.
Definition fw := F d _M.

Definition image_iden : set (state_model _M) :=
  fun (st : state_model _M) =>
  (st_rel st = m_rel _M /\ st_val st = m_val _M).

Definition image_fw : set (state_model _M) := 
  fun (st : state_model _M) =>
    (exists st': state_model _M, st ∈ fw st').

Definition image := image_iden ∪ image_fw.

Definition saturation :=
  forall (Σ : set form),
  forall st : state_model _M, st ∈ image ->
    (let _S := fw st in
     f_sat _S Σ -> sat _S Σ).

End Saturation.

Section HennesyMilner.

Variable _M : pointed_model.
Variable _M' : pointed_model.

Hypothesis M_sat : saturation _M.
Hypothesis M'_sat : saturation _M'.

Let f__W := F d _M.
Let f__W' := F d _M'.

Definition weneedaname st st' :=
    st ∈ image _M /\
    st' ∈ image _M' /\
    st ≡ st'.

Notation "a ↭ b" := (weneedaname a b) (at level 40).

Definition big_and Δ := fold_right And Top Δ.

Notation "'⋀' Δ" := (big_and Δ) (at level 0).

Axiom classic : forall st ϕ, st |= ϕ \/ st |= ~' ϕ.

Lemma sat_fold_forall m Δ: 
  Forall (fun ϕ : form => m |= ϕ) Δ <-> m |= ⋀Δ.
Proof.
  elim: Δ; first by simpl; tauto.
  move=>ϕ Δ /= ->.
  tauto.
Qed.


Lemma weneedaname_bisimulation : bisimulation weneedaname.
Proof.
  split; last split.
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
        by move/IH: HΔ {IH}.
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

    pose _S' : set (state_model _) :=
      fun st' => st' ∈ f__W' ⟨ s', S', X' ⟩ /\
              exists Δ : finset Σ, st' |= ⋀Δ.

    have f_sat' : f_sat _S' Σ.
    + unfold f_sat.
      move=>Δ.
      move: (sat_big_and'' Δ)=>[st' [infw' satΔ]].
      exists st'.
      split.
      * unfold _S'.
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
    + unfold weneedaname.
      have tTY_img : ⟨ t, T, Y ⟩ ∈ image _M.
      * apply: Union_intror.
        eexists.
        eassumption.

      have st_img : st' ∈ image _M'.
      * apply: Union_intror.
        eexists.
        eassumption.

      split; last split. 
      * by [].
      * by [].
      * unfold equivalent.
        move=>ϕ.
        split.
        -- move=>Ht.
           apply: H.
           by apply: Ht.
             
        -- move=>Ht.
           case: (classic  ⟨ t, T, Y ⟩ ϕ); first by [].
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
        by move/IH: HΔ {IH}.
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

    pose _S : set (state_model _) :=
      fun st => st ∈ f__W ⟨ s, S, X ⟩ /\
              exists Δ : finset Σ, st |= ⋀Δ.

    have f_sat_S : f_sat _S Σ.
    + unfold f_sat.
      move=>Δ.
      move: (sat_big_and'' Δ)=>[st [infw satΔ]].
      exists st.
      split.
      * unfold _S.
        split; first by [].
        by exists Δ.
      * apply sat_fold_forall.
        by apply satΔ.

    have f_sat_fw : f_sat (f__W ⟨ s, S, X ⟩) Σ.
    + unfold f_sat.
      move=>Δ.
      move: (f_sat_S Δ)=>[st [ [H1 H2] H3]].
      exists st.
      split; by [].

    unfold saturation in M_sat.
    have sat_fw : sat (f__W ⟨ s, S, X ⟩) Σ
      by apply: M_sat.
    case: sat_fw=>st [inS H].
    exists st.
    split.
    + by [].
    + unfold weneedaname.
      have tTY_img : ⟨ t', T', Y' ⟩ ∈ image _M'.
      * apply: Union_intror.
        eexists.
        eassumption.

      have st_img : st ∈ image _M.
      * apply: Union_intror.
        eexists.
        eassumption.

      do 2! (split; first by []).
      unfold equivalent.
      move=>ϕ.
      split.
      * move=>Ht.
        case: (classic  ⟨ t', T', Y' ⟩ ϕ); first by [].
        fold (Σ (~' ϕ)).
        move/H => /= notϕ. apply notϕ in Ht.
        contradiction.

      * move=>Ht.
        apply: H.
        by apply: Ht.
Qed.     

Theorem HennesyMilner : _M ≡ _M' -> bisimilar _M _M'.
Proof.
  move=> Heq.
  unfold bisimilar.
  exists weneedaname.
  split; first by apply weneedaname_bisimulation.
  split; last split.
  - apply: Union_introl.
    rewrite /Ensembles.In /image_iden; tauto.
  - apply: Union_introl.
    rewrite /Ensembles.In /image_iden; tauto.
  - move: _M _M' Heq => [ [W R V] /= w] [ [W' R' V'] /= w'].
    by apply.
Qed.

End HennesyMilner.

End InvarianceTheorem.
(* Local Variables: *)
(* company-coq-local-symbols: ( ("_M" . ?ℳ) ("_M'" . (?ℳ (Br . Bl) ?')) ("_S" . ?𝒮) ("_S'" . (?𝒮 (Br . Bl) ?')) ) *)
(* End: *)
