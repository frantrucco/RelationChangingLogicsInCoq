From Mtac2 Require Import Mtac2.
From Coq.Sets Require Import Constructive_sets.
From Coq.Relations Require Import Relations.
From Coq.Lists Require Import List.

Require Import ssreflect.

Module Utilities. (* move to file! *)

Obligation Tactic := idtac.
Import M.notations.

(* [a ?? b] will fill with enough _ until [a _ ... _ b] is typed *)
Polymorphic Definition fill {A B} (a : A) (b: B) {C} : M C :=
  (mfix1 f (d: dyn) : M C :=
    mmatch d with
    | [? V t] @Dyn (forall x:B, V x) t =u> [eqd]
        eqC <- M.unify_or_fail UniCoq C (V b);
        match eqC in (_ =m= y0) return (M y0 -> M C) with
        | meq_refl => fun HC0 : M C => HC0
        end (M.ret (t b))
    | [? U V t] @Dyn (forall x:U, V x) t =>
      e <- M.evar U;
      f (Dyn (t e))
    | _ => M.raise WrongTerm
    end) (Dyn a).

Notation "a ?? b" := (ltac:(mrun (fill a b))) (at level 0).

End Utilities.

Module Sets.

Notation "'set' S" := (Ensemble S) (at level 0) : type_scope.

Arguments Union {_}.
Notation "a ∪ b" := (Union a b) (at level 85).

Arguments Ensembles.In {_}.
Notation "a ∈ b" := (Ensembles.In b a) (at level 60).

Definition Forall {S} (s: S -> Prop) l := fold_left (fun b a=>s a /\ b) l True.
Definition finset {S} (s: set S) : Type := {l : list S | Forall s l}.

Definition list_of {S} {s: set S} (l: finset s) : list S := proj1_sig l.

Coercion list_of : finset >-> list.

End Sets.

Import Utilities.
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

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | DynDiam : Dyn -> form -> form.

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

Definition muf : Type := forall (W : Set),
  state_model W -> set (state_model W).

Variable F : Dyn -> muf.

Fixpoint satisfies (pm: pointed_model) (phi : form) : Prop :=
  match phi with
  | Atom a => pm.(m_val) pm.(pm_point) a
  | Bottom => False
  | If phi1 phi2 => (satisfies pm phi1) -> (satisfies pm phi2)
  | DynDiam d phi =>
    let fw := F d pm in
    exists p', fw pm p' /\ satisfies p' phi
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
  forall p p', Z p p' -> forall pr: prop, p.(st_val) p.(st_point) pr <-> p'.(st_val) p'.(st_point) pr.

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

Definition get_Zig {W W'} {Z: state_model_relation W W'} (bis: bisimulation Z) : (forall d : Dyn, (f_zig ?? Z (F d))).
  move: bis =>[_ [H _]].
  exact: H.
Defined.

Definition get_Zag {W W'} {Z: state_model_relation W W'} (bis: bisimulation Z) : (forall d : Dyn, (f_zag ?? Z (F d))).
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
  induction ϕ as [prop | | ϕ IHϕ ψ IHψ | d ϕ IH]; simpl;
  intros _M _M' [Z [bis HZ]].
  + rewrite !to_st_val !to_st_point ((get_HA bis) ?? HZ).
    tauto.
  + tauto.
  + split;
    intros HIf Hsat.
    eapply (IHψ _M).
    unfold bisimilar. eexists. split; eassumption.
    apply HIf.
    eapply (IHϕ _M).
    unfold bisimilar. eexists. split; eassumption.
    eassumption.

    eapply (IHψ _M).
    unfold bisimilar. eexists. split; eassumption.
    apply HIf.
    eapply (IHϕ _M).
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
Variable _S : set (state_model _M).
Variable Σ : set form.
Variable ϕ : form.

Definition sat :=
  exists st : state_model _M, _S st -> forall ϕ : form, Σ ϕ ->
  st |= ϕ.

Definition f_sat := forall l: finset Σ,
  exists st : state_model _M, _S st -> Forall (fun ϕ : form=> st |= ϕ) l.

End Satisfability.

Arguments sat {_}.
Arguments f_sat {_}.

Section Saturation.

Variable _M : model.
Variable d : Dyn.
Definition fw := F d _M.

Definition image_iden : set (state_model _M) :=
  fun (st : state_model _M) =>
  (st_rel st = m_rel _M /\ st_val st = m_val _M).

Definition image_fw : set (state_model _M) := 
  fun (st : state_model _M) =>
    (exists st': state_model _M, fw st' st).

Definition image := image_iden ∪ image_fw.

Definition successors (w : _M) : state_model _M -> state_model _M -> Prop :=
  fun '{| st_point := _; st_rel := S1; st_val := X1 |}
    '{| st_point := t; st_rel := S2; st_val := X2 |} =>
  S1 = S2 /\ X1 = X2 /\ S1 w t.

Definition saturation :=
  forall (Σ : set form),
  forall st : state_model _M, st ∈ image ->

    (* Saturation of every possible updated model *)
    (let _S := fw st in
     f_sat _S Σ -> sat _S Σ) /\

    (* Saturation of every successor *)
    (forall w : _M,
     let _S := successors w st in
     f_sat _S Σ -> sat _S Σ).

End Saturation.

Section HennesyMilner.

Variable _M : pointed_model.
Variable _M' : pointed_model.

Hypothesis M_sat : forall d, saturation _M d.
Hypothesis M'_sat : forall d, saturation _M' d.

Let f__W := fun d=> F d _M.
Let f__W' := fun d=> F d _M'.

Definition weneedaname d st st' :=
    st ∈ image _M d /\
    st' ∈ image _M' d /\
    st ≡ st'.

Notation "a ↭ b" := (weneedaname _ a b) (at level 40).

Lemma weneedaname_bisimulation : forall d, bisimulation (weneedaname d).
Proof.
  split; last split.
  - move=> s s' s_s' p.
    case: s_s' =>[s_img [s'_img seqs']].
    split; intro H.
    + have sat : s |= p by assumption.
      by move/seqs': sat.
    + have sat : s' |= p by assumption.
      by move/seqs': sat.
  - move=>d' [s S X] [t T Y] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] tTYinsSX.
    set Σ : set form := (fun ϕ=> ⟨ s , S , X ⟩ |= ϕ).
    evar (e: set (state_model _M)). 
    have finsat : f_sat e Σ. 
    + move=>[l].
      set big_and := fold_left And l Top.
      have sat_big_and : (⟨s, S, X⟩ |= DynDiam d' big_and).
      * unfold big_and; clear big_and.
simpl.
        elim: l.
        -- eexists; split; last by [].
           eassumption.
        -- move=>ϕ l [sm [Fsm satl]].
    
Theorem HennesyMilner : _M ≡ _M' -> bisimilar _M _M'.

End HennesyMilner.

(* Local Variables: *)
(* company-coq-local-symbols: ( ("_M" . ?ℳ) ("_M'" . (?ℳ (Br . Bl) ?')) ("_S" . ?𝒮) ) *)
(* End: *)
