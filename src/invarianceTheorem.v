From Mtac2 Require Import Mtac2.
From Coq.Sets Require Import Constructive_sets.
From Coq.Relations Require Import Relations.
From Coq.Lists Require Import List.
From RCLIC Require Import utilities.
From mathcomp Require Import ssrnat ssrbool eqtype.

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

Module Type DYN.
Variable Dyn : Set.
Variable F : Dyn -> muf.
End DYN.

Module DynLogic (D: DYN).

(* Syntax *)

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | DynDiam : D.Dyn -> form -> form.

Coercion Atom : prop >-> form.

(* Basic notation *)
Notation "⊥'" := Bottom.

Notation "p ->' q" := (If p q)
                     (at level 90, right associativity).

Notation "⃟ d φ" := (DynDiam d φ)
                     (at level 65, d at level 9, right associativity).

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
  | ⃟ d φ =>
    let fw := D.F d 𝔐.(m_states) in
    exists p', p' ∈ fw 𝔐  /\  p' |= φ
  end
where "p |= φ" := (satisfies p φ).

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


Theorem InvarianceUnderBisimulation :
  forall 𝔐 𝔐' : pointed_model,
  𝔐 ⇆ 𝔐' -> 𝔐 ≡ 𝔐'.

Proof.
  move=> 𝔐 𝔐' bis φ.
  move: 𝔐 𝔐' bis.
  elim: φ => [prop | | φ IHφ ψ IHψ | d φ IH] /=
             𝔐 𝔐'.
  + move=> [Z [bis HZ]].
    rewrite !to_st_val !to_st_point.
    by apply ((get_AH bis) ?? HZ).

  + by [].

  + move=>bis.
    split; move=> HIf Hsat;
      apply (IHψ ?? bis);
      apply HIf;
      by apply (IHφ ?? bis).

  + move=> [Z [bis HZ]].
    split.

    - move=> [q [HqinfW Hsatq]].
      apply ((get_Zig bis) ?? HZ) in HqinfW
        as [q' [Hq'infW' HZqq']].
      exists q'.
      split; first by [].
      apply (IH q) ; last by [].
      exists Z.
      by rewrite !to_st_to_pm.

    - move=> [q' [Hq'infW' Hsatq']].
      apply ((get_Zag bis) ?? HZ) in Hq'infW'
          as [q [HqinfW HZqq']].
      exists q.
      split; first by [].
      eapply (IH q); last by eassumption.
      exists Z.
      by rewrite !to_st_to_pm.
Qed.

Section Satisfability.

Variable 𝔐 : model.
Variable 𝔖 : set (state_model 𝔐.(m_states)).
Variable Σ : set form.
Variable φ : form.

Definition satisfiable :=
  exists st : state_model 𝔐.(m_states),
    st ∈ 𝔖 /\ (forall φ : form, φ ∈ Σ -> st |= φ).

Definition finitely_satisfiable := forall Δ: finset Σ,
  exists st : state_model 𝔐, st ∈ 𝔖 /\
  Forall (fun φ : form=> st |= φ) Δ.

End Satisfability.

Arguments satisfiable {_}.
Arguments finitely_satisfiable {_}.

Section Saturation.

Variable 𝔐 : model.

Definition image_iden : set (state_model 𝔐) :=
  fun st => st_rel st = m_rel 𝔐 /\ st_val st = m_val 𝔐.

Definition image_fw_d d : set (state_model 𝔐) :=
  fun st => exists st': state_model 𝔐, st ∈ D.F d 𝔐 st'.

Definition image_fw : set (state_model 𝔐) :=
  fun st => exists f, st ∈ image_fw_d f.

Definition image := image_iden ∪ image_fw.

Definition f_saturated f :=
  forall (Σ: set form) (st: state_model 𝔐),
    st ∈ image -> let 𝔖 := D.F f 𝔐 st in
    finitely_satisfiable 𝔖 Σ -> satisfiable 𝔖 Σ.

Definition saturated := forall f, f_saturated f.

End Saturation.

Section HennessyMilner.

Variable 𝔐 : pointed_model.
Variable 𝔐' : pointed_model.

Hypothesis M_sat : saturated 𝔐.
Hypothesis M'_sat : saturated 𝔐'.

Definition equiv_in_image st st' :=
    st ∈ image 𝔐 /\
    st' ∈ image 𝔐' /\
    st ≡ st'.

Notation "a ↭ b" := (equiv_in_image a b) (at level 40).

Definition big_and Δ := fold_right And Top Δ.

Notation "'⋀' Δ" := (big_and Δ) (at level 0).

Lemma sat_fold_forall m Δ:
  Forall (fun φ : form => m |= φ) Δ <-> m |= ⋀Δ.
Proof.
  elim: Δ; first by simpl; tauto.
  move=>φ Δ /= ->.
  tauto.
Qed.


Lemma equiv_in_image_bisimulation : bisimulation equiv_in_image.
Proof.
  unfold equiv_in_image.
  split_ands.
  - move=> s s' s_s' p.
    case: s_s' =>[s_img [s'_img seqs']].
    split; move=> ?.
    + have sat : s |= p by assumption.
      by move/seqs': sat.
    + have sat : s' |= p by assumption.
      by move/seqs': sat.

  - move=>f [s S X] [t T Y] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] tTYinsSX.
    set Σ : set form := (fun φ=> ⟨ t , T , Y ⟩ |= φ).

    have sat_big_and :
      forall Δ : finset Σ, ⟨t, T, Y⟩ |= ⋀Δ.
    + case.
      elim=>/= [ |φ Δ IH]; first by [].
      case=>Hφ. move/IH=> HΔ.
      by apply.

    have sat_diamond_big_and :
      forall Δ : finset Σ, ⟨s, S, X⟩ |= ⃟f ⋀Δ.
    + move=>Δ.
      exists ⟨t, T, Y⟩.
      split; first by [].
      by apply: sat_big_and.

    have sat_diamond_big_and' :
      forall Δ : finset Σ, ⟨s', S', X'⟩ |= ⃟f ⋀Δ
        by move=>Δ; apply/SeqS'.

    have sat_next_big_and' :
      forall Δ : finset Σ, exists st', st' ∈ D.F f 𝔐' ⟨s', S', X'⟩ /\ st' |= ⋀Δ.
    + move=>Δ.
      move: (sat_diamond_big_and' Δ) => [st' [IH1 IH2]].
      by exists st'.

    pose 𝔖' : set (state_model _) :=
      fun st' => st' ∈ D.F f 𝔐' ⟨ s', S', X' ⟩ /\
              exists Δ : finset Σ, st' |= ⋀Δ.

    have 𝔖'_fsat : finitely_satisfiable 𝔖' Σ.
    + move=>Δ.
      move: (sat_next_big_and' Δ)=>[st' [infw' satΔ]].
      exists st'.
      split_ands.
      * by [].
      * by exists Δ.
      * by apply sat_fold_forall.

    pose 𝔖'' := D.F f 𝔐' ⟨ s', S', X' ⟩.
    have fw'_fsat : finitely_satisfiable 𝔖'' Σ.
    + move=>Δ.
      move: (𝔖'_fsat Δ)=>[st' [ [ ? ?] ?]].
      by exists st'.

    have fw'_sat : satisfiable 𝔖'' Σ
      by apply: M'_sat.

    case: fw'_sat=>st' [inS H].
    exists st'.
    split; first by [].
    have tTY_img : ⟨ t, T, Y ⟩ ∈ image 𝔐.
    + apply: Union_intror. exists f.
      by exists ⟨ s, S, X ⟩.

    have st'_img : st' ∈ image 𝔐'.
    + apply: Union_intror. exists f.
      by exists ⟨ s', S', X' ⟩.

    split_ands; try by [].
    move=>φ.
    split.
    + move=>Ht.
      apply: H.
      by apply: Ht.

    + case: (sat_classic  ⟨ t, T, Y ⟩ φ); first by [].
      fold (Σ (~' φ)).
      move/H => sat_notφ sat_φ.
      apply sat_notφ in sat_φ.
      contradiction.

  - move=>d [s S X] [t' T' Y'] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] t'T'Y'insSX.
    set Σ : set form := (fun φ=> ⟨ t' , T' , Y' ⟩ |= φ).

    have sat_big_and' :
      forall Δ : finset Σ, ⟨t', T', Y'⟩ |= ⋀Δ.
    + case.
      elim=> /= [ |φ Δ IH]; first by [].
      case=>Hφ. move/IH=> HΔ.
      by apply.

    have sat_diamond_big_and' :
      forall Δ : finset Σ, ⟨s', S', X'⟩ |= ⃟ d ⋀Δ.
    + move=>Δ.
      exists ⟨t', T', Y'⟩.
      split; first by [].
      by apply: sat_big_and'.

    have sat_diamond_big_and :
      forall Δ : finset Σ, ⟨s, S, X⟩ |= ⃟ d ⋀Δ
        by move=>Δ; apply/SeqS'.

    have sat_next_big_and :
      forall Δ : finset Σ, exists st, st ∈ D.F d 𝔐 ⟨s, S, X⟩ /\ st |= ⋀Δ.
    + move=>Δ.
      move: (sat_diamond_big_and Δ)=> /= [st [IH1 IH2]].
      by exists st.

    pose 𝔖 : set (state_model _) :=
      fun st => st ∈ D.F d 𝔐 ⟨ s, S, X ⟩ /\
              exists Δ : finset Σ, st |= ⋀Δ.

    have 𝔖_fsat : finitely_satisfiable 𝔖 Σ.
    + move=>Δ.
      move: (sat_next_big_and Δ)=>[st [infw satΔ]].
      exists st.
      split_ands.
      * by [].
      * by exists Δ.
      * by apply sat_fold_forall.

    have fw_fsat : finitely_satisfiable (D.F d 𝔐 ⟨ s, S, X ⟩) Σ.
    + move=>Δ.
      move: (𝔖_fsat Δ)=>[st [ [ ? ?] ?]].
      by exists st.

    have fw_sat : satisfiable (D.F d 𝔐 ⟨ s, S, X ⟩) Σ
      by apply: M_sat.

    case: fw_sat=>st [inS H].
    exists st.
    split; first by [].
    have t'T'Y'_img : ⟨ t', T', Y' ⟩ ∈ image 𝔐'.
    + apply: Union_intror. exists d.
      by exists ⟨ s', S', X' ⟩.

    have st_img : st ∈ image 𝔐.
    + apply: Union_intror. exists d.
      by exists ⟨ s, S, X ⟩.

    split_ands; try by [].
    move=>φ.
    split.
    + case: (sat_classic ⟨ t', T', Y' ⟩ φ); first by [].
      fold (Σ (~' φ)).
      move/H => sat_notφ sat_φ.
      apply sat_notφ in sat_φ.
      contradiction.

    + move=>Ht.
      apply: H.
      by apply: Ht.
Qed.

Corollary HennesyMilner : 𝔐 ≡ 𝔐' -> 𝔐 ⇆ 𝔐'.
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
  - move: 𝔐 𝔐' Heq => [ [W R V] /= w] [ [W' R' V'] /= w'].
    by apply.
Qed.

End HennessyMilner.

End DynLogic.

Module Examples.

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

Definition F (d: Dyn) : muf :=
  match d with
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

End Examples.

(* Local Variables: *)
(* company-coq-local-symbols: ( ) *)
(* End: *)
