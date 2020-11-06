Require Import logic.

Module HennessyMilner (D: DYN).

Module DynLogic := DynLogic D.
Import DynLogic.


Section Satisfability.

Context (𝔐 : model).
Context (𝔖 : set (state_model 𝔐)).
Context (Σ : set form).
Context (φ : form).

Definition satisfiable :=
  exists st : state_model 𝔐,
    st ∈ 𝔖 /\ (forall φ : form, φ ∈ Σ -> st |= φ).

Definition finitely_satisfiable := forall Δ: finset Σ,
  exists st : state_model 𝔐, st ∈ 𝔖 /\
  Forall (fun φ : form=> st |= φ) Δ.

End Satisfability.

Arguments satisfiable {_}.
Arguments finitely_satisfiable {_}.

Section Saturation.

Context (𝔐 : model).

Definition image_iden : set (state_model 𝔐) :=
  fun st => st_rel st = m_rel 𝔐 /\ st_val st = m_val 𝔐.

Definition image_fw f : set (state_model 𝔐) :=
  fun st => exists st': state_model 𝔐, st ∈ D.F f 𝔐 st'.

Definition image_Ufw : set (state_model 𝔐) :=
  fun st => exists f, st ∈ image_fw f.

Definition image := image_iden ∪ image_Ufw.

Definition f_saturated f :=
  forall (Σ: set form) (st: state_model 𝔐),
    st ∈ image -> let 𝔖 := D.F f 𝔐 st in
    finitely_satisfiable 𝔖 Σ -> satisfiable 𝔖 Σ.

Definition saturated := forall f, f_saturated f.

End Saturation.

Section HennessyMilner.

Context (𝔐 : pointed_model).
Context (𝔐' : pointed_model).

Hypothesis M_sat : saturated 𝔐.
Hypothesis M'_sat : saturated 𝔐'.

Definition equiv_in_image st st' :=
    st ∈ image 𝔐 /\
    st' ∈ image 𝔐' /\
    st ≡ st'.

Notation "a ↭ b" := (equiv_in_image a b) (at level 40).

Lemma equiv_in_image_bisimulation : bisimulation equiv_in_image.
Proof.
  split_ands.
  - move=> [s S X] [s' S' X'] equiv_ss' p.
    case: equiv_ss' => [s_img [s'_img seqs']].
    split; move=> /= ps_in_X.
    + have sat : ⟨s, S, X⟩ |= p by assumption.
      by move/seqs': sat.
    + have sat : ⟨s', S', X'⟩ |= p by assumption.
      by move/seqs': sat.

  - move=>f [s S X] [t T Y] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] tTYinsSX.
    pose Σ : set form := (fun φ=> ⟨ t , T , Y ⟩ |= φ).

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
    have 𝔖''_fsat : finitely_satisfiable 𝔖'' Σ.
    + move=>Δ.
      move: (𝔖'_fsat Δ)=>[st' [ [ ? ?] ?]].
      by exists st'.

    have 𝔖''_sat : satisfiable 𝔖'' Σ
      by apply: M'_sat.

    case: 𝔖''_sat=>[ [t' T' Y'] [inS H] ].
    exists ⟨ t', T', Y' ⟩.
    split; first by [].
    have tTY_img : ⟨ t, T, Y ⟩ ∈ image 𝔐.
    + apply: Union_intror. exists f.
      by exists ⟨ s, S, X ⟩.

    have t'T'Y'_img : ⟨ t', T', Y' ⟩ ∈ image 𝔐'.
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
      move/H. apply2. simpl.
      contradiction.

  - move=>f [s S X] [t' T' Y'] [s' S' X'] /=.
    move=>[imgS [imgS' SeqS']] t'T'Y'insSX.
    pose Σ : set form := (fun φ=> ⟨ t' , T' , Y' ⟩ |= φ).

    have sat_big_and' :
      forall Δ : finset Σ, ⟨t', T', Y'⟩ |= ⋀Δ.
    + case.
      elim=> /= [ |φ Δ IH]; first by [].
      case=>Hφ. move/IH=> HΔ.
      by apply.

    have sat_diamond_big_and' :
      forall Δ : finset Σ, ⟨s', S', X'⟩ |= ⃟f ⋀Δ.
    + move=>Δ.
      exists ⟨t', T', Y'⟩.
      split; first by [].
      by apply: sat_big_and'.

    have sat_diamond_big_and :
      forall Δ : finset Σ, ⟨s, S, X⟩ |= ⃟f ⋀Δ
        by move=>Δ; apply/SeqS'.

    have sat_next_big_and :
      forall Δ : finset Σ, exists st, st ∈ D.F f 𝔐 ⟨s, S, X⟩ /\ st |= ⋀Δ.
    + move=>Δ.
      move: (sat_diamond_big_and Δ)=> /= [st [IH1 IH2]].
      by exists st.

    pose 𝔖 : set (state_model _) :=
      fun st => st ∈ D.F f 𝔐 ⟨ s, S, X ⟩ /\
              exists Δ : finset Σ, st |= ⋀Δ.

    have 𝔖_fsat : finitely_satisfiable 𝔖 Σ.
    + move=>Δ.
      move: (sat_next_big_and Δ)=>[st [infw satΔ]].
      exists st.
      split_ands.
      * by [].
      * by exists Δ.
      * by apply sat_fold_forall.

    have fw_fsat : finitely_satisfiable (D.F f 𝔐 ⟨ s, S, X ⟩) Σ.
    + move=>Δ.
      move: (𝔖_fsat Δ)=>[st [ [ ? ?] ?]].
      by exists st.

    have fw_sat : satisfiable (D.F f 𝔐 ⟨ s, S, X ⟩) Σ
      by apply: M_sat.

    case: fw_sat=>st [inS H].
    exists st.
    split; first by [].
    have t'T'Y'_img : ⟨ t', T', Y' ⟩ ∈ image 𝔐'.
    + apply: Union_intror. exists f.
      by exists ⟨ s', S', X' ⟩.

    have st_img : st ∈ image 𝔐.
    + apply: Union_intror. exists f.
      by exists ⟨ s, S, X ⟩.

    split_ands; try by [].
    move=>φ.
    split.
    + case: (sat_classic  ⟨ t', T', Y' ⟩ φ); first by [].
      fold (Σ (~' φ)).
      move/H. apply2. simpl.
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

End HennessyMilner.
