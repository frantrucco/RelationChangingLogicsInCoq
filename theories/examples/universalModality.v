Require Import 
  (* classic logic axioms *)
  logic.

(* Definition of a BML + universal modality as an instance of our generic notion
   of modal dynamic logic.
*)

(* Diamond form of the universal modality, and diamond of the basic modal 
   language, as dynamic operators.  *)
Module UniDyn <: DYN.
  (* TODO: we need to redefine BML's diamond each time that we want to extend
     BML with some new dynamic operator *)
  Definition diamond : muf :=
    fun W '⟨w, R, V⟩ '⟨v, R', V'⟩=>
      R w v /\ R = R' /\ V = V'.

  Inductive UniDynOp := E | Diamond.

  Definition Dyn := UniDynOp.

  Definition F (f: Dyn) : muf :=
    match f with
    | Diamond => diamond
    | E => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩ =>
            (* We do not force some constraint over v. We just
               need v : W, which is enforced by type-checking. *)
            R = R' /\ V = V'
    end.

End UniDyn.

(* We instantiate a new dynamic logic with E and Diamond as its dynamic 
   operators *)
Module UniExample.
  Module UniDynLogic := DynLogic UniDyn.
  Import UniDynLogic.
  Import UniDyn.
  
  Notation "⃟ φ" := (DynDiam Diamond φ)
                     (at level 65, right associativity).

  Notation "'E' φ" := (DynDiam E φ)
                        (at level 65, right associativity).

  (* We can force the existence of infinite chains in the accessibility
     relation, using E.  *)
  Example decreasing_chains : 
    forall W R (p : prop),
      (* TODO: abstract frame validity into a definition *)
        (forall V w,
          ⟪ W , R , V ⟫, w |= (p ->' E ⃟ p)) <-> forall x, exists y, R y x.
  Proof.
    intros W R p.
    split.
    - (* frame validity implies infinite chains *)
      intro Hframe_v.
      intro v.
      (* valuation / v \in V (p) *)
      specialize (Hframe_v ⦃ (p, v) ⦄ v).
      simpl in Hframe_v.
      
      assert(Hv_in_Val: (p, v) ∈ ⦃ (p, v) ⦄).
      {apply (In_singleton _ (p, v)).
      }
      
      specialize (Hframe_v Hv_in_Val).
      inversion Hframe_v as [WRV [WRV_in [WR'V' [WR'V'_in Hp_holds]]]].
      clear Hframe_v.

      destruct WRV as [w R' V].
      destruct WR'V' as [w' R'' V'].

      unfold Ensembles.In in WRV_in.
      inversion WRV_in as [Heq_R Heq_V].
      clear WRV_in.
      
      unfold Ensembles.In in WR'V'_in.
      inversion WR'V'_in as [Hrel [Heq_R' Heq_V']].
      clear WR'V'_in.

      unfold Ensembles.In in Hp_holds.
      
      simpl in Hp_holds.
      simpl in Hrel.
      simpl in Heq_R'.
      simpl in Heq_V'.
      rewrite <- Heq_V' in Hp_holds.
      
      assert(Heq_w'_v : w' = v).
      {assert(Hin: Ensembles.In (Singleton (p, v)) (p, w')).
       {rewrite Heq_V.
        exact Hp_holds.
       }
       inversion Hin.
       reflexivity.
      }

      rewrite <- Heq_w'_v.
      rewrite Heq_R.
      eauto.
    - (* infinite chains implies frame validity *)
      intro Hinf_chain.
      intros V w.
      simpl.
      intro Hin_V.
      specialize (Hinf_chain w).
      inversion Hinf_chain as [w' Hrel].
      clear Hinf_chain.
      (* E ⃟ p *)
      exists ⟨w', R, V⟩.
      split.
      + (* ⟨R, V⟩ = ⟨R, V⟩ *)
        unfold Ensembles.In.
        split;
          reflexivity.
      + (* ⃟ p *)
        simpl.
        exists ⟨w, R, V⟩.
        split.
        * (* R w' w /\ ⟨R, V⟩ = ⟨R, V⟩ *)
          unfold Ensembles.In.
          split.
          -- (* R w' w *)
             simpl.
             exact Hrel.
          -- (* ⟨R, V⟩ = ⟨R, V⟩ *)
             split;
               reflexivity.
        * (* (p 1, w) ∈ V *)
          exact Hin_V.
  Qed.

End UniExample.
