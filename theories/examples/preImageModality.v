Require Import 
  logic
  (* basic modal logic *)
  bml.

(* TODO: fix the name: is it pre-image? *)

(* Definition of a BML + pre-image modality as an instance of our generic notion
   of modal dynamic logic.
*)

(* Diamond form of the pre-image modality, and diamond of the basic modal 
   language, as dynamic operators.  *)
Module PreImageDyn <: DYN.
  (* TODO: we need to redefine BML's diamond each time that we want to extend
     BML with some new dynamic operator *)
  Module BmlDynLogic := DynLogic BmlDyn.
  Import BmlDynLogic.
  Import BmlDyn.

  Inductive PreImageDynOp := Rpre | Diamond.

  Definition Dyn := PreImageDynOp.

  Definition F (f: Dyn) : muf :=
    match f with
    | Diamond => diamond
    | Rpre => fun W '⟨w, R, V⟩ '⟨v, R', V'⟩ =>
               (* We do not force some constraint over v. We just
                  need v : W, which is enforced by type-checking. *)
               R = R' /\ V = V' /\ R v w
    end.

End PreImageDyn.

(* We instantiate a new dynamic logic with Rpre and Diamond as its dynamic 
   operators *)
Module PreImageExample.
  Module PreImageDynLogic := DynLogic PreImageDyn.
  Import PreImageDynLogic.
  Import PreImageDyn.

  Notation "⃟ φ" := (DynDiam Diamond φ)
                     (at level 65, right associativity).

  Notation "'⟨R⟩⁻¹' φ" := (DynDiam Rpre φ)
                            (at level 65, right associativity).

  (* TODO: a simple, generic way of defining a finite set of worlds? *)
  Inductive W := One | Two.
  Definition r1 := (fun v w : W => ((v = One) /\ (w = Two)) \/
                                  (v = Two) /\ (w = Two)).
  Definition r2 := (fun v w : W => v = Two /\ w = Two).

  Definition M1 := ⟪ W, r1, ∅ ⟫, One.
  Definition M2 := ⟪ W, r2, ∅ ⟫, Two.
  
  (* M1 and M2 can be distinguished by a BML + <R⁻¹> formula. *)
  Example not_pred_M1 : ~ (M1 |= ⟨R⟩⁻¹ ⊤').
  Proof.
    unfold M1.
    intro Hsat.
    simpl in Hsat.
    inversion Hsat as [p' [Hdyn Hsat']].
    clear Hsat.
    unfold Ensembles.In in Hdyn.
    destruct p'.
    inversion Hdyn as [_ [_ Hrel]].
    inversion Hrel as [Heq | Heq];
      inversion Heq;
      discriminate.
  Qed.

  Example pred_M2 : M2 |= ⟨R⟩⁻¹ ⊤'.
  Proof.
    unfold M2.
    simpl.
    exists M2.
    unfold Ensembles.In.
    simpl.
    unfold r2.
    split;
      repeat (split + reflexivity).
    auto.
  Qed.
  
  (* The following code allows us to assume just for a moment that 
     Dyn := BmlDynOp, in order to prove the statement M1 ⇆ M2 under the 
     assumption that the set of dynamic operators are just those mentioned 
     in BmlDynOp.
   *)
  Module BmlDynLogic := DynLogic BmlDyn.
  Import BmlDynLogic.
  Import BmlDyn.
  Definition Dyn := BmlDynOp.

  (* M1 and M2 are bisimilar under basic modal logic's notion of bisimulation *)
  Example bisimilar_models : M1 ⇆ M2.
  Proof.
    (* TODO: maybe some tactic to avoid unfolding defs.? *)
    exists
      (fun v w => ((v = ⟨ One, r1 , ∅ ⟩) /\ (w = ⟨ Two, r2 , ∅ ⟩)) 
               \/
               ((v = ⟨ Two, r1, ∅ ⟩) /\ (w = ⟨ Two, r2, ∅ ⟩))).
    split.
    - (* bisimulation  *)
      unfold bisimulation.
      split.
      + (* atomic harmony *)
        unfold atomic_harmony.
        simpl.
        intros p p' Heq pr.
        destruct p as [point1 r1' val1].
        destruct p' as [point2 r2' val2].
        simpl.

        assert(val1 = ∅ /\ val2 = ∅)
          as [Hval1 Hval2].
        {inversion Heq as [Heq_1 | Heq_2];
            (inversion Heq_1 as [Hm1 Hm2] + 
             inversion Heq_2 as [Hm1 Hm2]);
            inversion Hm1;
            inversion Hm2;
            split;
            reflexivity.
        }
        subst.
        split;
          intro H;
          inversion H.
      + (* zig and zag *)
        split.
        * (* zig *)
          intro d.
          destruct d.
          unfold f_zig.
          intros p q p' Hbisim Hdyn.
          inversion Hbisim as [Hpair1 | Hpair2].
          -- (* p = ⟨ One, r1, ∅ ⟩ /\ p' = ⟨ Two, r2, ∅ ⟩ *)
             simpl.
             unfold diamond.
             exists ⟨ Two, r2, ∅ ⟩.
             unfold Ensembles.In.
             destruct p'.
             split.
             ++ (* q' ∈ F Diamond ⟪ W, r2, ∅ ⟫, (Two) p' *)
                inversion Hpair1 as [Heq_p Heq_mod].
                inversion Heq_mod.
                unfold r2.
                split;
                  repeat (split + reflexivity).
             ++ (* Z q q' *)
                inversion Hpair1 as [Heq_p Heq_p'].
                simpl in Hdyn.
                unfold diamond in Hdyn.
                unfold Ensembles.In in Hdyn.
                rewrite Heq_p in Hdyn.
                destruct q.
                inversion Hdyn as [Hr1 [Heq_r1 Hval]].
                right.
                assert(Heq_st_point0: st_point0 = Two).
                {destruct st_point0.
                 - (* One *)
                   unfold r1 in Hr1.
                   inversion Hr1 as [Heq | Heq];
                     inversion Heq;
                     discriminate.
                 - (* Two *)
                   reflexivity.
                }
                rewrite Heq_st_point0.
                split;
                  repeat (subst + split + reflexivity).
          -- (* p = ⟨ Two, r1, ∅ ⟩ /\ p' = ⟨ Two, r2, ∅ ⟩ *)
             simpl.
             unfold diamond.
             exists ⟨ Two, r2, ∅ ⟩.
             unfold Ensembles.In.
             destruct p'.
             split.
             ++ (* q' ∈ F Diamond ⟪ W, r2, ∅ ⟫, (Two) p' *)
               inversion Hpair2 as [Heq_p Heq_mod].
               inversion Heq_mod.
               unfold r2.
               split;
                 repeat (split + reflexivity).
             ++ (* Z q q' *)
               inversion Hpair2 as [Heq_p Heq_p'].
               simpl in Hdyn.
               unfold diamond in Hdyn.
               unfold Ensembles.In in Hdyn.
               rewrite Heq_p in Hdyn.
               destruct q.
               inversion Hdyn as [Hr1 [Heq_r1 Hval]].
               right.
               assert(Heq_st_point0: st_point0 = Two).
               {destruct st_point0.
                - (* One *)
                  unfold r1 in Hr1.
                  inversion Hr1 as [Heq | Heq];
                    inversion Heq;
                    discriminate.
                - (* Two *)
                  reflexivity.
               }
               rewrite Heq_st_point0.
               split;
                 repeat (subst + split + reflexivity).
        * (* zag *)
          intro d.
          destruct d.
          unfold f_zag.
          intros p q' p' Hbisim Hdyn.
          inversion Hbisim as [Hpair1 | Hpair2].
          -- (* p = ⟨ One, r1, ∅ ⟩ /\ p' = ⟨ Two, r2, ∅ ⟩ *)
             simpl.
             unfold diamond.
             exists ⟨ Two, r1, ∅ ⟩.
             unfold Ensembles.In.
             destruct p.
             split.
             ++ (* q ∈ F Diamond ⟪ W, r1, ∅ ⟫, (One) p' *)
                inversion Hpair1 as [Heq_p Heq_mod].
                inversion Heq_p.
                unfold r1.
                split;
                  repeat (left + split + reflexivity).
             ++ (* Z q q' *)
                inversion Hpair1 as [Heq_p Heq_p'].
                simpl in Hdyn.
                unfold diamond in Hdyn.
                unfold Ensembles.In in Hdyn.
                rewrite Heq_p' in Hdyn.
                destruct q'.
                inversion Hdyn as [Hr2 [Heq_r2 Hval]].
                right.
                assert(Heq_st_point0: st_point0 = Two).
                {destruct st_point0.
                 - (* One *)
                   unfold r2 in Hr2.
                   inversion Hr2 as [_ Heq_One].
                   inversion Heq_One.
                 - (* Two *)
                   reflexivity.
                }
                rewrite Heq_st_point0.
                split;
                  repeat (subst + split + reflexivity).
          -- (* p = ⟨ Two, r1, ∅ ⟩ /\ p' = ⟨ Two, r2, ∅ ⟩ *)
             simpl.
             unfold diamond.
             exists ⟨ Two, r1, ∅ ⟩.
             unfold Ensembles.In.
             destruct p.
             split.
             ++ (* q ∈ F Diamond ⟪ W, r1, ∅ ⟫, (One) p *)
                inversion Hpair2 as [Heq_p Heq_mod].
                inversion Heq_p.
                unfold r1.
                split;
                  repeat (right + split + reflexivity).
            ++ (* Z q q' *)
               inversion Hpair2 as [Heq_p Heq_p'].
               simpl in Hdyn.
               unfold diamond in Hdyn.
               unfold Ensembles.In in Hdyn.
               rewrite Heq_p' in Hdyn.
               destruct q'.
               inversion Hdyn as [Hr2 [Heq_r2 Hval]].
               right.
               assert(Heq_st_point0: st_point0 = Two).
               {destruct st_point0.
                - (* One *)
                  unfold r2 in Hr2.
                  inversion Hr2 as [_ Heq].
                  inversion Heq.
                - (* Two *)
                  reflexivity.
               }
               rewrite Heq_st_point0.
               split;
                 repeat (subst + split + reflexivity).
    - (* bisimulation contains the pair of interest *)
      left.
      unfold M1.
      unfold M2.
      unfold r1.
      unfold r2.
      split;
        reflexivity.
  Qed.
      
End PreImageExample.
