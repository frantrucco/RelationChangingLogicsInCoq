Require Import 
  (* classic logic axioms *)
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

  Inductive W := One | Two.
  (* the following code allows us to assume just for a moment that Dyn := BmlDynOp, in order to prove the 
   statement:
   
    ⟪ W, (fun v w => (v = One) /\ (w = Two)), ∅ ⟫, One ⇆ 
    ⟪ W, (fun v w => (v = Two) /\ (w = Two)), ∅ ⟫, Two.
    under the assumption that the set of dynamic operators are just those mentioned in BmlDynOp.        
   *)
  Module BmlDynLogic := DynLogic BmlDyn.
  Import BmlDynLogic.
  Import BmlDyn.
  Definition Dyn := BmlDynOp.
        
  Example bisimilar_models : 
    ⟪ W, (fun v w => (v = One) /\ (w = Two)), ∅ ⟫, One ⇆ 
    ⟪ W, (fun v w => (v = Two) /\ (w = Two)), ∅ ⟫, Two.
  Proof.
    (* TODO: maybe some tactic to avoid unfolding defs.? *)
    unfold bisimilar.
    unfold state_model_relation.

    remember (fun v w : W => v = One /\ w = Two) as r1.
    remember (fun v w : W => v = Two /\ w = Two) as r2.

    exists (fun v w => ((v = ⟨ One, r1 , ∅ ⟩) /\ (w = ⟨ Two, r2 , ∅ ⟩)) 
               \/
               ((v = ⟨ Two, r1, ∅ ⟩) /\ (w = ⟨ Two, r2, ∅ ⟩))).

    split.
    - (* bisimulation  *)
      split.
      + (* atomic harmony *)
        unfold atomic_harmony.
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
                rewrite Heqr2.
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
                   rewrite Heqr1 in Hr1.
                   inversion Hr1 as [Heq_One Heq_Two].
                   inversion Heq_Two.
                 - (* Two *)
                   reflexivity.
                }
                rewrite Heq_st_point0.
                split;
                  repeat (subst + split + reflexivity).
          -- (* p = ⟨ One, r1, ∅ ⟩ /\ p' = ⟨ Two, r2, ∅ ⟩ *)
             simpl.
             unfold diamond.
             exists ⟨ Two, r2, ∅ ⟩.
             unfold Ensembles.In.
             destruct p'.
             split.
             ++ (* q' ∈ F Diamond ⟪ W, r2, ∅ ⟫, (Two) p' *)
               inversion Hpair2 as [Heq_p Heq_mod].
               inversion Heq_mod.
               rewrite Heqr2.
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
                  rewrite Heqr1 in Hr1.
                  inversion Hr1 as [Heq_One Heq_Two].
                  inversion Heq_Two.
                - (* Two *)
                  reflexivity.
               }
               rewrite Heq_st_point0.
               split;
                 repeat (subst + split + reflexivity).
               
               
                

          
          
      
End UniExample.
