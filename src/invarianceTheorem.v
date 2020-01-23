From Mtac2 Require Import Mtac2.
From Coq.Relations Require Import Relations.
From Coq.Lists Require Import List.

Obligation Tactic := idtac.
Import M.notations.
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


Section invarianceTheorem.

(* Syntax *)
Variable Dyn : Set.

Inductive prop : Set :=
  p : nat -> prop.

Inductive form : Set :=
  | Atom    : prop -> form
  | Bottom  : form
  | If      : form -> form -> form
  | DynDiam : Dyn -> form -> form.

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
Definition set (S: Type) := S -> Prop.

Definition val (W: Set) : Type := W -> prop -> Prop.

Structure state_model (W: Set) := {
  value: W; rel: relation W; valuation: val W
}.

Arguments value {W}.
Arguments rel {W}.
Arguments valuation {W}.

Definition muf : Type := forall (W : Set),
  state_model W -> set (state_model W).

Variable F : Dyn -> muf.

Fixpoint satisfies {W : Set} (p: state_model W) (phi : form) : Prop :=
  match phi with
  | Atom a => p.(valuation) p.(value) a
  | Bottom => False
  | If phi1 phi2 => (satisfies p phi1) -> (satisfies p phi2)
  | DynDiam d phi =>
    let fw := F d W in
    exists p', fw p p' /\ satisfies p' phi
  end.

Notation "p |= phi" := (satisfies p phi) (at level 30).

(* Semantic Definitions *)
Variables W W' : Set.

Definition equivalent_at_sm (p: state_model W) (p': state_model W') :=
  forall (ϕ: form), (p |= ϕ) <-> (p' |= ϕ).

Definition model_to_model_relation : Type :=
  state_model W -> state_model W' -> Prop.

Variable Z : model_to_model_relation.

Definition atomic_harmony : Prop :=
  forall p p', Z p p' -> p.(valuation) p.(value) = p'.(valuation) p'.(value).

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

Definition bis_at_sm (p: state_model W) (p': state_model W') : Prop :=
  bisimulation /\ Z p p'.

(* Theorem *)


Theorem InvarianceUnderBisimulation :
forall (p: state_model W) (p': state_model W'),
    bis_at_sm p p' -> equivalent_at_sm p p'.

Proof.
  intros p p'. (* name each component of the points *)
  unfold bis_at_sm.          (* unfold definitions *)
  unfold equivalent_at_sm.
  unfold bisimulation.

  intros [ [HAtomicHarmony [HFZig HFZag]] HZwSw'S'].
  intros ϕ.

  generalize dependent p'. generalize dependent p.

  induction ϕ as [prop | | ϕ IHϕ ψ IHψ | d ϕ IH];
  simpl.                (* This tactic unfolds definitions *)
  + intros p p' HZpp'. rewrite (HAtomicHarmony ?? HZpp'). tauto.
  + tauto.
  + intros p p'; split;
    intros HIf Hsat;
    apply (IHψ ?? HZwSw'S');
    apply HIf;
    apply (IHϕ ?? HZwSw'S');
    apply Hsat.
  + intros p p'. split; simpl.
    - intros [q [HfWpp' Hsatq]].
      apply (HFZig ?? HZwSw'S') in HfWpp'
          as [q' [HfW'q'p' HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply IH; eassumption.
    - intros [q' [HfWpp' Hsatq']].
      apply (HFZag ?? HZwSw'S') in HfWpp'
          as [q [HfWpq HZqq']].
      eexists.
      split.
      * eassumption.
      * eapply IH; eassumption.
Qed.

Structure Model := {
  wstates :> Set;
  wrel : relation wstates;
  wval: val wstates
}.


Section finset.
Definition finset {S} (s: set S) : Type := {l : list S | Forall s l}.

Definition list_of {S} {s: set S} (l: finset s) : list S := proj1_sig l.

End finset.


Coercion list_of : finset >-> list.

Section sat.

Variable _M : Model.
Variable _S : set (state_model _M).
Variable Σ : set form.
Variable ϕ : form.

Definition sat :=
  exists st : state_model _M, _S st -> forall ϕ : form, Σ ϕ ->
  st |= ϕ.

Definition f_sat := forall l: finset Σ,
  exists st : state_model _M, _S st -> Forall (fun ϕ : form=> st |= ϕ) l.

End sat.

Arguments sat {_}.
Arguments f_sat {_}.

Section saturation.

Variable _M : Model.
Variable d : Dyn.
Definition fw := F d _M.

Definition is_image_iden
           (st : state_model _M) :=
  (rel st = wrel _M /\ valuation st = wval _M).

Definition is_image_fw
           (fw : state_model _M -> set (state_model _M))
           (st : state_model _M) :=
  (exists st': state_model _M, fw st' st).

Definition is_image fw st :=
  is_image_iden st /\ is_image_fw fw st.

Print state_model.

Definition successors (w : _M) st :=
  fun st' =>

  let S := rel st in
  let X := valuation st in

  let t := value st' in
  let S' := rel st' in
  let X' := valuation st' in

  S = S' /\ X = X' /\ S w t.

Definition saturation :=
  forall (Σ : set form),
  forall (d : Dyn),
  let fw := F d _M in
  forall st : state_model _M, is_image fw st ->

    (* Saturation of every possible updated model *)
    (let _S := fw st in
     f_sat _S Σ -> sat _S Σ) /\

    (* Saturation of every successor *)
    (forall w : _M,
     let _S := successors w st in
     f_sat _S Σ -> sat _S Σ).

End saturation.


(* Local Variables: *)
(* company-coq-local-symbols: ( ("_M" . ?ℳ) ("_S" . ?𝒮) ) *)
(* End: *)
