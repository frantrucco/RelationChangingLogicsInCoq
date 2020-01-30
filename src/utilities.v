From Mtac2 Require Import Mtac2.
From Coq.Sets Require Import Constructive_sets.
From Coq.Lists Require Import List.

Module Sets.

Notation "'set' S" := (Ensemble S) (at level 0) : type_scope.

Arguments Union {_}.
Notation "a ∪ b" := (Union a b) (at level 85).

Arguments Ensembles.In {_}.
Notation "a ∈ b" := (Ensembles.In b a) (at level 60).

Definition Forall {S} (s: S -> Prop) l := fold_right (fun a b=>s a /\ b) True l.
Definition finset {S} (s: set S) : Type := {l : list S | Forall s l}.

Definition empty_finset {S} {s: set S} : finset s := exist _ nil I.
Definition singleton_finset {S} {s: set S} x (p : s x) : finset s :=
  exist _ (x::nil) (conj p I).

Definition list_of {S} {s: set S} (l: finset s) : list S := proj1_sig l.

Coercion list_of : finset >-> list.

End Sets.

Module Tactics.

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

End Tactics.
