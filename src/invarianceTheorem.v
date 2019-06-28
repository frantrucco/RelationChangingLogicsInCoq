Section invarianceTheorem.

Variable Dyn : Set.

Inductive prop: Set :=
p : nat -> prop.

Inductive form : Type :=
| Atom    : prop -> form
| Bottom  : form
| If      : form -> form -> form
| Diam    : form -> form
| DynDiam : Dyn -> form -> form.

Definition muf : Type := forall (W : Set),
  let R := (W -> W -> Prop) in (W * R) -> ((W * R) -> Prop).

Variable F : Dyn -> muf.

Fixpoint satisfies
         (W : Set)
         (R : W -> W -> Prop)
         (V : W -> prop -> Prop)
         (w : W)
         (phi : form) : Prop :=
match phi with
| Atom v => (V w v)
| Bottom => False
| If phi1 phi2 => (satisfies W R V w phi1) -> (satisfies W R V w phi2)
| Diam phi =>
    exists v : W, R w v /\ (satisfies W R V v phi)
| DynDiam d phi =>
  let fw := F d W in
  exists (v : W) (R' : W -> W -> Prop), fw (w, R) (v, R') /\
                             satisfies W R' V v phi
end.

Notation "# W , R , V >> w |= phi" := (satisfies W R V w phi)
                                      (at level 30).

Definition model_to_model_relation W W' : Type :=
  W -> (W -> W -> Prop) -> W' -> (W' -> W' -> Prop) -> Prop.

Definition equivalent_at_points W R V W' R' V' w w' :=
  forall (phi:form), (# W , R , V >> w |= phi) <->
                (# W' , R' , V' >> w' |= phi).

Definition atomic_harmony
           (W : Set) (V : W -> prop -> Prop)
           (W' : Set) (V' : W' -> prop -> Prop)
           (Z : model_to_model_relation W W') : Prop :=
  forall w S w' S',
  Z w S w' S' -> V w = V' w'.

Definition zig
           (W : Set)
           (W' : Set)
           (Z : model_to_model_relation W W') : Prop :=
  forall w S w' S' v, Z w S w' S' ->
    S w v -> (exists v' : W', Z v S v' S' /\ S' w' v').

Definition zag
           (W : Set)
           (W' : Set)
           (Z : model_to_model_relation W W') : Prop :=
  forall w S w' S' v', Z w S w' S' ->
    S' w' v' -> (exists v : W, Z v S v' S' /\ S w v).

Definition f_zig
           (W : Set)
           (W' : Set)
           (Z : model_to_model_relation W W')
           (f : muf) : Prop :=
  let (fw, fw') := (f W, f W') in
  forall w S w' S' v T, Z w S w' S' ->
    fw (w, S) (v, T) -> (exists (v' : W') T', fw' (w', S') (v', T') /\ Z v T v' T').

Definition f_zag
           (W : Set)
           (W' : Set)
           (Z : model_to_model_relation W W')
           (f : muf) : Prop :=
  let (fw, fw') := (f W, f W') in
  forall w S w' S' v' T', Z w S w' S' ->
    fw' (w', S') (v', T') -> (exists (v : W) T, fw (w, S) (v, T) /\ Z v T v' T').

Definition bisimulation W V W' V' Z :=
  (atomic_harmony W V W' V' Z) /\ (zig W W' Z) /\ (zag W W' Z) /\
  (forall d : Dyn, (f_zig W W' Z (F d))) /\
  forall d : Dyn, (f_zag W W' Z (F d)).

Definition bisimulation_at_points W R V W' R' V' Z w w' :=
  bisimulation W V W' V' Z /\ Z w R w' R'.

Definition bisimulable W V W' V' :=
  exists Z, bisimulation W V W' V' Z.

Definition bisimulable_at_points W R V W' R' V' w w':=
  exists Z, bisimulation W V W' V' Z /\ Z w R w' R'.

Theorem InvarianceUnderBisimulation :
  forall W R V W' R' V' w w',
    bisimulable_at_points W R V W' R' V' w w' ->
    equivalent_at_points W R V W' R' V' w w'.
Proof.
  intros W R V W' R' V' w w'.

  unfold bisimulable_at_points.
  unfold equivalent_at_points.
  unfold bisimulation.

  intros [Z [[HAtomicHarmony [HZig [HZag [HFZig HFZag]]]] HZwSw'S']].
  intros phi.

  generalize dependent Z.
  generalize dependent R'.
  generalize dependent R.
  generalize dependent w'.
  generalize dependent w.

  induction phi as [p | | phi IHphi psi IHpsi | phi IH | d phi IH];
    unfold satisfies; fold satisfies; 
    intros w w' S S' Z HAtomicHarmony HZig HZag HFZig HFZag HZwSw'S'.

  + (* Atom *)
    rewrite (HAtomicHarmony w S w' S' HZwSw'S').
    tauto.

  + (* Bottom *)
    tauto.

  + (* If *)
    split;
      intros H Hsat;
      apply (IHpsi w w' S S' Z
                   HAtomicHarmony HZig HZag HFZig HFZag HZwSw'S');
      apply H;
      apply (IHphi w w' S S' Z
                   HAtomicHarmony HZig HZag HFZig HFZag HZwSw'S');
      apply Hsat.

  + (* Modal *)
    split.
    - intro H.
      destruct H as [v [HSwv Hsatv]].
      unfold zig in HZig.
      apply (HZig w S w' S' v HZwSw'S') in HSwv as [v' [HZvv' HS'w'v']].
      exists v'.
      split.
      * assumption.
      * apply (IH v v' S S' Z
                  HAtomicHarmony HZig HZag HFZig HFZag HZvv').
        assumption.
    - intro H.
      unfold zag in HZag.
      destruct H as [v' H].
      destruct H as [HSw'v' Hsatv'].
      apply (HZag w S w' S' v' HZwSw'S') in HSw'v' as Hexists.
      destruct Hexists as [v Hexists].
      destruct Hexists as [HZvv' HSwv].
      exists v.
      split.
      * assumption.
      * apply (IH v v' S S' Z
                  HAtomicHarmony HZig HZag HFZig HFZag HZvv').
        assumption.

  + (* Dynamic *)
    split.
    - intro H.
      destruct H as [v [T [HfWwSvT HsatTv]]].

      apply (HFZig d w S w' S' v T HZwSw'S') in HfWwSvT
        as [v' [T' [HfW'w'S'v'T' HZvTv'T']]].

      exists v'. exists T'.

      split.
        * assumption.
        * apply (IH v v' T T' Z HAtomicHarmony HZig
                    HZag HFZig HFZag HZvTv'T').
          assumption.


    - intro H.
      destruct H as [v' [T' [HfW'w'S'v'T' HsatT'v']]].

      apply (HFZag d w S w' S' v' T' HZwSw'S') in HfW'w'S'v'T'
        as [v [T [HfWwSvT HZvTv'T']]].

      exists v. exists T.

      split.
        * assumption.
        * apply (IH v v' T T' Z HAtomicHarmony HZig
                    HZag HFZig HFZag HZvTv'T').
          assumption.
Qed.
End invarianceTheorem.
