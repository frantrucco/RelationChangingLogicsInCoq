Require Import logic.

Module Invariance (D: DYN).

Module DynLogic := DynLogic D.
Import DynLogic.

Theorem InvarianceUnderBisimulation :
  forall 𝔐 𝔐' : pointed_model,
  𝔐 ⇆ 𝔐' -> 𝔐 ≡ 𝔐'.

Proof.
  move=> 𝔐 𝔐' bis φ.
  move: 𝔐 𝔐' bis.
  elim: φ => [prop | | φ IHφ ψ IHψ | f φ IH] /=
             𝔐 𝔐'.
  + move=> [Z [bis HZ]].
    rewrite !to_st_val !to_st_point.
    by apply ((get_AH bis) ?? HZ).

  + by [].

  + move=>bis.
    split; move=> HImpl Hsat;
      apply (IHψ ?? bis);
      apply HImpl;
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

End Invariance.
