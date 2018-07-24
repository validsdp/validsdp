Require Import Reals.
Require Import Interval_tactic.

Goal
  forall x, (-1/2 <= x <= 0)%R ->
  True.
Proof.
intros x Hx.
interval_intro (Rabs x + x)%R upper with (i_bisect_diff x, i_depth 5).
exact I.
Qed.
