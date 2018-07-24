Require Import Reals Interval_tactic.

Goal forall x : R,
  (Rabs (x - x) <= 1/5)%R.
Proof.
intros x.
interval with (i_bisect_diff x).
Qed.
