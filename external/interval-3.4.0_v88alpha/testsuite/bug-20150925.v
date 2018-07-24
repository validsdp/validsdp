Require Import Reals Interval_tactic.

Goal forall x, (-1 / 3 <= x - x <= 1 / 7)%R.
Proof.
intros x.
interval with (i_bisect_diff x).
Qed.
