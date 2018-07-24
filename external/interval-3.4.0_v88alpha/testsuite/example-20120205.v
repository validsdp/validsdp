Require Import Reals.
Require Import Interval_tactic.

Goal forall x, (1 <= x)%R -> (0 < x)%R.
intros.
interval.
Qed.

Goal forall x, (1 <= x)%R -> (x <= x * x)%R.
intros.
interval with (i_bisect_diff x).
Qed.

Goal forall x, (2 <= x)%R -> (x < x * x)%R.
intros.
interval with (i_bisect_diff x).
Qed.

Goal forall x, (-1 <= x)%R -> (x < 1 + powerRZ x 3)%R.
intros.
interval with (i_bisect_diff x).
Qed.
