Require Import Reals.
Require Import Interval_tactic.
Local Open Scope R_scope.

Goal forall x : R, exp x >= 0.
intros; interval.
Qed.
