Require Import Reals.
Require Import Interval_tactic.

Goal True.
interval_intro PI lower.
interval_intro (PI/2)%R upper.
exact I.
Qed.
