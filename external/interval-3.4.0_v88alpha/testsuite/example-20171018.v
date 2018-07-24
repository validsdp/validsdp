Require Import Reals.
Require Import Interval.Interval_tactic.
Require Import Interval.Interval_definitions.

Open Scope R_scope.

Lemma h_54_ln_2  h :
  -53 <= h <= 0 ->
  -  Rnearbyint rnd_DN (h * ln 2 / ln 5) * ln 5 <= 54 * ln 2.
Proof.
intros.
interval.
Qed.
