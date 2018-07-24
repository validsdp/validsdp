Require Import Reals.
Require Import Interval.Interval_tactic.

Open Scope R_scope.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 3/2.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval_intro (sqrt (1 - x)) upper as H'.
  apply Rle_trans with (1 := H').
  interval.
Qed.

Goal
  forall x, 3/2 <= x <= 2 ->
  forall y, 1 <= y <= 33/32 ->
  Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768.
Proof.
  intros.
  interval with (i_prec 19, i_bisect x).
Qed.

Goal
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
Proof.
  intros.
  interval with (i_bisect_taylor x 3).
Qed.

Goal
  forall x, -1 <= x ->
  x < 1 + powerRZ x 3.
Proof.
  intros.
  interval with (i_bisect_diff x).
Qed.

Require Import Coquelicot.Coquelicot.

Goal
  Rabs (RInt (fun x => atan (sqrt (x*x + 2)) / (sqrt (x*x + 2) * (x*x + 1))) 0 1
        - 5/96*PI*PI) <= 1/1000.
Proof.
  interval with (i_integral_prec 9, i_integral_depth 1, i_integral_deg 5).
Qed.

Goal
  RInt_gen (fun x => 1 * (powerRZ x 3 * ln x^2))
           (at_right 0) (at_point 1) = 1/32.
Proof.
  refine ((fun H => Rle_antisym _ _ (proj2 H) (proj1 H)) _).
  interval.
Qed.

Goal
  Rabs (RInt_gen (fun t => 1/sqrt t * exp (-(1*t)))
                 (at_point 1) (Rbar_locally p_infty)
        - 2788/10000) <= 1/1000.
Proof.
  interval.
Qed.
