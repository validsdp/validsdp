From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 : R) :=
  -x0 + 2/1 * x1 - x2 - 417817267/500000000 * x1 * (1 + x1).

Let b1 (x0 x1 x2 : R) :=
  (x0 + 5/1) * (5/1 - x0).

Let b2 (x0 x1 x2 : R) :=
  (x1 + 5/1) * (5/1 - x1).

Let b3 (x0 x1 x2 : R) :=
  (x2 + 5/1) * (5/1 - x2).

Let lb := -36713/1000.

Let ub := 10439/1000.

Let lb_sigma (x0 x1 x2 : R) :=
  1078193359413343/34359738368.

Let lb_sigma1 (x0 x1 x2 : R) :=
  431340833813429/137438953472.

Let lb_sigma2 (x0 x1 x2 : R) :=
  4106105866600931/137438953472.

Let lb_sigma3 (x0 x1 x2 : R) :=
  431340833813401/137438953472.

Let ub_sigma (x0 x1 x2 : R) :=
  7940631182374179/8589934592.

Let ub_sigma1 (x0 x1 x2 : R) :=
  200278046848393/2147483648.

Let ub_sigma2 (x0 x1 x2 : R) :=
  2680190779007/4294967296.

Let ub_sigma3 (x0 x1 x2 : R) :=
  200278046848393/2147483648.

Lemma lb_pos (x0 x1 x2 : R) :
  lb_sigma x0 x1 x2 * (p x0 x1 x2 - lb)
  - lb_sigma1 x0 x1 x2 * b1 x0 x1 x2
  - lb_sigma2 x0 x1 x2 * b2 x0 x1 x2
  - lb_sigma3 x0 x1 x2 * b3 x0 x1 x2 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3.
validsdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 : R) : lb_sigma x0 x1 x2 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 : R) : lb_sigma1 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma1. interval. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 : R) : lb_sigma2 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma2. interval. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 : R) : lb_sigma3 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma3. interval. Qed.

Lemma ub_pos (x0 x1 x2 : R) :
  ub_sigma x0 x1 x2 * (ub - p x0 x1 x2)
  - ub_sigma1 x0 x1 x2 * b1 x0 x1 x2
  - ub_sigma2 x0 x1 x2 * b2 x0 x1 x2
  - ub_sigma3 x0 x1 x2 * b3 x0 x1 x2 >= 0.
Proof.
rewrite /p /ub /ub_sigma /ub_sigma1 /b1 /ub_sigma2 /b2 /ub_sigma3 /b3.
validsdp.
Qed.

Lemma ub_sigma_pos (x0 x1 x2 : R) : ub_sigma x0 x1 x2 > 0.
Proof. rewrite /ub_sigma. interval. Qed.

Lemma ub_sigma1_pos (x0 x1 x2 : R) : ub_sigma1 x0 x1 x2 >= 0.
Proof. rewrite /ub_sigma1. interval. Qed.

Lemma ub_sigma2_pos (x0 x1 x2 : R) : ub_sigma2 x0 x1 x2 >= 0.
Proof. rewrite /ub_sigma2. interval. Qed.

Lemma ub_sigma3_pos (x0 x1 x2 : R) : ub_sigma3 x0 x1 x2 >= 0.
Proof. rewrite /ub_sigma3. interval. Qed.

Lemma var_bounds (x l u : R) : l <= x <= u -> (x - l) * (u - x) >= 0.
Proof.
move=> [Hl Hu].
apply Rle_ge.
by apply Interval_missing.Rmult_le_pos_pos; apply Fcore_Raux.Rle_0_minus.
Qed.

Lemma relax (x y z : R) : x >= 0 -> y >= 0 -> z - x * y >= 0 -> z >= 0.
Proof.
move=> HX Hy.
apply Rge_trans, Rle_ge.
rewrite -{2}(Rminus_0_r z).
apply Rplus_le_compat_l, Ropp_le_contravar.
by apply Interval_missing.Rmult_le_pos_pos; apply Rge_le.
Qed.
  
Theorem p_ge_lb (x0 x1 x2 : R) :
  -5 <= x0 <= 5 -> -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> lb <= p x0 x1 x2.
Proof.
move=> H0 H1 H2.
have Hb0 : b1 x0 x1 x2 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb1 : b2 x0 x1 x2 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (lb_sigma x0 x1 x2)); [by apply lb_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (lb_sigma1_pos x0 x1 x2) Hb0).
apply (relax _ _ _ (lb_sigma2_pos x0 x1 x2) Hb1).
apply (relax _ _ _ (lb_sigma3_pos x0 x1 x2) Hb2).
apply lb_pos.
Qed.

Theorem p_le_ub (x0 x1 x2 : R) :
  -5 <= x0 <= 5 -> -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> p x0 x1 x2 <= ub.
Proof.
move=> H0 H1 H2.
have Hb0 : b1 x0 x1 x2 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb1 : b2 x0 x1 x2 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (ub_sigma x0 x1 x2)); [by apply ub_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (ub_sigma1_pos x0 x1 x2) Hb0).
apply (relax _ _ _ (ub_sigma2_pos x0 x1 x2) Hb1).
apply (relax _ _ _ (ub_sigma3_pos x0 x1 x2) Hb2).
apply ub_pos.
Qed.
