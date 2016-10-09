From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x0)^2 + 2 * (x1)^2 + 2 * (x2)^2 + 2 * (x3)^2 + 2 * (x4)^2 + 2 * (x5)^2
  + 2 * (x6)^2 - x0.

Let b1 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x0 + 1) * (1 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x1 + 1) * (1 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x2 + 1) * (1 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x3 + 1) * (1 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x4 + 1) * (1 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x5 + 1) * (1 - x5).

Let b7 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x6 + 1) * (1 - x6).

Let lb := -2501/10000.

Let ub := 140001/10000.

Let lb_sigma (x0 x1 x2 x3 x4 x5 x6 : R) :=
  2211104745248113/68719476736.

Let lb_sigma1 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  36851219757/68719476736.

Let lb_sigma2 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  55277412661/137438953472.

Let lb_sigma3 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  3454838289/8589934592.

Let lb_sigma4 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  55277412631/137438953472.

Let lb_sigma5 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  27638706307/68719476736.

Let lb_sigma6 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  27638706303/68719476736.

Let lb_sigma7 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  55277412615/137438953472.

Let ub_sigma (x0 x1 x2 x3 x4 x5 x6 : R) :=
  1779052236128537/4398046511104.

Let ub_sigma1 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  2668588671163423/4398046511104.

Let ub_sigma2 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  3558129883156913/4398046511104.

Let ub_sigma3 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  3558129883322351/4398046511104.

Let ub_sigma4 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  222383117704275/274877906944.

Let ub_sigma5 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  889532470803647/1099511627776.

Let ub_sigma6 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  3558129883206963/4398046511104.

Let ub_sigma7 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  889532470816829/1099511627776.

Lemma lb_pos (x0 x1 x2 x3 x4 x5 x6 : R) :
  lb_sigma x0 x1 x2 x3 x4 x5 x6 * (p x0 x1 x2 x3 x4 x5 x6 - lb)
  - lb_sigma1 x0 x1 x2 x3 x4 x5 x6 * b1 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma2 x0 x1 x2 x3 x4 x5 x6 * b2 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma3 x0 x1 x2 x3 x4 x5 x6 * b3 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma4 x0 x1 x2 x3 x4 x5 x6 * b4 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma5 x0 x1 x2 x3 x4 x5 x6 * b5 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma6 x0 x1 x2 x3 x4 x5 x6 * b6 x0 x1 x2 x3 x4 x5 x6
  - lb_sigma7 x0 x1 x2 x3 x4 x5 x6 * b7 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3
        /lb_sigma4 /b4 /lb_sigma5 /b5 /lb_sigma6 /b6 /lb_sigma7 /b7.
do_sdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma x0 x1 x2 x3 x4 x5 x6 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma1 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma1. interval. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma2 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma2. interval. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma3 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma3. interval. Qed.

Lemma lb_sigma4_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma4 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma4. interval. Qed.

Lemma lb_sigma5_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma5 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma5. interval. Qed.

Lemma lb_sigma6_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma6 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma6. interval. Qed.

Lemma lb_sigma7_pos (x0 x1 x2 x3 x4 x5 x6 : R) : lb_sigma7 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /lb_sigma7. interval. Qed.

Lemma ub_pos (x0 x1 x2 x3 x4 x5 x6 : R) :
  ub_sigma x0 x1 x2 x3 x4 x5 x6 * (ub - p x0 x1 x2 x3 x4 x5 x6)
  - ub_sigma1 x0 x1 x2 x3 x4 x5 x6 * b1 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma2 x0 x1 x2 x3 x4 x5 x6 * b2 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma3 x0 x1 x2 x3 x4 x5 x6 * b3 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma4 x0 x1 x2 x3 x4 x5 x6 * b4 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma5 x0 x1 x2 x3 x4 x5 x6 * b5 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma6 x0 x1 x2 x3 x4 x5 x6 * b6 x0 x1 x2 x3 x4 x5 x6
  - ub_sigma7 x0 x1 x2 x3 x4 x5 x6 * b7 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof.
rewrite /p /ub /ub_sigma /ub_sigma1 /b1 /ub_sigma2 /b2 /ub_sigma3 /b3
        /ub_sigma4 /b4 /ub_sigma5 /b5 /ub_sigma6 /b6 /ub_sigma7 /b7.
do_sdp.
Qed.

Lemma ub_sigma_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma x0 x1 x2 x3 x4 x5 x6 > 0.
Proof. rewrite /ub_sigma. interval. Qed.

Lemma ub_sigma1_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma1 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma1. interval. Qed.

Lemma ub_sigma2_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma2 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma2. interval. Qed.

Lemma ub_sigma3_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma3 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma3. interval. Qed.

Lemma ub_sigma4_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma4 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma4. interval. Qed.

Lemma ub_sigma5_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma5 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma5. interval. Qed.

Lemma ub_sigma6_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma6 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma6. interval. Qed.

Lemma ub_sigma7_pos (x0 x1 x2 x3 x4 x5 x6 : R) : ub_sigma7 x0 x1 x2 x3 x4 x5 x6 >= 0.
Proof. rewrite /ub_sigma7. interval. Qed.

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
  
Theorem p_ge_lb (x0 x1 x2 x3 x4 x5 x6 : R) :
  -1 <= x0 <= 1 -> -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 -> -1 <= x5 <= 1 -> -1 <= x6 <= 1 ->
  lb <= p x0 x1 x2 x3 x4 x5 x6.
Proof.
move=> H0 H1 H2 H3 H4 H5 H6.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b1 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b2 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b3 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b4 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b5 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b6 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb6 : b7 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b7 -{1}(Ropp_involutive 1); apply var_bounds. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (lb_sigma x0 x1 x2 x3 x4 x5 x6)); [by apply lb_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (lb_sigma1_pos x0 x1 x2 x3 x4 x5 x6) Hb0).
apply (relax _ _ _ (lb_sigma2_pos x0 x1 x2 x3 x4 x5 x6) Hb1).
apply (relax _ _ _ (lb_sigma3_pos x0 x1 x2 x3 x4 x5 x6) Hb2).
apply (relax _ _ _ (lb_sigma4_pos x0 x1 x2 x3 x4 x5 x6) Hb3).
apply (relax _ _ _ (lb_sigma5_pos x0 x1 x2 x3 x4 x5 x6) Hb4).
apply (relax _ _ _ (lb_sigma6_pos x0 x1 x2 x3 x4 x5 x6) Hb5).
apply (relax _ _ _ (lb_sigma7_pos x0 x1 x2 x3 x4 x5 x6) Hb6).
apply lb_pos.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 x4 x5 x6 : R) :
  -1 <= x0 <= 1 -> -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 -> -1 <= x5 <= 1 -> -1 <= x6 <= 1 ->
  p x0 x1 x2 x3 x4 x5 x6 <= ub.
Proof.
move=> H0 H1 H2 H3 H4 H5 H6.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b1 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b2 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b3 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b4 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b5 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b6 -{1}(Ropp_involutive 1); apply var_bounds. }
have Hb6 : b7 x0 x1 x2 x3 x4 x5 x6 >= 0.
{ by rewrite /b7 -{1}(Ropp_involutive 1); apply var_bounds. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (ub_sigma x0 x1 x2 x3 x4 x5 x6)); [by apply ub_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (ub_sigma1_pos x0 x1 x2 x3 x4 x5 x6) Hb0).
apply (relax _ _ _ (ub_sigma2_pos x0 x1 x2 x3 x4 x5 x6) Hb1).
apply (relax _ _ _ (ub_sigma3_pos x0 x1 x2 x3 x4 x5 x6) Hb2).
apply (relax _ _ _ (ub_sigma4_pos x0 x1 x2 x3 x4 x5 x6) Hb3).
apply (relax _ _ _ (ub_sigma5_pos x0 x1 x2 x3 x4 x5 x6) Hb4).
apply (relax _ _ _ (ub_sigma6_pos x0 x1 x2 x3 x4 x5 x6) Hb5).
apply (relax _ _ _ (ub_sigma7_pos x0 x1 x2 x3 x4 x5 x6) Hb6).
apply ub_pos.
Qed.
