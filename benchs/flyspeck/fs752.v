From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  (0 - x1) * x2 - x0 * x3 + x1 * x4 + x2 * x5 - x4 * x5
  + x0 * (0 - x0 + x1 + x2 - x3 + x4 + x5).

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 - 4/1) * (63504/10000 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 - 4/1) * (63504/10000 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 - 4/1) * (63504/10000 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 - 4/1) * (63504/10000 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 - 4/1) * (63504/10000 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 - 8/1) * (254016/10000 - x5).

Let sigma (x0 x1 x2 x3 x4 x5 : R) :=
  7634916093561979/36028797018963968.

Let sigma1 (x0 x1 x2 x3 x4 x5 : R) :=
  1907236905925199/2251799813685248.

Let sigma2 (x0 x1 x2 x3 x4 x5 : R) :=
  6065442019836759/9007199254740992.

Let sigma3 (x0 x1 x2 x3 x4 x5 : R) :=
  532695258865619/562949953421312.

Let sigma4 (x0 x1 x2 x3 x4 x5 : R) :=
  3838900911882699/4503599627370496.

Let sigma5 (x0 x1 x2 x3 x4 x5 : R) :=
  1629752366943531/2251799813685248.

Let sigma6 (x0 x1 x2 x3 x4 x5 : R) :=
  4395491125087337/72057594037927936.

Lemma relax_pos (x0 x1 x2 x3 x4 x5 : R) :
  sigma x0 x1 x2 x3 x4 x5 * p x0 x1 x2 x3 x4 x5
  - sigma1 x0 x1 x2 x3 x4 x5 * b1 x0 x1 x2 x3 x4 x5
  - sigma2 x0 x1 x2 x3 x4 x5 * b2 x0 x1 x2 x3 x4 x5
  - sigma3 x0 x1 x2 x3 x4 x5 * b3 x0 x1 x2 x3 x4 x5
  - sigma4 x0 x1 x2 x3 x4 x5 * b4 x0 x1 x2 x3 x4 x5
  - sigma5 x0 x1 x2 x3 x4 x5 * b5 x0 x1 x2 x3 x4 x5
  - sigma6 x0 x1 x2 x3 x4 x5 * b6 x0 x1 x2 x3 x4 x5 - 1/100000000 >= 0.
Proof.
rewrite /sigma /p /sigma1 /b1 /sigma2 /b2 /sigma3 /b3 /sigma4 /b4 /sigma5 /b5 /sigma6 /b6.
validsdp.
Qed.

Lemma sigma_pos (x0 x1 x2 x3 x4 x5 : R) : sigma x0 x1 x2 x3 x4 x5 > 0.
Proof. rewrite /sigma. interval. Qed.

Lemma sigma1_pos (x0 x1 x2 x3 x4 x5 : R) : sigma1 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma1. interval. Qed.

Lemma sigma2_pos (x0 x1 x2 x3 x4 x5 : R) : sigma2 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma2. interval. Qed.

Lemma sigma3_pos (x0 x1 x2 x3 x4 x5 : R) : sigma3 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma3. interval. Qed.

Lemma sigma4_pos (x0 x1 x2 x3 x4 x5 : R) : sigma4 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma4. interval. Qed.

Lemma sigma5_pos (x0 x1 x2 x3 x4 x5 : R) : sigma5 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma5. interval. Qed.

Lemma sigma6_pos (x0 x1 x2 x3 x4 x5 : R) : sigma6 x0 x1 x2 x3 x4 x5 >= 0.
Proof. rewrite /sigma6. interval. Qed.

Lemma var_bounds (x l u : R) : l <= x <= u -> (x - l) * (u - x) >= 0.
Proof.
move=> [Hl Hu].
apply Rle_ge.
by apply Interval_missing.Rmult_le_pos_pos; apply Fcore_Raux.Rle_0_minus.
Qed.

Lemma relax (x y z : R) : x >= 0 -> y >= 0 -> z - x * y > 0 -> z > 0.
Proof.
move=> HX Hy.
apply Rge_gt_trans, Rle_ge.
rewrite -{2}(Rminus_0_r z).
apply Rplus_le_compat_l, Ropp_le_contravar.
by apply Interval_missing.Rmult_le_pos_pos; apply Rge_le.
Qed.
  
Theorem p_pos (x0 x1 x2 x3 x4 x5 x6 : R) :
  4 <= x0 <= 63504 / 10000 ->
  4 <= x1 <= 63504 / 10000 ->
  4 <= x2 <= 63504 / 10000 ->
  4 <= x3 <= 63504 / 10000 ->
  4 <= x4 <= 63504 / 10000 ->
  8 <= x5 <= 254016 / 10000 ->
  p x0 x1 x2 x3 x4 x5 > 0.
Proof.
move=> H1 H2 H3 H4 H5 H6.
have Hb0 : b1 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
have Hb1 : b2 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
have Hb3 : b4 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
have Hb4 : b5 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
have Hb5 : b6 x0 x1 x2 x3 x4 x5 >= 0.
{ by apply var_bounds; rewrite !Rcomplements.Rdiv_1. }
apply (Rmult_lt_reg_l (sigma x0 x1 x2 x3 x4 x5)); [by apply sigma_pos|].
rewrite Rmult_0_r.
apply (relax _ _ _ (sigma1_pos x0 x1 x2 x3 x4 x5) Hb0).
apply (relax _ _ _ (sigma2_pos x0 x1 x2 x3 x4 x5) Hb1).
apply (relax _ _ _ (sigma3_pos x0 x1 x2 x3 x4 x5) Hb2).
apply (relax _ _ _ (sigma4_pos x0 x1 x2 x3 x4 x5) Hb3).
apply (relax _ _ _ (sigma5_pos x0 x1 x2 x3 x4 x5) Hb4).
apply (relax _ _ _ (sigma6_pos x0 x1 x2 x3 x4 x5) Hb5).
move: (relax_pos x0 x1 x2 x3 x4 x5).
apply Rgt_ge_trans.
rewrite -{1}(Rplus_0_r (_ - _)).
apply (Rplus_gt_compat_l).
interval.
Qed.
