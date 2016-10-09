From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 : R) :=
  (x0 - x1)^2 + (x1 - 1)^2 + (x0 - (x2)^2)^2 + (x2 - 1)^2.

Let b1 (x0 x1 x2 : R) :=
  (x0 + 10) * (10 - x0).

Let b2 (x0 x1 x2 : R) :=
  (x1 + 10) * (10 - x1).

Let b3 (x0 x1 x2 : R) :=
  (x2 + 10) * (10 - x2).

Let lb := -1/10000.

Let ub := 12800/1.

Let lb_sigma (x0 x1 x2 : R) :=
  6075076687004067/281474976710656.

Let lb_sigma1 (x0 x1 x2 : R) :=
  7861677775023705/72057594037927936
  + 6819959636995119/9671406556917033397649408 * x0
  + -8034942811885227/288230376151711744 * x1
  + -1714221072618407/9007199254740992 * x2
  + 4626760829135455/72057594037927936 * x0^2
  + -2313388770721395/18014398509481984 * x0 * x1
  + 2815655607595063/36028797018963968 * x1^2
  + -2251498434012833/1208925819614629174706176 * x0 * x2
  + -3614796312565441/604462909807314587353088 * x1 * x2
  + 6856720121343935/72057594037927936 * x2^2.

Let lb_sigma2 (x0 x1 x2 : R) :=
  3788730862615999/144115188075855872
  + 6644807044063285/9671406556917033397649408 * x0
  + -7576596686426099/144115188075855872 * x1
  + -4103041387609989/18889465931478580854784 * x2
  + 7219839170287757/288230376151711744 * x0^2
  + -7219615006370765/144115188075855872 * x0 * x1
  + 7398192513861493/144115188075855872 * x1^2
  + -1083236320587187/604462909807314587353088 * x0 * x2
  + -4261466556185365/604462909807314587353088 * x1 * x2
  + 7251888076430351/4722366482869645213696 * x2^2.

Let lb_sigma3 (x0 x1 x2 : R) :=
  5295111535484571/18014398509481984
  + 7366503389714963/9671406556917033397649408 * x0
  + -6269017998701199/18014398509481984 * x1
  + -540079370887233/2251799813685248 * x2
  + 2269847788677363/18014398509481984 * x0^2
  + -4539761311758343/18014398509481984 * x0 * x1
  + 1351074631935433/4503599627370496 * x1^2
  + -2176899055311441/1208925819614629174706176 * x0 * x2
  + -1663402048813149/302231454903657293676544 * x1 * x2
  + 8641036266330383/72057594037927936 * x2^2.

Lemma lb_pos (x0 x1 x2 : R) :
  lb_sigma x0 x1 x2 * (p x0 x1 x2 - lb)
  - lb_sigma1 x0 x1 x2 * b1 x0 x1 x2
  - lb_sigma2 x0 x1 x2 * b2 x0 x1 x2
  - lb_sigma3 x0 x1 x2 * b3 x0 x1 x2 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3.
do_sdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 : R) : lb_sigma x0 x1 x2 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 : R) : lb_sigma1 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma1. do_sdp. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 : R) : lb_sigma2 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma2. do_sdp. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 : R) : lb_sigma3 x0 x1 x2 >= 0.
Proof. rewrite /lb_sigma3. do_sdp. Qed.

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
  -10 <= x0 <= 10 -> -10 <= x1 <= 10 -> -10 <= x2 <= 10 -> lb <= p x0 x1 x2.
Proof.
move=> H0 H1 H2.
have Hb0 : b1 x0 x1 x2 >= 0.
{ by rewrite /b1 -{1}(Ropp_involutive 10); apply var_bounds. }
have Hb1 : b2 x0 x1 x2 >= 0.
{ by rewrite /b2 -{1}(Ropp_involutive 10); apply var_bounds. }
have Hb2 : b3 x0 x1 x2 >= 0.
{ by rewrite /b3 -{1}(Ropp_involutive 10); apply var_bounds. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (lb_sigma x0 x1 x2)); [by apply lb_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (lb_sigma1_pos x0 x1 x2) Hb0).
apply (relax _ _ _ (lb_sigma2_pos x0 x1 x2) Hb1).
apply (relax _ _ _ (lb_sigma3_pos x0 x1 x2) Hb2).
apply lb_pos.
Qed.
