From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 : R) :=
  x0 * (x1)^2 + x0 * (x2)^2 + x0 * (x3)^2 - 11/10 * x0 + 1.

Let b1 (x0 x1 x2 x3 : R) :=
  (x0 + 2/1) * (2/1 - x0).

Let b2 (x0 x1 x2 x3 : R) :=
  (x1 + 2/1) * (2/1 - x1).

Let b3 (x0 x1 x2 x3 : R) :=
  (x2 + 2/1) * (2/1 - x2).

Let b4 (x0 x1 x2 x3 : R) :=
  (x3 + 2/1) * (2/1 - x3).

Let lb := -20802/1000.

Let ub := 22802/1000.

Let lb_sigma (x0 x1 x2 x3 : R) :=
  7440659867365075/2251799813685248.

Let lb_sigma1 (x0 x1 x2 x3 : R) :=
  4646999889723611/2361183241434822606848
  + -5811704356722117/38685626227668133590597632 * x0
  + 3504101721412145/9007199254740992 * x0^2
  + 5590803803060975/9007199254740992 * x1^2
  + 5590803796393575/9007199254740992 * x2^2
  + 1397700955047449/2251799813685248 * x3^2.

Let lb_sigma2 (x0 x1 x2 x3 : R) :=
  2323501630298437/1180591620717411303424
  + -24829150100695/151115727451828646838272 * x0
  + 4654531034550513/2361183241434822606848 * x0^2
  + 4960697062374543/9007199254740992 * x1^2
  + 1240170819321323/2251799813685248 * x2^2
  + 4960542700855359/9007199254740992 * x3^2.

Let lb_sigma3 (x0 x1 x2 x3 : R) :=
  4647003260596863/2361183241434822606848
  + -397266401547371/2417851639229258349412352 * x0
  + 4654531034550305/2361183241434822606848 * x0^2
  + 310033917947413/562949953421312 * x1^2
  + 620087132138359/1125899906842624 * x2^2
  + 1240170824066565/2251799813685248 * x3^2.

Let lb_sigma4 (x0 x1 x2 x3 : R) :=
  2323501630298439/1180591620717411303424
  + -3178131213145349/19342813113834066795298816 * x0
  + 4654531034550159/2361183241434822606848 * x0^2
  + 1240170820646921/2251799813685248 * x1^2
  + 4960542681926061/9007199254740992 * x2^2
  + 2480348538016775/4503599627370496 * x3^2.

Let ub_sigma (x0 x1 x2 x3 : R) :=
  3720319242919605/1125899906842624.

Let ub_sigma1 (x0 x1 x2 x3 : R) :=
  4678850716090783/2361183241434822606848
  + 2862612374170229/151115727451828646838272 * x0
  + 438011962480251/1125899906842624 * x0^2
  + 698848294791251/1125899906842624 * x1^2
  + 5590786353691473/9007199254740992 * x2^2
  + 5590786357594173/9007199254740992 * x3^2.

Let ub_sigma2 (x0 x1 x2 x3 : R) :=
  4679895057315317/2361183241434822606848
  + 1559085303016559/75557863725914323419136 * x0
  + 5572102824200003/2361183241434822606848 * x0^2
  + 4960681807412779/9007199254740992 * x1^2
  + 4960594987544269/9007199254740992 * x2^2
  + 4960599858576897/9007199254740992 * x3^2.

Let ub_sigma3 (x0 x1 x2 x3 : R) :=
  4679895057893141/2361183241434822606848
  + 389771326145133/18889465931478580854784 * x0
  + 5572102845112319/2361183241434822606848 * x0^2
  + 4960599859225139/9007199254740992 * x1^2
  + 4960681803812687/9007199254740992 * x2^2
  + 620074373674583/1125899906842624 * x3^2.

Let ub_sigma4 (x0 x1 x2 x3 : R) :=
  1169973764448697/590295810358705651712
  + 6236341217102733/302231454903657293676544 * x0
  + 5572102841199271/2361183241434822606848 * x0^2
  + 2480297495614835/4503599627370496 * x1^2
  + 2480299927906349/4503599627370496 * x2^2
  + 2480340903310167/4503599627370496 * x3^2.

Lemma lb_pos (x0 x1 x2 x3 : R) :
  lb_sigma x0 x1 x2 x3 * (p x0 x1 x2 x3 - lb)
  - lb_sigma1 x0 x1 x2 x3 * b1 x0 x1 x2 x3
  - lb_sigma2 x0 x1 x2 x3 * b2 x0 x1 x2 x3
  - lb_sigma3 x0 x1 x2 x3 * b3 x0 x1 x2 x3
  - lb_sigma4 x0 x1 x2 x3 * b4 x0 x1 x2 x3 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3 /lb_sigma4 /b4.
do_sdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 x3 : R) : lb_sigma x0 x1 x2 x3 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 x3 : R) : lb_sigma1 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma1. do_sdp. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 x3 : R) : lb_sigma2 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma2. do_sdp. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 x3 : R) : lb_sigma3 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma3. do_sdp. Qed.

Lemma lb_sigma4_pos (x0 x1 x2 x3 : R) : lb_sigma4 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma4. do_sdp. Qed.

Lemma ub_pos (x0 x1 x2 x3 : R) :
  ub_sigma x0 x1 x2 x3 * (ub - p x0 x1 x2 x3)
  - ub_sigma1 x0 x1 x2 x3 * b1 x0 x1 x2 x3
  - ub_sigma2 x0 x1 x2 x3 * b2 x0 x1 x2 x3
  - ub_sigma3 x0 x1 x2 x3 * b3 x0 x1 x2 x3
  - ub_sigma4 x0 x1 x2 x3 * b4 x0 x1 x2 x3 >= 0.
Proof.
rewrite /p /ub /ub_sigma /ub_sigma1 /b1 /ub_sigma2 /b2 /ub_sigma3 /b3 /ub_sigma4 /b4.
do_sdp.
Qed.

Lemma ub_sigma_pos (x0 x1 x2 x3 : R) : ub_sigma x0 x1 x2 x3 > 0.
Proof. rewrite /ub_sigma. interval. Qed.

Lemma ub_sigma1_pos (x0 x1 x2 x3 : R) : ub_sigma1 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma1. do_sdp. Qed.

Lemma ub_sigma2_pos (x0 x1 x2 x3 : R) : ub_sigma2 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma2. do_sdp. Qed.

Lemma ub_sigma3_pos (x0 x1 x2 x3 : R) : ub_sigma3 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma3. do_sdp. Qed.

Lemma ub_sigma4_pos (x0 x1 x2 x3 : R) : ub_sigma4 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma4. do_sdp. Qed.

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
  
Theorem p_ge_lb (x0 x1 x2 x3 : R) :
  -2 <= x0 <= 2 -> -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 ->
  lb <= p x0 x1 x2 x3.
Proof.
move=> H0 H1 H2 H3.
have Hb0 : b1 x0 x1 x2 x3 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb1 : b2 x0 x1 x2 x3 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 x3 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb3 : b4 x0 x1 x2 x3 >= 0.
{ rewrite /b4 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (lb_sigma x0 x1 x2 x3)); [by apply lb_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (lb_sigma1_pos x0 x1 x2 x3) Hb0).
apply (relax _ _ _ (lb_sigma2_pos x0 x1 x2 x3) Hb1).
apply (relax _ _ _ (lb_sigma3_pos x0 x1 x2 x3) Hb2).
apply (relax _ _ _ (lb_sigma4_pos x0 x1 x2 x3) Hb3).
apply lb_pos.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 : R) :
  -2 <= x0 <= 2 -> -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 ->
  p x0 x1 x2 x3 <= ub.
Proof.
move=> H0 H1 H2 H3.
have Hb0 : b1 x0 x1 x2 x3 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb1 : b2 x0 x1 x2 x3 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb2 : b3 x0 x1 x2 x3 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
have Hb3 : b4 x0 x1 x2 x3 >= 0.
{ rewrite /b4 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div !Rcomplements.Rdiv_1. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (ub_sigma x0 x1 x2 x3)); [by apply ub_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (ub_sigma1_pos x0 x1 x2 x3) Hb0).
apply (relax _ _ _ (ub_sigma2_pos x0 x1 x2 x3) Hb1).
apply (relax _ _ _ (ub_sigma3_pos x0 x1 x2 x3) Hb2).
apply (relax _ _ _ (ub_sigma4_pos x0 x1 x2 x3) Hb3).
apply ub_pos.
Qed.
