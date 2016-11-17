From mathcomp Require Import ssreflect.
Require Import Reals.
From Interval Require Import Interval_tactic.
From ValidSDP Require Import validsdp.

Local Open Scope R_scope.

Let p (x0 x1 x2 x3 : R) :=
  (0 - x0) * (x2)^3 + 4 * x1 * (x2)^2 * x3 + 4 * x0 * x2 * (x3)^2
  + 2 * x1 * (x3)^3 + 4 * x0 * x2 + 4 * (x2)^2 - 10 * x1 * x3 - 10 * (x3)^2
  + 2.

Let b1 (x0 x1 x2 x3 : R) :=
  (x0 + 1/2) * (1/2 - x0).

Let b2 (x0 x1 x2 x3 : R) :=
  (x1 + 1/2) * (1/2 - x1).

Let b3 (x0 x1 x2 x3 : R) :=
  (x2 + 1/2) * (1/2 - x2).

Let b4 (x0 x1 x2 x3 : R) :=
  (x3 + 1/2) * (1/2 - x3).

Let lb := -3181/1000.

Let ub := 4486/1000.

Let lb_sigma (x0 x1 x2 x3 : R) :=
  725394200409815/68719476736.

Let lb_sigma1 (x0 x1 x2 x3 : R) :=
  270601566977209/68719476736 + 2673882925076061/137438953472 * x0^2
  + 1688597368876505/137438953472 * x1^2
  + 322420458963949/68719476736 * x0 * x2
  + 1486414419775159/68719476736 * x2^2
  + -1781147113323347/137438953472 * x1 * x3
  + 1804608149767255/137438953472 * x3^2.

Let lb_sigma2 (x0 x1 x2 x3 : R) :=
  992945604707005/34359738368 + 1254199804873191/68719476736 * x0^2
  + 1110018315379963/34359738368 * x1^2
  + 47242460188191/17179869184 * x0 * x2
  + 2746974638749405/137438953472 * x2^2
  + 47987391154535/17179869184 * x1 * x3 + 805526331728895/34359738368 * 
  x3^2.

Let lb_sigma3 (x0 x1 x2 x3 : R) :=
  243821101527/34359738368 + 328579613767341/68719476736 * x0^2
  + 1399589350439053/137438953472 * x1^2
  + 1357430183626229/68719476736 * x0 * x2
  + 2820672575740735/137438953472 * x2^2
  + -2795201992952591/137438953472 * x1 * x3
  + 1399512045426751/137438953472 * x3^2.

Let lb_sigma4 (x0 x1 x2 x3 : R) :=
  4421366461173739/34359738368 + 3385577932567967/137438953472 * x0^2
  + 3944094731196885/137438953472 * x1^2
  + -289137253697785/68719476736 * x0 * x2
  + 3178232543120263/137438953472 * x2^2
  + 156703708923763/34359738368 * x1 * x3 + 318848071303837/8589934592 * 
  x3^2.

Let ub_sigma (x0 x1 x2 x3 : R) :=
  649065311135479/34359738368.

Let ub_sigma1 (x0 x1 x2 x3 : R) :=
  1242770077707163/68719476736 + 4332293307531911/137438953472 * x0^2
  + 2641340916804937/137438953472 * x1^2
  + 67994445261751/68719476736 * x0 * x2
  + 3020547715825575/137438953472 * x2^2
  + 58497890650429/17179869184 * x1 * x3
  + 3608270562866957/137438953472 * x3^2.

Let ub_sigma2 (x0 x1 x2 x3 : R) :=
  706320380126037/34359738368 + 2740814972901887/137438953472 * x0^2
  + 1273428968146125/34359738368 * x1^2
  + -291764029962897/68719476736 * x0 * x2
  + 1311314850250137/68719476736 * x2^2
  + -132647133533499/68719476736 * x1 * x3
  + 3820655019040887/137438953472 * x3^2.

Let ub_sigma3 (x0 x1 x2 x3 : R) :=
  2462749074062709/34359738368 + 4005329203070675/137438953472 * x0^2
  + 3230928493680159/137438953472 * x1^2
  + 278744395414153/34359738368 * x0 * x2
  + 1611451404345403/34359738368 * x2^2
  + 216900899059619/34359738368 * x1 * x3
  + 3630010232715583/137438953472 * x3^2.

Let ub_sigma4 (x0 x1 x2 x3 : R) :=
  174240505547/17179869184 + 72764290627759/8589934592 * x0^2
  + 507788637087493/68719476736 * x1^2
  + -2322167645642019/137438953472 * x0 * x2
  + 18179944770687/2147483648 * x2^2
  + 4211098470723089/137438953472 * x1 * x3
  + 2194712047907809/68719476736 * x3^2.

Lemma lb_pos (x0 x1 x2 x3 : R) :
  lb_sigma x0 x1 x2 x3 * (p x0 x1 x2 x3 - lb)
  - lb_sigma1 x0 x1 x2 x3 * b1 x0 x1 x2 x3
  - lb_sigma2 x0 x1 x2 x3 * b2 x0 x1 x2 x3
  - lb_sigma3 x0 x1 x2 x3 * b3 x0 x1 x2 x3
  - lb_sigma4 x0 x1 x2 x3 * b4 x0 x1 x2 x3 >= 0.
Proof.
rewrite /p /lb /lb_sigma /lb_sigma1 /b1 /lb_sigma2 /b2 /lb_sigma3 /b3 /lb_sigma4 /b4.
validsdp.
Qed.

Lemma lb_sigma_pos (x0 x1 x2 x3 : R) : lb_sigma x0 x1 x2 x3 > 0.
Proof. rewrite /lb_sigma. interval. Qed.

Lemma lb_sigma1_pos (x0 x1 x2 x3 : R) : lb_sigma1 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma1. validsdp. Qed.

Lemma lb_sigma2_pos (x0 x1 x2 x3 : R) : lb_sigma2 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma2. validsdp. Qed.

Lemma lb_sigma3_pos (x0 x1 x2 x3 : R) : lb_sigma3 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma3. validsdp. Qed.

Lemma lb_sigma4_pos (x0 x1 x2 x3 : R) : lb_sigma4 x0 x1 x2 x3 >= 0.
Proof. rewrite /lb_sigma4. validsdp. Qed.

Lemma ub_pos (x0 x1 x2 x3 : R) :
  ub_sigma x0 x1 x2 x3 * (ub - p x0 x1 x2 x3)
  - ub_sigma1 x0 x1 x2 x3 * b1 x0 x1 x2 x3
  - ub_sigma2 x0 x1 x2 x3 * b2 x0 x1 x2 x3
  - ub_sigma3 x0 x1 x2 x3 * b3 x0 x1 x2 x3
  - ub_sigma4 x0 x1 x2 x3 * b4 x0 x1 x2 x3 >= 0.
Proof.
rewrite /p /ub /ub_sigma /ub_sigma1 /b1 /ub_sigma2 /b2 /ub_sigma3 /b3 /ub_sigma4 /b4.
validsdp.
Qed.

Lemma ub_sigma_pos (x0 x1 x2 x3 : R) : ub_sigma x0 x1 x2 x3 > 0.
Proof. rewrite /ub_sigma. interval. Qed.

Lemma ub_sigma1_pos (x0 x1 x2 x3 : R) : ub_sigma1 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma1. validsdp. Qed.

Lemma ub_sigma2_pos (x0 x1 x2 x3 : R) : ub_sigma2 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma2. validsdp. Qed.

Lemma ub_sigma3_pos (x0 x1 x2 x3 : R) : ub_sigma3 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma3. validsdp. Qed.

Lemma ub_sigma4_pos (x0 x1 x2 x3 : R) : ub_sigma4 x0 x1 x2 x3 >= 0.
Proof. rewrite /ub_sigma4. validsdp. Qed.

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
  -1/2 <= x0 <= 1/2 -> -1/2 <= x1 <= 1/2 -> -1/2 <= x2 <= 1/2 -> -1/2 <= x3 <= 1/2 ->
  lb <= p x0 x1 x2 x3.
Proof.
move=> H0 H1 H2 H3.
have Hb0 : b1 x0 x1 x2 x3 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb1 : b2 x0 x1 x2 x3 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb2 : b3 x0 x1 x2 x3 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb3 : b4 x0 x1 x2 x3 >= 0.
{ rewrite /b4 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
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
  -1/2 <= x0 <= 1/2 -> -1/2 <= x1 <= 1/2 -> -1/2 <= x2 <= 1/2 -> -1/2 <= x3 <= 1/2 ->
  p x0 x1 x2 x3 <= ub.
Proof.
move=> H0 H1 H2 H3.
have Hb0 : b1 x0 x1 x2 x3 >= 0.
{ rewrite /b1 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb1 : b2 x0 x1 x2 x3 >= 0.
{ rewrite /b2 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb2 : b3 x0 x1 x2 x3 >= 0.
{ rewrite /b3 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
have Hb3 : b4 x0 x1 x2 x3 >= 0.
{ rewrite /b4 -{1}(Ropp_involutive (_ / _)).
  by apply var_bounds; rewrite -Ropp_div. }
apply Rge_le, Rminus_ge, Rle_ge.
apply (Rmult_le_reg_l (ub_sigma x0 x1 x2 x3)); [by apply ub_sigma_pos|].
rewrite Rmult_0_r; apply Rge_le.
apply (relax _ _ _ (ub_sigma1_pos x0 x1 x2 x3) Hb0).
apply (relax _ _ _ (ub_sigma2_pos x0 x1 x2 x3) Hb1).
apply (relax _ _ _ (ub_sigma3_pos x0 x1 x2 x3) Hb2).
apply (relax _ _ _ (ub_sigma4_pos x0 x1 x2 x3) Hb3).
apply ub_pos.
Qed.
