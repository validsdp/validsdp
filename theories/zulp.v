Require Import Reals.
Require Import BigQ.
Require Import ROmega.
From Flocq Require Import Fcore_defs.
From Flocq Require Import Fcore_digits.
From Interval Require Import Interval_float_sig.
From Interval Require Import Interval_interval.
From Interval Require Import Interval_interval_float_full.
From Interval Require Import Interval_bigint_carrier.
From Interval Require Import Interval_definitions.
From Interval Require Import Interval_specific_ops.
From Interval Require Import Interval_xreal.
From Interval Require Import Interval_missing.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import misc coqinterval_infnan.

Notation toR := (fun f => proj_val (F.toX f)).

Lemma real_FtoX_toR f : F.real f -> F.toX f = Xreal (toR f).
Proof. by rewrite FtoX_real; rewrite /X_real; case: F.toX. Qed.

Lemma Xreal_inj x y : Xreal x = Xreal y -> x = y.
Proof. by case. Qed.

(** Number of radix2-[digits] of a [bigZ] number *)

Definition digits (m : bigZ) : bigZ :=
  match m with
  | BigZ.Pos n => Bir.mantissa_digits n
  | BigZ.Neg n => Bir.mantissa_digits n
  end.

Definition Zdigits2 (n : Z) := Zdigits radix2 n.

Lemma Zdigits2_mult_Zpower m e : m <> Z0 -> (0 <= e)%Z ->
  Zdigits2 (m * 2 ^ e) = (Zdigits2 m + e)%Z.
Proof. exact: Zdigits_mult_Zpower. Qed.

Lemma Zdigits2_double m : m <> Z0 -> Zdigits2 (Z.double m) = (Z.succ (Zdigits2 m))%Z.
Proof.
move=> NZm.
suff->: Z.double m = (m * 2 ^ 1)%Z by apply: Zdigits2_mult_Zpower.
by rewrite Z.double_spec Zmult_comm.
Qed.

Lemma Zdigits_opp r (n : Z) : Zdigits r (- n) = Zdigits r n.
Proof. by case: n. Qed.

Lemma digits_spec n : [digits n]%bigZ = Zdigits2 [n]%bigZ.
Proof.
rewrite /digits; case: n => n.
have Hn : [n]%bigN = Z0 \/ [n]%bigN <> Z0.
{ case E: [n]%bigN => [|p|p]; [by left|by right|exfalso].
  by have := BigN.spec_pos n; rewrite E; auto. }
have {Hn} [Zn|NZn] := Hn.
{ rewrite /= Zn /= BigN.spec_sub.
  apply/Z.max_l_iff.
  rewrite BigN.spec_Ndigits BigN.spec_head00 //.
  zify; omega. }
{ rewrite [LHS]Bir.mantissa_digits_correct; last first.
  { case E: [BigZ.Pos n]%bigZ NZn => [|p|p] //= NZn.
    exists p; by rewrite -E.
    clear NZn; exfalso; simpl in E.
    by have := BigN.spec_pos n; rewrite E; auto. }
  rewrite -Interval_generic_proof.digits_conversion.
  rewrite /Zdigits2; f_equal.
  rewrite /= /Bir.MtoP; simpl in NZn.
  have := BigN.spec_pos n; case: [n]%bigN NZn => [p|p|] NZn; try done.
    by move=> _ K; exfalso; auto. }
(* almost same proof *)
have Hn : [n]%bigN = Z0 \/ [n]%bigN <> Z0.
{ case E: [n]%bigN => [|p|p]; [by left|by right|exfalso].
  by have := BigN.spec_pos n; rewrite E; auto. }
have {Hn} [Zn|NZn] := Hn.
{ rewrite /= Zn /= BigN.spec_sub.
  apply/Z.max_l_iff.
  rewrite BigN.spec_Ndigits BigN.spec_head00 //.
  zify; omega. }
{ rewrite [LHS]Bir.mantissa_digits_correct; last first.
  { case E: [BigZ.Pos n]%bigZ NZn => [|p|p] //= NZn.
    exists p; by rewrite -E.
    clear NZn; exfalso; simpl in E.
    by have := BigN.spec_pos n; rewrite E; auto. }
  rewrite -Interval_generic_proof.digits_conversion.
  rewrite [RHS]Zdigits_opp /Zdigits2; f_equal.
  rewrite /= /Bir.MtoP; simpl in NZn.
  have := BigN.spec_pos n; case: [n]%bigN NZn => [p|p|] NZn; try done.
  by move=> _ K; exfalso; auto. }
Qed.

Lemma digits_ge0 n :(0 <= digits n)%bigZ.
Proof.
apply/BigZ.leb_le.
rewrite BigZ.spec_leb digits_spec //.
exact/Zle_is_le_bool/Zdigits_ge_0.
Qed.

Lemma digits_gt0 n : [n]%bigZ <> Z0 -> (0 < digits n)%bigZ.
Proof.
move=> NZn; apply/BigZ.ltb_lt.
rewrite BigZ.spec_ltb digits_spec //.
exact/Zlt_is_lt_bool/Zdigits_gt_0.
Qed.

(** Definition of ulp (unit in the last place) for signed integers *)

Definition Zulp (m : Z) : Z := Z.land m (- m).

Definition bigZulp (m : bigZ) : bigZ := BigZ.land m (- m).

Lemma bigZulp_spec m : [bigZulp m]%bigZ = Zulp [m]%bigZ.
Proof. by rewrite BigZ.spec_land BigZ.spec_opp. Qed.

(** Preliminary results *)

Lemma Pos_ldiff_eq0 p : Pos.ldiff p p = 0%num.
Proof.
apply: N.bits_inj_0 => n.
elim: p n =>[p IHp|p IHp|//] n.
{ case: n => [/=|n].
  by rewrite N.testbit_even_0.
  rewrite -N.succ_pos_pred.
  by rewrite N.double_bits_succ. }
case: n => [/=|n].
by rewrite N.testbit_even_0.
rewrite -N.succ_pos_pred.
by rewrite N.double_bits_succ.
Qed.

Lemma Pos_ldiff_neq0 q : Pos.ldiff (Pos.succ q) q <> 0%num.
Proof.
elim: q => [q IHq|q IHq|] //=; first by case: Pos.ldiff IHq.
by rewrite /Pos.Nsucc_double Pos_ldiff_eq0.
Qed.

Lemma Pos_ldiff_mod q :
  (N.pos (Pos.succ q) mod Pos.ldiff (Pos.succ q) q)%num = N0.
Proof.
elim: q => [q IHp|q IHp|] =>//=.
now_show (N.double (N.pos (Pos.succ q)) mod N.double (Pos.ldiff (Pos.succ q) q)
  = 0)%num.
rewrite !N.double_spec !N.mul_mod_distr_l; [|exact: Pos_ldiff_neq0|done].
by rewrite IHp.
by rewrite Pos_ldiff_eq0 /= N.mod_1_r.
Qed.

Lemma Zdivide_div_l a b : (a | b)%Z -> (b / a | b)%Z.
Proof.
case: a => [|p|p]; first by rewrite Zdiv_0_r.
by case => z ->; rewrite Z_div_mult_full //; apply Z.divide_mul_l, Z.divide_refl.
by case => z ->; rewrite Z_div_mult_full //; apply Z.divide_mul_l, Z.divide_refl.
Qed.

Lemma Rabs_div_gt_1 a b : a <> R0 -> Rabs a < b <-> 1 < b / Rabs a.
Proof.
move=> H0; split => Hab.
{ rewrite -[R1](Rinv_r_simpl_l (Rabs a)); last exact: Rabs_no_R0.
  rewrite Rmult_1_l /Rdiv.
  apply: Rmult_lt_compat_r =>//.
  apply/Rinv_0_lt_compat.
  exact: Rabs_pos_lt. }
{ apply (Rmult_lt_reg_r (/ Rabs a)).
  exact/Rinv_0_lt_compat/Rabs_pos_lt.
  rewrite (Rinv_r (Rabs a)) //.
  exact: Rabs_no_R0. }
Qed.

Lemma Rdiv_gt_1 a b : (0 < a)%R -> a < b <-> 1 < b / a.
Proof.
move=> H0.
rewrite -(Rabs_pos_eq _ (Rlt_le _ _ H0)).
apply: Rabs_div_gt_1 =>//.
exact: Rgt_not_eq.
Qed.

(** Support results on [Zulp] *)

Lemma Zulp_gt0 m : m <> Z0 -> (0 < Zulp m)%Z.
Proof.
move => NZm; rewrite /Zulp.
case: m NZm => [//|p|p] NZm /=.
{ change Z0 with (Z.of_N N0).
  apply N2Z.inj_lt.
  case E: Pos.pred_N => [//|q].
  apply/N.neq_0_lt_0 =>K.
  have {K} K' : forall n, N.testbit (Pos.ldiff p q) n = false.
  { by move=> n; rewrite K N.bits_0. }
  have Hp: p = (q + 1)%positive.
  { zify.
    by rewrite -E N.pos_pred_spec N2Z.inj_pred // -/(Zsucc _) -Zsucc_pred. }
  clear E NZm.
  rewrite {}Hp in K'.
  elim: q K' => [q IHq|q IHq|] K'.
  - apply: IHq => n.
    move/(_ (N.succ n)) in K'.
    by rewrite N.double_bits_succ -Pos.add_1_r in K'.
  - move/(_ 0%num) in K'.
    rewrite N.pos_ldiff_spec in K'.
    by move/negbT/negP in K'; apply: K'.
  - move/(_ 1%num) in K'.
    rewrite N.pos_ldiff_spec in K'.
    by move/negbT/negP in K'; apply: K'. }
(* same proof *)
{ change Z0 with (Z.of_N N0).
  apply N2Z.inj_lt.
  case E: Pos.pred_N => [//|q].
  apply/N.neq_0_lt_0 =>K.
  have {K} K' : forall n, N.testbit (Pos.ldiff p q) n = false.
  { by move=> n; rewrite K N.bits_0. }
  have Hp: p = (q + 1)%positive.
  { zify.
    by rewrite -E N.pos_pred_spec N2Z.inj_pred // -/(Zsucc _) -Zsucc_pred. }
  clear E NZm.
  rewrite {}Hp in K'.
  elim: q K' => [q IHq|q IHq|] K'.
  - apply: IHq => n.
    move/(_ (N.succ n)) in K'.
    by rewrite N.double_bits_succ -Pos.add_1_r in K'.
  - move/(_ 0%num) in K'.
    rewrite N.pos_ldiff_spec in K'.
    by move/negbT/negP in K'; apply: K'.
  - move/(_ 1%num) in K'.
    rewrite N.pos_ldiff_spec in K'.
    by move/negbT/negP in K'; apply: K'. }
Qed.

Lemma Zulp_neq0 m : m <> Z0 -> (Zulp m <> 0)%Z.
Proof. by move=> NZm; apply/BigNumPrelude.Zlt0_not_eq/Zulp_gt0. Qed.

Lemma Zulp_ge0 m : (0 <= Zulp m)%Z.
Proof. case: m => [//|p|p]; apply Z.lt_le_incl; exact: Zulp_gt0. Qed.

Lemma Zulp_mul m : (m / Zulp m * Zulp m)%Z = m.
case: m => [|p|p] //.
{ elim: p => [p IHp|p IHp|] //.
  { by rewrite /= Pos_ldiff_eq0 /= Zdiv_1_r Zmult_1_r. }
  rewrite /=.
  case E : (Pos.pred_double p) => [q|q|] /=.
  have->: p = Pos.succ q.
  { rewrite Pos.pred_double_spec in E.
    move/(congr1 Pos.succ) in E.
    rewrite Pos.succ_pred // in E.
    by case: E. }
  { clear E.
    symmetry; rewrite Zmult_comm; apply Znumtheory.Zdivide_Zdiv_eq.
    by rewrite -[Z0]/(Z.of_N N0); apply N2Z.inj_lt;
      case: Pos.ldiff (@Pos_ldiff_neq0 q).
    apply Z.mod_divide.
    by apply/BigNumPrelude.Zlt0_not_eq;
      rewrite -[Z0]/(Z.of_N N0); apply N2Z.inj_lt;
      case: Pos.ldiff (@Pos_ldiff_neq0 q).
    now_show (Z.of_N (N.double (N.pos (Pos.succ q)))
      mod Z.of_N (N.double (Pos.ldiff (Pos.succ q) q)) = Z0)%Z.
    rewrite -N2Z.inj_mod; last first.
    rewrite N.double_spec.
    apply/N.neq_mul_0; split =>//; exact: Pos_ldiff_neq0.
    rewrite !N.double_spec !N.mul_mod_distr_l; [|exact: Pos_ldiff_neq0|done].
    by rewrite Pos_ldiff_mod. }
  { exfalso; clear IHp.
    move: E; by case: p. }
  clear E.
  symmetry; rewrite Zmult_comm; apply Znumtheory.Zdivide_Zdiv_eq =>//.
  exact: Z.divide_refl. }
(* almost same proof *)
elim: p => [p IHp|p IHp|] //.
{ by rewrite /= Pos_ldiff_eq0 /= Zdiv_1_r Zmult_1_r. }
rewrite /=.
case E : (Pos.pred_double p) => [q|q|] /=.
have->: p = Pos.succ q.
{ rewrite Pos.pred_double_spec in E.
  move/(congr1 Pos.succ) in E.
  rewrite Pos.succ_pred // in E.
  by case: E. }
{ clear E.
  symmetry; rewrite Zmult_comm; apply Znumtheory.Zdivide_Zdiv_eq.
  by rewrite -[Z0]/(Z.of_N N0); apply N2Z.inj_lt;
    case: Pos.ldiff (@Pos_ldiff_neq0 q).
  apply Z.mod_divide.
  by apply/BigNumPrelude.Zlt0_not_eq;
    rewrite -[Z0]/(Z.of_N N0); apply N2Z.inj_lt;
    case: Pos.ldiff (@Pos_ldiff_neq0 q).
  now_show (- Z.of_N (N.double (N.pos (Pos.succ q)))
    mod Z.of_N (N.double (Pos.ldiff (Pos.succ q) q)) = Z0)%Z.
  (*:*) apply Z_mod_zero_opp_full.
  rewrite -N2Z.inj_mod; last first.
  rewrite N.double_spec.
  apply/N.neq_mul_0; split =>//; exact: Pos_ldiff_neq0.
  rewrite !N.double_spec !N.mul_mod_distr_l; [|exact: Pos_ldiff_neq0|done].
  by rewrite Pos_ldiff_mod. }
{ exfalso; clear IHp.
  move: E; by case: p. }
clear E.
symmetry; rewrite Zmult_comm; apply Znumtheory.Zdivide_Zdiv_eq =>//.
(*:*) now_show (Z.pos p~0 | - Z.pos p~0)%Z; apply Znumtheory.Zdivide_opp_r.
exact: Z.divide_refl.
Qed.

Lemma Zulp_divides m : Z.divide (Zulp m) m.
Proof.
apply Znumtheory.Zdivide_intro with (m / Zulp m)%Z.
by rewrite Zulp_mul.
Qed.

Lemma Zulp_le m : (Zulp m <= Z.abs m)%Z.
Proof.
have := Zulp_divides m.
case: m => [//|p|p].
by apply: Znumtheory.Zdivide_le; first exact: Zulp_ge0.
move/Znumtheory.Zdivide_opp_r.
by apply: Znumtheory.Zdivide_le; first exact: Zulp_ge0.
Qed.

Lemma Zulp_double n : n <> Z0 -> Zulp (Z.double n) = (Z.double (Zulp n))%Z.
Proof.
case: n => [//|p|p].
{ elim: p => [p IHp|p IHp|//] _ /=; first by rewrite /= Pos_ldiff_eq0.
  case E : (Pos.pred_double p) => [q|q|//].
  have->: p = Pos.succ q.
  { rewrite Pos.pred_double_spec in E.
    move/(congr1 Pos.succ) in E.
    rewrite Pos.succ_pred // in E.
    by case: E. }
  by rewrite Z.double_spec -[2%Z]/(Z.of_N 2) -N2Z.inj_mul.
  by rewrite Z.double_spec -[2%Z]/(Z.of_N 2) -N2Z.inj_mul. }
(* same proof *)
elim: p => [p IHp|p IHp|//] _ /=; first by rewrite /= Pos_ldiff_eq0.
case E : (Pos.pred_double p) => [q|q|//].
have->: p = Pos.succ q.
{ rewrite Pos.pred_double_spec in E.
  move/(congr1 Pos.succ) in E.
  rewrite Pos.succ_pred // in E.
  by case: E. }
by rewrite Z.double_spec -[2%Z]/(Z.of_N 2) -N2Z.inj_mul.
by rewrite Z.double_spec -[2%Z]/(Z.of_N 2) -N2Z.inj_mul.
Qed.

Lemma Zulp_digits m : m <> Z0 -> (2 ^ (Zdigits2 (Zulp m) - 1))%Z = Zulp m.
Proof.
move=> NZm.
case: m NZm => [//|p|p] _.
{ elim: p => [p IHp|p IHp|//].
  by rewrite /= Pos_ldiff_eq0 /=.
  have->: Z.pos p~0 = Z.double (Z.pos p) by [].
  rewrite Zulp_double // -[in RHS]IHp Zdigits2_double; last exact: Zulp_neq0.
  have->: (Z.succ ?[n] - 1 = Z.succ (?n - 1))%Z by intros; ring.
  rewrite Z.pow_succ_r //.
  apply(*:*) Z.lt_le_pred.
  apply: Zdigits_gt_0.
  exact: Zulp_neq0. }
(* almost same proof *)
{ elim: p => [p IHp|p IHp|//].
  by rewrite /= Pos_ldiff_eq0 /=.
  have->: Z.neg p~0 = Z.double (Z.neg p) by [].
  rewrite Zulp_double // -[in RHS]IHp Zdigits2_double; last exact: Zulp_neq0.
  have->: (Z.succ ?[n] - 1 = Z.succ (?n - 1))%Z by intros; ring.
  rewrite Z.pow_succ_r //.
  apply(*:*) Z.lt_le_pred.
  apply: Zdigits_gt_0.
  exact: Zulp_neq0. }
Qed.

Lemma Zdigits_div_ulp m :
  m <> Z0 -> Zdigits2 (m / Zulp m) = Z.succ (Zdigits2 m - Zdigits2 (Zulp m)).
Proof.
move=> NZm.
rewrite -{3}(Zulp_mul m).
rewrite -{3}(Zulp_digits _ NZm).
rewrite Zdigits2_mult_Zpower; first ring.
{ apply/Z.div_small_iff; first exact: Zulp_neq0.
  move=> [[K1 K2]|[K1 K2]].
  { have Absm : (Z.abs m < Zulp m)%Z by rewrite Z.abs_eq.
    by have /Zlt_not_le Absm' := @Zulp_le m. }
  have /Zlt_not_le K := Z.lt_le_trans _ _ _ K1 K2.
  by have K' := @Zulp_ge0 m. }
{ apply(*:*) Z.lt_le_pred.
  apply: Zdigits_gt_0.
  exact: Zulp_neq0. }
Qed.

Lemma Zdigits2_Zulp_le m p :
  (Z.succ (Zdigits2 m - Zdigits2 (Zulp m)) <= p -> Zdigits2 (m / Zulp m) <= p)%Z.
Proof.
have [->|NZm] := Z_zerop m.
{ by simpl; auto with zarith. }
by rewrite Zdigits_div_ulp.
Qed.

Lemma Zulp_mod2 m : m <> Z0 ->
  ((m / Zulp m) mod 2 = 1)%Z.
Proof.
move=> NZm.
rewrite -(Zulp_digits _ NZm).
apply/Z.testbit_true.
{ apply(*:*) Z.lt_le_pred.
  apply: Zdigits_gt_0.
  exact: Zulp_neq0. }
case: m NZm => [//|p|p] _.
{ elim: p => [p IHp|p IHp|] //; first by rewrite /= Pos_ldiff_eq0.
  rewrite -[Z.pos p~0]/(Z.double (Z.pos p)).
  rewrite Zulp_double //.
  have->: Z.double (Zulp (Z.pos p)) = (Zulp (Z.pos p) * 2 ^ 1)%Z
    by rewrite Z.double_spec Zmult_comm.
  rewrite Zdigits2_mult_Zpower //; last exact: Zulp_neq0.
  have->: (?[a] + 1 - 1 = Z.succ (?a - 1))%Z by move=> ?; rewrite /Z.succ; ring.
  rewrite Z.double_spec Z.testbit_even_succ //.
  { apply(*:*) Z.lt_le_pred.
    apply: Zdigits_gt_0.
    exact: Zulp_neq0. } }
(* almost same proof *)
{ elim: p => [p IHp|p IHp|] //; first by rewrite /= Pos_ldiff_eq0.
  rewrite -[Z.neg p~0]/(Z.double (Z.neg p)).
  rewrite Zulp_double //.
  have->: Z.double (Zulp (Z.pos p)) = (Zulp (Z.pos p) * 2 ^ 1)%Z
    by rewrite Z.double_spec Zmult_comm.
  rewrite Zdigits2_mult_Zpower //; last exact: Zulp_neq0.
  have->: (?[a] + 1 - 1 = Z.succ (?a - 1))%Z by move=> ?; rewrite /Z.succ; ring.
  rewrite Z.double_spec Z.testbit_even_succ //.
  { apply(*:*) Z.lt_le_pred.
    apply: Zdigits_gt_0.
    exact: Zulp_neq0. } }
Qed.

Lemma Zulp_rel_prime m e :
  m <> Z0 -> (0 <= e)%Z -> Znumtheory.rel_prime (Z.abs (m / Zulp m)) (2 ^ e).
Proof.
move=> NZm NNe.
apply Zpow_facts.rel_prime_Zpower_r =>//.
apply Znumtheory.rel_prime_sym.
apply Znumtheory.prime_rel_prime; first exact: Znumtheory.prime_2.
move/Z.divide_abs_r/Znumtheory.Zdivide_mod.
by rewrite Zulp_mod2.
Qed.

(** Number of significant radix2 digits of a [bigZ] number *)

Definition signif_digits (m : bigZ) :=
  let d := digits m in
  let d' := digits (bigZulp m) in
  BigZ.succ (d - d').

Lemma signif_digits_correct m e :
  (signif_digits m <=? 53)%bigZ <=>
  mantissa_bounded (Interval_specific_ops.Float m e).
Proof.
split => H.
{ rewrite /mantissa_bounded /x_bounded; right.
  exists (toR (Float m e)); first by rewrite -real_FtoX_toR.
  red; rewrite /signif_digits in H.
  exists (Fcore_defs.Float radix2
                      [m / bigZulp m]%bigZ
                      [digits (bigZulp m) - 1 + e]%bigZ).
  split.
  { rewrite /F.toX /F.toF.
    case: Bir.mantissa_sign (Bir.mantissa_sign_correct m) =>[/=|s n].
    { rewrite /F2R /= BigZ.spec_div.
      by rewrite /Bir.MtoZ =>->; rewrite Zdiv_0_l Rsimpl. }
    case=> Hm Vn; rewrite /= FtoR_split.
    case: s Hm => Hm; rewrite /= -Hm /F2R /= /Bir.MtoZ /Bir.EtoZ.
    { rewrite BigZ.spec_add bpow_plus /= -Rmult_assoc; congr Rmult.
      rewrite -Z2R_Zpower; last first.
      { rewrite BigZ.spec_sub digits_spec.
        apply(*:*) Z.lt_le_pred.
        apply: Zdigits_gt_0.
        rewrite /bigZulp BigZ.spec_land BigZ.spec_opp -/(Zulp [m]%bigZ).
        apply: Zulp_neq0.
        by move: Hm; rewrite /Bir.MtoZ =>->. }
      rewrite BigZ.spec_sub digits_spec.
      rewrite -Z2R_mult; congr Z2R.
      rewrite BigZ.spec_div BigZ.spec_land BigZ.spec_opp.
      rewrite -/(Zulp [m]%bigZ) /= Zulp_digits;
        last by move=> K; rewrite /Bir.MtoZ K in Hm.
      by rewrite Zulp_mul. }
    rewrite BigZ.spec_add bpow_plus /= -Rmult_assoc; congr Rmult.
    rewrite -Z2R_Zpower; last first.
    { rewrite BigZ.spec_sub digits_spec.
      apply(*:*) Z.lt_le_pred.
      apply: Zdigits_gt_0.
      rewrite /bigZulp BigZ.spec_land BigZ.spec_opp -/(Zulp [m]%bigZ).
      apply: Zulp_neq0.
      by move: Hm; rewrite /Bir.MtoZ =>->. }
    rewrite BigZ.spec_sub digits_spec.
    rewrite -Z2R_mult; congr Z2R.
    rewrite BigZ.spec_div BigZ.spec_land BigZ.spec_opp.
    rewrite -/(Zulp [m]%bigZ) /= Zulp_digits;
      last by move=> K; rewrite /Bir.MtoZ K in Hm.
    by rewrite Zulp_mul. }
  (* could be extracted to some lemma *)
  have [_ H1] := Zdigits_correct radix2 [m / bigZulp m]%bigZ.
  have H2 := @Zdigits2_Zulp_le [m]%bigZ 53.
  rewrite BigZ.spec_leb BigZ.spec_succ BigZ.spec_sub in H.
  rewrite !digits_spec bigZulp_spec in H.
  move/Z.leb_le in H.
  move/(_ H) in H2.
  rewrite !BigZ.spec_div !bigZulp_spec in H1 *.
  apply (Z.lt_le_trans _ _ _ H1); exact: Zpower_le. }
have {H} [|[r H1 [f [Hf1 Hf2]]]] := H; first by rewrite real_FtoX_toR.
rewrite /signif_digits.
set f1 := Fnum f in Hf2.
rewrite Hf1 in H1.
rewrite /F.toX /= in H1.
case E: Bir.mantissa_sign H1 (Bir.mantissa_sign_correct m) => [|s p] H1 Hm.
{ rewrite /Bir.MtoZ in Hm.
  rewrite BigZ.spec_leb BigZ.spec_succ BigZ.spec_sub !digits_spec bigZulp_spec.
  by rewrite Hm. }
rewrite /Bir.MtoZ in Hm.
rewrite BigZ.spec_leb BigZ.spec_succ BigZ.spec_sub !digits_spec bigZulp_spec.
case: Hm => Hm Hp.
have [Hlt|Hle] := Z_lt_le_dec (Z.abs f1) (Z.abs [m]%bigZ); last first.
{ move/(Zdigits_le radix2 _ _ (Z.abs_nonneg _)) in Hle.
  rewrite Zdigits_abs in Hle.
  move/(Zdigits_le_Zpower radix2) in Hf2.
  apply/Z.leb_le.
  have NZm : [m]%bigZ <> 0%Z by rewrite Hm; case: (s).
  have NZum : Zulp [m]%bigZ <> 0%Z by apply: Zulp_neq0.
  have H0 := Zdigits_gt_0 radix2 _ NZum.
  change [53]%bigZ with 53%Z; rewrite /Zdigits2 in H0 *.
  rewrite Zdigits_abs in Hle.
  clear - Hle Hf2 H0; romega. }
have NZf1 : f1 <> Z0.
{ move=> K; rewrite /F2R -/f1 K /= Rsimpl in H1.
  case: H1; rewrite FtoR_split /F2R /=.
  case/Rmult_integral.
  { change R0 with (Z2R 0); apply: Z2R_neq; by case: (s). }
  by apply: Rgt_not_eq; apply: bpow_gt_0. }
move/(Zdigits_le_Zpower radix2) in Hf2.
apply/Z.leb_le.
rewrite -/(Z.succ _) -Zdigits_div_ulp; last by rewrite Hm; case: (s).
apply: Z.le_trans _ Hf2.
rewrite /Zdigits2 -Zdigits_abs -(Zdigits_abs _ f1).
apply Zdigits_le; first exact: Z.abs_nonneg.
apply Znumtheory.Zdivide_bounds =>//.
apply Z.divide_abs_l.
have Hmf : (Z2R [m]%bigZ * bpow radix2 [e]%bigZ = F2R f)%Re.
{ rewrite Hm; apply Xreal_inj; rewrite -{}H1; congr Xreal.
  rewrite FtoR_split /F2R /=.
  by case: (s). }
have Hlte : bpow radix2 [e]%bigZ < bpow radix2 (Fexp f).
{ rewrite /F2R in Hmf.
  move/Z2R_lt in Hlt.
  rewrite !Z2R_abs in Hlt.
  rewrite -/f1 in Hmf.
  move/(congr1 (Rdiv ^~ (bpow radix2 [e]%bigZ))) in Hmf.
  rewrite /Rdiv Rinv_r_simpl_l in Hmf; last exact/Rgt_not_eq/bpow_gt_0.
  rewrite {}Hmf in Hlt.
  rewrite !Rabs_mult in Hlt.
  apply/Rdiv_gt_1; first exact: bpow_gt_0.
  move/Rdiv_gt_1: Hlt.
  rewrite (_ : ?[a] * Rabs ?[b] * Rabs ?[c] / ?a = ?b * ?c); last first.
    rewrite (Rabs_pos_eq (bpow _ _)); last exact: bpow_ge_0.
    rewrite (Rabs_pos_eq (/ bpow _ _));
      last exact/Rlt_le/Rinv_0_lt_compat/bpow_gt_0.
    field.
    split; last by apply/Rabs_no_R0; change R0 with (Z2R Z0); exact: Z2R_neq.
    exact/Rgt_not_eq/bpow_gt_0.
  apply.
  by apply/Rabs_pos_lt; change R0 with (Z2R Z0); exact: Z2R_neq. }
move/lt_bpow in Hlte.
have {Hmf} Hmf : ([m]%bigZ = f1 * 2 ^ (Fexp f - [e]%bigZ))%Z.
{ clear - Hlte Hmf.
  rewrite /F2R - /f1 in Hmf.
  move/(congr1 (Rmult ^~ (bpow radix2 (- [e]%bigZ)))) in Hmf.
  rewrite !Rmult_assoc -!bpow_plus Zegal_left //= Rmult_1_r in Hmf.
  rewrite -Z2R_Zpower in Hmf; last romega.
  rewrite -Z2R_mult in Hmf.
  exact: eq_Z2R. }
have Hdiv : (Z.abs ([m]%bigZ / Zulp [m]%bigZ) | [m]%bigZ)%Z.
{ apply/Z.divide_abs_l.
  apply Zdivide_div_l.
  by apply Zulp_divides. }
rewrite {3}Hmf Z.mul_comm in Hdiv.
apply (Znumtheory.Gauss _ (2 ^ (Fexp f - [e]%bigZ))) =>//.
apply: Zulp_rel_prime; last romega.
by rewrite Hm; case: (s).
Qed.
