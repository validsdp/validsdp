Require Import Reals.
Require Import ZArith.
From Bignums Require Import BigQ.
From Flocq Require Import Core.Defs.
From Flocq Require Import Core.Digits.
From Interval Require Import Interval_definitions.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(** * Number of radix2 digits of a [Z] number *)

Definition Zdigits2 (n : BinNums.Z) := Zdigits radix2 n.

Lemma Zdigits2_mult_Zpower m e : m <> Z0 -> (0 <= e)%Z ->
  Zdigits2 (m * 2 ^ e) = (Zdigits2 m + e)%Z.
Proof. exact: Zdigits_mult_Zpower. Qed.

Lemma Zdigits2_double m : m <> Z0 -> Zdigits2 (Z.double m) = (Z.succ (Zdigits2 m))%Z.
Proof.
move=> NZm.
suff->: Z.double m = (m * 2 ^ 1)%Z by apply: Zdigits2_mult_Zpower.
by rewrite Z.double_spec Zmult_comm.
Qed.

Lemma Zdigits_opp r (n : BinNums.Z) : Zdigits r (- n) = Zdigits r n.
Proof. by case: n. Qed.

(** * Definition of ulp (unit in the last place) for signed integers *)

Definition Zulp (m : BinNums.Z) : BinNums.Z := Z.land m (- m).

Definition bigZulp (m : bigZ) : bigZ := BigZ.land m (- m).

Lemma bigZulp_spec m : [bigZulp m]%bigZ = Zulp [m]%bigZ.
Proof. by rewrite BigZ.spec_land BigZ.spec_opp. Qed.

(** ** Preliminary results *)

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

Lemma Rabs_div_gt_1 a b : a <> R0 -> (Rabs a < b <-> 1 < b / Rabs a)%Re.
Proof.
move=> H0; split => Hab.
{ rewrite -[1%Re](Rinv_r_simpl_l (Rabs a)); last exact: Rabs_no_R0.
  rewrite Rmult_1_l /Rdiv.
  apply: Rmult_lt_compat_r =>//.
  apply/Rinv_0_lt_compat.
  exact: Rabs_pos_lt. }
{ apply (Rmult_lt_reg_r (/ Rabs a)).
  exact/Rinv_0_lt_compat/Rabs_pos_lt.
  rewrite (Rinv_r (Rabs a)) //.
  exact: Rabs_no_R0. }
Qed.

Lemma Rdiv_gt_1 a b : (0 < a)%Re -> (a < b <-> 1 < b / a)%Re.
Proof.
move=> H0.
rewrite -(Rabs_pos_eq _ (Rlt_le _ _ H0)).
apply: Rabs_div_gt_1 =>//.
exact: Rgt_not_eq.
Qed.

(** ** Support results on [Zulp] *)

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
    (* BinInt *)
    by rewrite -E N.pos_pred_spec N2Z.inj_pred // -/(Z.succ _) -Zsucc_pred. }
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
    by rewrite -E N.pos_pred_spec N2Z.inj_pred // -/(Z.succ _) -Zsucc_pred. }
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
rewrite -{3}(Zulp_digits NZm).
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
rewrite -(Zulp_digits NZm).
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
