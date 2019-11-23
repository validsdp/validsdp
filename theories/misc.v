(** * Miscellaneous lemmas. *)

Require Import Reals QArith.
From Bignums Require Import BigQ.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import ssralg ssrnum ssrint rat.

From CoqEAL.refinements Require Import binrat.
Require Import libValidSDP.Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Open Scope R_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.
Delimit Scope Q_scope with Qrat.

(** ** Lemmas about [BigQ] and [R] *)
Definition Q2R (x : Q) : R :=
  (IZR (Qnum x) / IZR (Z.pos (Qden x)))%Re.

Definition bigQ2R (x : BigQ.t_ (* the type of (_ # _)%bigQ *)) : R :=
  Q2R [x]%bigQ.

Ltac pos_IPR :=
  by rewrite /= -INR_IPR; apply not_0_INR, not_eq_sym, lt_0_neq, Pos2Nat.is_pos.

Lemma Q2R_0 : Q2R 0%Qrat = 0%Re.
Proof. by rewrite /Q2R /= /Rdiv Rmult_0_l. Qed.

Lemma Q2R_inv x : Q2R x <> 0%Re -> Q2R (/ x) = / (Q2R x).
Proof.
move: x => [[ |a|a] b] Hx; rewrite /Q2R /Qinv /=.
{ by rewrite /Q2R /= /Rdiv Rmult_0_l in Hx. }
{ clear Hx; rewrite Rinv_Rdiv //. }
{ clear Hx; rewrite /Rdiv !Ropp_mult_distr_l_reverse -Ropp_inv_permute.
  rewrite Rinv_Rdiv //; pos_IPR.
  by apply Rmult_integral_contrapositive_currified;
    [pos_IPR|apply Rinv_neq_0_compat]. }
Qed.

Lemma Q2R_mult x y : Q2R (x * y) = (Q2R x * Q2R y)%Re.
Proof.
  rewrite /Q2R /= !(mult_IZR, Pos2Z.inj_mul) /Rdiv Rinv_mult_distr //; ring.
Qed.

Lemma Q2R_opp x : Q2R (- x) = (- Q2R x)%Re.
Proof. by rewrite /Q2R /= opp_IZR -Ropp_mult_distr_l_reverse. Qed.

Lemma Q2R_Qeq x y :
  Qeq x y -> Q2R x = Q2R y.
Proof.
move=> Hxy; rewrite /Q2R.
rewrite /Qeq in Hxy.
move/(congr1 IZR) in Hxy.
rewrite !mult_IZR in Hxy.
apply (Rmult_eq_reg_r (IZR (Z.pos (Qden y)))); last by simpl.
by rewrite /Rdiv Rmult_assoc [(/ _ * _)%Re]Rmult_comm -Rmult_assoc Hxy; field.
Qed.

Lemma Qeq_Q2R x y :
  Q2R x = Q2R y -> Qeq x y.
Proof.
move=> Hxy; rewrite /Qeq.
rewrite /Q2R in Hxy.
apply: eq_IZR.
rewrite !mult_IZR.
apply (Rmult_eq_reg_r (/ IZR (Z.pos (Qden x)))); last first.
{ apply: Rinv_neq_0_compat.
  by change 0%Re with (IZR 0); apply: IZR_neq. }
rewrite /Rdiv in Hxy.
by rewrite Rmult_assoc [(_ * / _)%Re]Rmult_comm -Rmult_assoc Hxy; field.
Qed.

(** ** Lemmas about [BigQ.check_int], [BigQ.norm] and [BigQ.red] *)

Local Open Scope Z_scope.

Lemma BigQ_check_int_den_neq0_aux n d :
  match BigQ.check_int n d with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof.
rewrite /BigQ.check_int.
case E: (_ ?= _)%bigN=>//.
move: E; rewrite BigN.compare_lt_iff=> E H.
apply (BigN.lt_irrefl BigN.one).
apply (BigN.lt_trans _ BigN.zero); [ |apply BigN.lt_0_1].
by move: E; rewrite -BigN.ltb_lt BigN.spec_ltb H /=.
Qed.

Lemma BigQ_check_int_den_neq0 n d :
  match BigQ.check_int n d with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof.
move: (BigQ_check_int_den_neq0_aux n d); case (BigQ.check_int _ _)=>[//|_ n' H].
by apply/negP; rewrite /is_true BigN.spec_eqb Z.eqb_eq=>H'; apply H; rewrite H'.
Qed.

Lemma BigQ_norm_den_neq0_aux n d :
  match BigQ.norm n d with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof.
case E: (BigQ.norm _ _)=>//; move: E; rewrite /BigQ.norm.
case (_ ?= _)%bigN.
{ move: (BigQ_check_int_den_neq0_aux n d).
  by case (BigQ.check_int _ _)=>[//| n' d'] H [] _ <-. }
{ set n' := (_ / _)%bigZ; set d' := (_ / _)%bigN.
  move: (BigQ_check_int_den_neq0_aux n' d').
  by case (BigQ.check_int _ _)=>[//| n'' d''] H [] _ <-. }
by [].
Qed.

Lemma BigQ_norm_den_neq0 n d :
  match BigQ.norm n d with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof.
move: (BigQ_norm_den_neq0_aux n d); case (BigQ.norm _ _)=>[//|_ n' H].
by apply/negP; rewrite /is_true BigN.spec_eqb Z.eqb_eq=>H'; apply H; rewrite H'.
Qed.

Lemma BigQ_red_den_neq0_aux q :
  match BigQ.red q with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof. by rewrite /BigQ.red; case q=>// n d; apply BigQ_norm_den_neq0_aux. Qed.

Lemma BigQ_red_den_neq0 q :
  match BigQ.red q with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof. by rewrite /BigQ.red; case q=>// n d; apply BigQ_norm_den_neq0. Qed.

(** ** Lemmas about [int], [rat] and [R] *)

Lemma Z2R_int2Z_nat (n : nat) : IZR (int2Z n) = n%:~R.
Proof.
elim: n => [//|n IHn].
rewrite -addn1 PoszD intrD -{}IHn /= addn1.
set zn := match n with O => Z0 | _ => Z.pos (Pos.of_nat n) end.
suff->: zn = Z.of_nat n.
{ change 1%N%:~R with (IZR 1).
  rewrite /GRing.add /= -plus_IZR Z.add_1_r -Nat2Z.inj_succ.
  by rewrite /Z.of_nat Pos.of_nat_succ. }
clear; rewrite {}/zn /Z.of_nat.
case: n => // n.
by rewrite Pos.of_nat_succ.
Qed.

Lemma Z2R_int2Z n : IZR (int2Z n) = n%:~R.
Proof.
elim/int_rec: n =>// n IHn.
{ exact: Z2R_int2Z_nat. }
by clear IHn; rewrite mulrNz /= -Z2R_int2Z_nat.
Qed.

Lemma int2Z_le m n : int2Z m <=? int2Z n = (m <= n)%Ri.
Proof.
rewrite -(ler_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.leb_le/IZR_le/RleP. }
by move/RleP/le_IZR/Z.leb_le.
Qed.

Lemma int2Z_lt m n : int2Z m <? int2Z n = (m < n)%Ri.
Proof.
rewrite -(ltr_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.ltb_lt/IZR_lt/RltP. }
by move/RltP/lt_IZR/Z.ltb_lt.
Qed.

Lemma bigQ2R_redE (c : bigQ) : bigQ2R (BigQ.red c) = bigQ2R c.
Proof.
case: c => [//|n d].
by rewrite /bigQ2R; apply: Q2R_Qeq; apply: BigQ.spec_red.
Qed.

Notation rat2R := (@ratr real_unitRingType) (only parsing).

Lemma bigQ2R_rat (c : bigQ) : bigQ2R c = rat2R (bigQ2rat c).
Proof.
rewrite -[LHS]bigQ2R_redE /bigQ2R BigQ.strong_spec_red.
rewrite /bigQ2rat /ratr; set r := Rat _.
rewrite /GRing.inv /= /invr ifF /GRing.mul /= /Rdiv.
{ rewrite /numq /denq /=; congr Rmult.
  { rewrite /IZR /Z2int; case: Qnum =>[//|p|p].
      by rewrite -INR_IPR binnat.to_natE INR_natmul.
    rewrite -INR_IPR binnat.to_natE INR_natmul /=.
    now rewrite -> mulrNz. }
  by rewrite /IZR /= -INR_IPR binnat.to_natE INR_natmul. }
rewrite -(denq_eq0 (r)).
have->: 0%Re = O%:~R by [].
exact/inj_eq/intr_inj.
Qed.

Import Num.Theory.

Lemma ratr_inj (R : numFieldType) : injective (@ratr R).
Proof. by move=> x y H; apply ler_asym; rewrite -!(ler_rat R) H lerr. Qed.
