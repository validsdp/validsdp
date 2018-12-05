(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Rpow_def.
Require Import Epsilon FunctionalExtensionality.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.choice mathcomp.ssreflect.bigop mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.ssrnum.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

(** * Instantiation of the mathcomp algebraic hierarchy with the Reals stdlib *)

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure real_eqMixin := EqMixin eqrP.
Canonical Structure real_eqType := Eval hnf in EqType R real_eqMixin.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%N. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

Definition R_choiceMixin : choiceMixin R :=
  Choice.Mixin pickR_some pickR_ex pickR_ext.

Canonical R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Definition real_zmodMixin := ZmodMixin RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Canonical Structure real_zmodType := Eval hnf in ZmodType R real_zmodMixin.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

Definition real_ringMixin := RingMixin RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

Canonical Structure real_ringType := Eval hnf in RingType R real_ringMixin.
Canonical Structure real_comRingType := Eval hnf in ComRingType R Rmult_comm.

Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Definition invr (x : R) := if x == 0 then 0 else / x.

Fact mulVr (x : R) : x != 0 -> (invr x) * x = 1.
Proof.
move=> H; rewrite /invr ifF; first by move/eqP: H; exact: Rinv_l.
exact: negbTE.
Qed.

Fact invr0 : invr 0 = 0.
Proof. by rewrite /invr eqxx. Qed.

Definition real_fieldUnitMixin := FieldUnitMixin mulVr invr0.

Canonical real_unitRingType :=
  Eval hnf in UnitRingType R real_fieldUnitMixin.
Canonical real_comUnitRingType := Eval hnf in [comUnitRingType of R].

Fact real_field_axiom : GRing.Field.mixin_of real_unitRingType.
Proof. exact. Qed.

Definition real_FieldIdomainMixin := (FieldIdomainMixin real_field_axiom).
Canonical real_iDomainType :=
  Eval hnf in IdomainType R (FieldIdomainMixin real_field_axiom).
Canonical real_fieldType := FieldType R real_field_axiom.

Definition Rleb (x y : R) := match total_order_T x y with
                            | inleft _ => true
                            | inright _ => false
                            end.

Definition Rltb (x y : R) := match total_order_T x y with
                            | inleft (left _) => true
                            | _ => false
                            end.

Lemma RleP (x y : R) : reflect (Rle x y) (Rleb x y).
Proof.
apply: (iffP idP); rewrite /Rleb; case: total_order_T =>//; first by intuition.
by move/Rgt_not_le.
Qed.

Lemma RltP (x y : R) : reflect (Rlt x y) (Rltb x y).
Proof.
apply: (iffP idP); rewrite /Rltb; case: total_order_T =>//.
{ by case. }
{ by case =>// ->; move/Rlt_irrefl. }
by move/Rgt_lt=> Hyx Hxy; exfalso; apply: (Rlt_irrefl x); apply: Rlt_trans Hxy _.
Qed.

Fact Rleb0D x y : Rleb 0 x -> Rleb 0 y -> Rleb 0 (x + y).
Proof.
move/RleP => Hx /RleP Hy; apply/RleP.
exact: Rplus_le_le_0_compat.
Qed.

Fact Rleb0M x y : Rleb 0 x -> Rleb 0 y -> Rleb 0 (x * y).
Proof.
move/RleP => Hx /RleP Hy; apply/RleP.
exact: Rmult_le_pos.
Qed.

Fact Rleb0_anti x : Rleb 0 x -> Rleb x 0 -> x = 0.
Proof. move/RleP => _x /RleP x_; exact: Rle_antisym. Qed.

Fact subq_ge0 x y : Rleb 0 (y - x) = Rleb x y.
Proof.
apply/RleP/RleP.
{ move=> H0; apply: Rminus_le.
  move/Ropp_0_le_ge_contravar/Rge_le in H0.
  by rewrite Ropp_minus_distr in H0. }
{ move=> Hxy.
  have->: y - x = - (x - y) by rewrite Ropp_minus_distr.
  exact/Ropp_0_ge_le_contravar/Rle_ge/Rle_minus. }
Qed.

Fact Rleb_total : total Rleb.
Proof.
move=> x y; rewrite /Rleb; case: (total_order_T x y) =>//.
case: (total_order_T y x) =>// Hyx Hxy; exfalso; apply: (Rlt_irrefl x).
by apply: (@Rlt_trans _ y); apply Rlt_gt.
Qed.

Notation normr := Rabs (only parsing).

Fact ger0_norm x : Rleb 0 x -> normr x = x.
Proof. move/RleP => Hx; exact: Rabs_pos_eq. Qed.

Fact Rltb_def x y : (Rltb x y) = (y != x) && (Rleb x y).
Proof.
rewrite /Rltb /Rleb; case: total_order_T.
{ case =>//=; first by move/Rgt_not_eq/eqP =>->.
  by move->; rewrite eqxx. }
by rewrite andbF.
Qed.

Definition real_LeMixin := RealLeMixin Rleb0D Rleb0M Rleb0_anti
  subq_ge0 (@Rleb_total 0) Rabs_Ropp ger0_norm Rltb_def.

Canonical real_numDomainType := NumDomainType R real_LeMixin.
Canonical real_numFieldType := [numFieldType of R].
Canonical real_realDomainType := RealDomainType R (@Rleb_total 0).
Canonical real_realFieldType := [realFieldType of R].

Section UnfoldR.

Let RaddE a b : Rplus a b = GRing.add a b.
Proof. by []. Qed.

Let RoppE a : Ropp a = (- a)%R.
Proof. by []. Qed.

Let RminusE a b : Rminus a b = (a - b)%R.
Proof. by []. Qed.

Let RmultE a b : Rmult a b = GRing.mul a b.
Proof. by []. Qed.

Let powE a n : pow a n = (a ^+ n)%R.
Proof. by elim: n => [//|n IHn] /=; rewrite IHn exprS. Qed.

Let RinvE a : a <> R0 -> Rinv a = (a ^-1)%R.
Proof. by move=> /eqP H0; rewrite /GRing.inv /= /invr ifF // (negbTE H0). Qed.

Let RdivE a b : b <> R0 -> Rdiv a b = (a / b)%R.
Proof. by move=> /eqP H0; rewrite /Rdiv RinvE //; exact/eqP. Qed.

Lemma RlebE a b : Rleb a b = (a <= b)%R.
Proof. by []. Qed.

Lemma RltbE a b : Rltb a b = (a < b)%R.
Proof. by []. Qed.

Let R0E : R0 = 0%R.
Proof. by []. Qed.

Let R1E : R1 = 1%R.
Proof. by []. Qed.

Lemma RabsE a : Rabs a = `|a|%R.
Proof. by []. Qed.

Lemma INR_natmul n : INR n = (n%:R)%R.
Proof.
elim: n => [//|n IHn].
by rewrite -addn1 plus_INR IHn mulrnDr.
Qed.

Definition unfoldR :=
  (RminusE, RoppE, RaddE, RmultE, powE, R0E, R1E,
   INR_natmul, RlebE, RltbE, RabsE).

Definition unfoldR' :=
  (RminusE, RdivE, RoppE, RinvE, RaddE, RmultE, powE, R0E, R1E,
   INR_natmul, RlebE, RltbE, RabsE).

End UnfoldR.
