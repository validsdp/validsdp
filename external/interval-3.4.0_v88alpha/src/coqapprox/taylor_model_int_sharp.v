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

Require Import ZArith Psatz Reals.
From Flocq Require Import Raux.
Require Import Coquelicot.Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import Interval_xreal.
Require Import Interval_interval.
Require Import Interval_definitions.
Require Import Interval_xreal_derive.
Require Import Interval_missing.
Require Import Rstruct.
Require Import xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import basic_rec.
Require Import poly_bound.
Require Import coquelicot_compl integral_pol.

(********************************************************************)
(** This theory implements Taylor models with interval polynomials for
    univariate real-valued functions. The implemented algorithms rely
    on the so-called Zumkeller's technique, which allows one to obtain
    sharp enclosures of the approximation error, when it detects that
    the Taylor-Lagrange remainder of the elementary function at stake
    is monotonic over the interval under study.
*)
(********************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

(** Rigorous Polynomial Approximation structure *)
Record rpa {pol int : Type} : Type := RPA { approx : pol ; error : int }.

Module TaylorModel (I : IntervalOps) (Pol : PolyIntOps I) (Bnd : PolyBound I Pol).
Import Pol.Notations.
Import PolR.Notations.
Local Open Scope ipoly_scope.
Module Export Aux := IntervalAux I.
Module Import TI := TaylorPoly Pol.Int Pol.
Module TR := TaylorPoly FullR PolR.
Module Import BndThm := PolyBoundThm I Pol Bnd.
Module J := IntervalExt I.

(* POSSIBLE UTF-8 NOTATION
Notation "X ∋ x" := (contains X x) (at level 70).
Notation "X ⊂ Y" := (I.subset_ X Y) (at level 70).
*)

Ltac step_xr xr :=
  match goal with
  [ |- contains ?i ?g ] => rewrite -(_ : xr = g)
  end.
Ltac step_r r :=
  match goal with
  [ |- contains ?i (Xreal ?g) ] => rewrite -(_ : r = g)
  end.
Ltac step_xi xi :=
  match goal with
  [ |- contains ?g ?xr ] => rewrite -(_ : xi = g)
  end.
Ltac step_i i :=
  match goal with
  [ |- contains (I.convert ?g) ?xr ] => rewrite -(_ : i = g)
  end.

(* Erik: Some lemmas could be generalized from [I.type] to [interval]. *)

Notation rpa := (@rpa Pol.T I.type).

Section PrecArgument.
(** For greater convenience, set the precision as a section variable.
    Note that this will not hinder any dynamic-change of the precision
    inside the functions that are defined or called below.
*)
Variable prec : I.precision.

Section TaylorModel.

Variable M : rpa.

Variable Tcoeffs : I.type -> nat -> Pol.T.
(** For complexity reasons, [Tcoeffs] must return more than one coefficient. *)

(** The generic functions [TLrem]/[Ztech] are intended to ease the
    computation of the interval remainder for basic functions.
*)
Definition TLrem (X0 X : I.type) n :=
  let N := S n in
  let NthCoeff := Pol.nth (Tcoeffs X N) N in
  let NthPower :=
    I.power_int prec (I.sub prec X X0) (Z_of_nat N) (* improvable *) in
  I.mul prec NthCoeff NthPower.

(** The first argument of [Ztech] will be instantiated with [Tcoeffs X0 n]. *)
Definition Ztech (P : Pol.T) F (X0 X : I.type) n :=
  let N := S n in
  let NthCoeff := Pol.nth (Tcoeffs X N) N in
  if isNNegOrNPos NthCoeff && I.bounded X then
    let a := I.lower X in let b := I.upper X in
    let A := I.bnd a a in let B := I.bnd b b in
    (* If need be, we could replace Pol.horner with Bnd.ComputeBound *)
    let Da := I.sub prec (F A) (Pol.horner prec P (I.sub prec A X0)) in
    let Db := I.sub prec (F B) (Pol.horner prec P (I.sub prec B X0)) in
    let Dx0 := I.sub prec (F X0) (Pol.nth P 0) (* :-D *) in
    I.join (I.join Da Db) Dx0
  else
    let NthPower :=
      I.power_int prec (I.sub prec X X0) (Z_of_nat N) in
    I.mul prec NthCoeff NthPower.

End TaylorModel.

(** Note that Zumkeller's technique is not necessary for [TM_cst] & [TM_var]. *)
Definition TM_cst (X c : I.type) : rpa :=
  RPA (Pol.polyC c) (I.mask (I.mask I.zero X) c).

Definition TM_var (X X0 : I.type) :=
  RPA (Pol.set_nth Pol.polyX 0 X0) (I.mask I.zero X).

Definition TM_exp (X0 X : I.type) (n : nat) : rpa :=
  (** Note that this let-in is essential in call-by-value context. *)
  let P := (T_exp prec X0 n) in
  RPA P (Ztech (T_exp prec) P (I.exp prec) X0 X n).

Definition TM_sin (X0 X : I.type) (n : nat) : rpa :=
  let P := (T_sin prec X0 n) in
  RPA P (Ztech (T_sin prec) P (I.sin prec) X0 X n).

Definition TM_cos (X0 X : I.type) (n : nat) : rpa :=
  let P := (T_cos prec X0 n) in
  RPA P (Ztech (T_cos prec) P (I.cos prec) X0 X n).

Definition TM_atan (X0 X : I.type) (n : nat) : rpa :=
  let P := (T_atan prec X0 n) in
  RPA P (Ztech (T_atan prec) P (I.atan prec) X0 X n).

Definition TM_add (Mf Mg : rpa) : rpa :=
  RPA (Pol.add prec (approx Mf) (approx Mg))
    (I.add prec (error Mf) (error Mg)).

Definition TM_opp (M : rpa) : rpa :=
  RPA (Pol.opp (approx M)) (I.neg (error M)).

Definition TM_sub (Mf Mg : rpa) : rpa :=
  RPA (Pol.sub prec (approx Mf) (approx Mg))
      (I.sub prec (error Mf) (error Mg)).

Definition i_validTM (X0 X : interval (* not I.type *) )
  (M : rpa) (xf : R -> ExtendedR) :=
  [/\
    forall x : R, contains X (Xreal x) -> xf x = Xnan -> I.convert (error M) = IInan,
    X = IInan -> I.convert (error M) = IInan,
    contains (I.convert (error M)) (Xreal 0),
    subset' X0 X &
    forall x0, contains X0 (Xreal x0) ->
    exists2 Q, approx M >:: Q
    & forall x, contains X (Xreal x) ->
      error M >: proj_val (xf x) - Q.[x - x0]].

Lemma TM_fun_eq f g (X0 X : interval) TMf :
  (forall x, contains X (Xreal x) -> f x = g x) ->
  i_validTM X0 X TMf f -> i_validTM X0 X TMf g.
Proof.
move=> Hfg [Hdom Hnai H0 Hsubs Hmain].
split=>//.
  move=> x Hx Dx.
  apply: (Hdom x) =>//.
  by rewrite Hfg.
move=> x0 Hx0.
move/(_ x0 Hx0) in Hmain.
have [Q HQ Hf] := Hmain.
exists Q =>//.
move=> x Hx.
rewrite -Hfg //.
exact: Hf.
Qed.

Section TM_integral.

Local Notation Isub := (I.sub prec).
Local Notation Imul := (I.mul prec).
Local Notation Iadd := (I.add prec).

Variables (X0 X : I.type).
Variable xF : R -> ExtendedR. Let f := fun x => proj_val (xF x).
Let iX0 := I.convert X0.
Let iX := I.convert X.
(* Hypothesis extF : extension f1 f. *) (* to correct *)

Hypothesis f_int : forall x x0 : R,
  contains iX (Xreal x) -> contains iX0 (Xreal x0) ->
  ex_RInt f x0 x.
Hypothesis x_Def : forall x : R, contains iX (Xreal x) -> xF x <> Xnan.
Variable Mf : rpa.

(* here we define a function which takes a Taylor Model for f
and returns a Taylor model for the primitive of f which evaluates to
*)

Definition TM_integral_poly :=
  Pol.primitive prec (I.zero) (approx Mf).

Definition TM_integral_error R :=
  Iadd (Imul (Isub X X0) (error Mf)) ((Iadd (Bnd.ComputeBound (*Pol.horner?*) prec R (Isub X0 X0)))
    (Imul (Isub X0 X0) (error Mf))).

Local Open Scope R_scope.

Lemma pol_int_sub pol x1 x2 x3 :
  ex_RInt (fun y : R => pol.[y - x3]) x1 x2.
Proof.
have -> : x1 = x1 - x3 + x3 by ring.
have -> : x2 = x2 - x3 + x3 by ring.
apply: ex_RInt_translation_sub.
exact: Rpol_integrable.
Qed.

(** the following section is now concerned with computing just one integral
    from a to b, for the "interval" tactic *)
Section NumericIntegration.

Local Open Scope R_scope.

Variables (x0 a b : R) (ia ib : I.type).

Hypothesis Hx0 : contains iX0 (Xreal x0).
Hypothesis Ha : contains iX (Xreal a).
Hypothesis Hb : contains iX (Xreal b).
Hypothesis Hia : contains (I.convert ia) (Xreal a).
Hypothesis Hib : contains (I.convert ib) (Xreal b).
Hypothesis f_int_numeric : ex_RInt f a b.

Definition polIntegral := Isub (Pol.horner prec TM_integral_poly (Isub ib X0)) (Pol.horner prec TM_integral_poly (Isub ia X0)).
Definition integralError := Imul (Isub ib ia) (error Mf).
Definition integralEnclosure := Iadd polIntegral integralError.

Lemma integralEnclosure_correct :
  i_validTM iX0 iX Mf xF ->
  contains (I.convert integralEnclosure) (Xreal (RInt f a b)).
Proof.
move => [Hdef Hnai Hcontains0 HX0X H].
have {H} [q HMfq Herror] := H x0 Hx0.
have HI: ex_RInt (fun x => q.[x - x0]) a b by exact: pol_int_sub.
have ->: RInt f a b =
    RInt (fun x => q.[x - x0]) a b +
    RInt (fun x => f x - q.[x - x0]) a b.
  rewrite RInt_minus //.
  by rewrite -[minus _ _]/(Rplus _ (Ropp _)) Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r.
apply: J.add_correct.
  rewrite RInt_translation_sub.
  rewrite Rpol_integral_0.
  have H: forall x xi, xi >: x -> Pol.horner prec TM_integral_poly (Isub xi X0) >: (PolR.primitive tt 0 q).[x - x0].
    move => x xi Hx.
    apply: Pol.horner_correct.
    exact: Pol.primitive_correct J.zero_correct HMfq.
    exact: J.sub_correct.
  apply: J.sub_correct ; exact: H.
  eapply ex_RInt_ext.
  2: apply: ex_RInt_translation_add HI.
  intros t.
  by rewrite /= /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r.
apply: J.contains_RInt => //.
  exact: ex_RInt_minus.
move => x Hx.
apply: Herror.
apply: contains_connected Hx.
now apply Rmin_case.
now apply Rmax_case.
Qed.

End NumericIntegration.

Lemma contains_interval_float_integral (p : PolR.T) :
  approx Mf >:: p ->
  TM_integral_poly >:: (PolR.primitive tt 0%R p).
Proof.
move=> Hp; rewrite /TM_integral_poly.
by apply: Pol.primitive_correct; first exact: J.zero_correct.
Qed.

Lemma TM_integral_error_0 (x0 : R) :
  contains iX0 (Xreal x0) ->
  i_validTM (I.convert X0) iX Mf xF ->
  contains (I.convert (TM_integral_error TM_integral_poly)) (Xreal 0).
Proof.
move => Hx0X0 [_ _ ErrMf0 HX0X HPol].
case: {HPol} (HPol x0 Hx0X0) => [p Hcontains _].
replace 0 with ((x0 - x0) * 0 + (0 + (x0 - x0) * 0)) by ring.
apply: J.add_correct; last apply: J.add_correct.
- apply: J.mul_correct ErrMf0.
  apply: J.sub_correct (Hx0X0).
  exact: HX0X.
- apply (@BndThm.ComputeBound_nth0 prec _ (PolR.primitive tt 0%R p)).
    apply: Pol.primitive_correct =>//; exact: J.zero_correct.
  have -> : 0%R = (x0 - x0)%R by rewrite Rminus_diag_eq.
  exact: J.sub_correct.
  exact: Pol.primitive_correct J.zero_correct Hcontains O.
- apply: J.mul_correct ErrMf0.
  exact: J.sub_correct.
Qed.

Definition TM_integral :=
  let R := TM_integral_poly in RPA R (TM_integral_error R).

Lemma TM_integral_correct (x0 : Rdefinitions.R) :
contains iX0 (Xreal x0) ->
i_validTM (I.convert X0) iX Mf xF ->
i_validTM (I.convert X0) iX TM_integral (fun x => Xreal (RInt f x0 x)).
Proof.
move => Hx0X0 [Hdef Hnai ErrMf0 HX0X HPol] /= ; split =>//.
    rewrite /TM_integral /TM_integral_error /= /iX => H.
    by rewrite I.add_propagate_l // I.mul_propagate_l // I.sub_propagate_l.
  by apply: (@TM_integral_error_0 _ Hx0X0).
move=> /= x1 HX0x1 {ErrMf0}.
case: (HPol (x0) Hx0X0) => [p Hcontains H3].
case: (HPol (x1) HX0x1) => [p1 Hcontains1 H31 {HPol}].
exists (PolR.primitive tt 0 p1).
- by apply: Pol.primitive_correct; first exact: J.zero_correct.
- move => x hxX.
  have <- : RInt f x0 x1 + RInt f x1 x = RInt f x0 x.
  + apply: RInt_Chasles; apply: f_int => //.
    exact: HX0X.
  have -> : (PolR.primitive tt 0 p1).[x - x1] =
            RInt (fun t => p1.[t - x1]) x1 x.
  + rewrite RInt_translation_sub.
      have -> : (PolR.primitive tt 0 p1).[x - x1] =
            (PolR.primitive tt 0 p1).[x - x1] -
            (PolR.primitive tt 0 p1).[x1 - x1].
      * have -> : x1 - x1 = 0 by ring.
        set t0 := (X in (_ = _ - X)).
        have->: t0 = 0; last by rewrite Rminus_0_r.
        rewrite /t0 PolR.hornerE PolR.size_primitive big1 // => i _.
        rewrite PolR.nth_primitive.
        case: ifP; first by rewrite Rmult_0_l.
        rewrite /PolR.int_coeff; case: i; first by rewrite Rmult_0_l.
        by move=> *; rewrite /= Rmult_0_l Rmult_0_r.
    by rewrite Rpol_integral_0.
    exact: Rpol_integrable.
rewrite {Hcontains1}.
set rem := (X in X + _ - _).
set i1 := (X in (rem + X - _)).
set i2 := (X in (rem + _ - X)).
have -> : rem + i1 - i2 = rem + (i1 - i2) by ring.
have -> : i1 - i2 = RInt (fun t => f t - p1.[t - x1]) x1 x.
  apply sym_eq.
  apply is_RInt_unique.
  apply: is_RInt_minus ; apply RInt_correct.
    + by apply: f_int.
    + have {2}-> : x1 = (0 + x1) by ring.
        have -> : x = (x - x1) + x1 by ring.
        apply: ex_RInt_translation_sub.
        exact: Rpol_integrable.
rewrite /TM_integral_error {i1 i2}.
rewrite Rplus_comm.
have {rem} -> : rem = RInt (fun t => p.[t - x0]) x0 x1
                     + (RInt f x0 x1 - RInt (fun t => p.[t - x0]) x0 x1).
  by rewrite /rem /Rminus (Rplus_comm (RInt f _ _)) -Rplus_assoc Rplus_opp_r Rplus_0_l.
apply: J.add_correct.
  apply: J.contains_RInt => //.
    apply: ex_RInt_minus.
    exact: f_int.
    exact: pol_int_sub.
  move => x2 Hx2.
  apply: H31.
  apply HX0X in HX0x1.
  apply: contains_connected Hx2.
  now apply Rmin_case.
  now apply Rmax_case.
apply: J.add_correct.
  rewrite RInt_translation_sub.
  rewrite Rpol_integral_0.
  rewrite (Rminus_diag_eq x0) //.
  rewrite PolR.toSeq_horner0. rewrite -nth0 -PolR.nth_toSeq PolR.nth_primitive // Rminus_0_r.
  apply: Bnd.ComputeBound_correct; last by exact: J.sub_correct.
  by apply: Pol.primitive_correct; first exact: J.zero_correct.
  exact: Rpol_integrable.
rewrite -[Rminus _ _](RInt_minus f) ; last by apply: pol_int_sub.
  apply: J.contains_RInt => //.
    apply: ex_RInt_minus.
    apply: f_int Hx0X0.
    exact: HX0X.
    exact: pol_int_sub.
  move => x2 Hx2.
  apply: H3.
  apply HX0X in Hx0X0.
  apply HX0X in HX0x1.
  apply: contains_connected Hx2.
  now apply Rmin_case.
  now apply Rmax_case.
apply: f_int Hx0X0.
exact: HX0X.
Qed.

End TM_integral.

Section Const_prelim.

Definition is_const (f : R -> ExtendedR) (X c : interval) : Prop :=
  exists2 y : ExtendedR, contains c y
  & forall x : R, contains X (Xreal x) -> f x = y.

Lemma is_const_ext (f g : R -> ExtendedR) (X c : interval) :
  (forall x : R, contains X (Xreal x) -> f x = g x) ->
  is_const f X c -> is_const g X c.
Proof.
move=> Hmain [a Ha1 Ha2].
exists a =>//.
move=> x Hx.
rewrite -Hmain //.
exact: Ha2.
Qed.

Corollary is_const_ext_weak (f g : R -> ExtendedR) (X c : interval) :
  (forall x : R, f x = g x) ->
  is_const f X c -> is_const g X c.
Proof.
move=> Hmain.
apply: is_const_ext.
move=> x _; exact: Hmain.
Qed.

End Const_prelim.

Section GenericProof.
(** Generic proof for [TLrem] and [Ztech]. *)

Variable xf : R -> ExtendedR.
Variable P : R -> nat -> PolR.T.

Let f0 := fun x => proj_val (xf x).
Let Dn n := Derive_n f0 n.

Definition Rdelta (n : nat) (x0 x : R) :=
  (f0 x - (P x0 n).[x - x0])%R.

(** We now define the derivative of [Rdelta n x0] *)
Definition Rdelta' (n : nat) (x0 x : R) :=
  (Dn 1 x - (PolR.deriv tt (P x0 n)).[x - x0])%R.

Section aux.

Variable dom : R -> Prop.
Hypothesis Hdom : connected dom.

Lemma Rmonot_contains (g : R -> R) :
  Rmonot dom g ->
  forall (x y z : R),
  dom x -> dom y -> intvl x y z ->
  intvl (g x) (g y) (g z) \/ intvl (g y) (g x) (g z).
Proof.
move=> Hmonot x y z Hx Hy Hz.
have Dz: dom z by exact: Hdom Hz.
case: Hmonot; rewrite /Rincr /Rdecr =>H; [left|right];
  split; apply: H =>//; move: Hz; rewrite /intvl /=;
  by move=> [H1 H2].
Qed.

Lemma upper_Rpos_over
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  dom x0 ->
  Rpos_over dom (Dn n.+1) ->
  forall x : R, (x0 <= x)%R -> dom x -> intvl x x0 c \/ intvl x0 x c ->
  (0 <= (Dn n.+1 c) / INR (fact n) * (x - x0) ^ n)%R.
Proof.
move=> Hx0 Hsign x Hx Dx [Hc|Hc].
  have ->: x = x0.
    by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_pos_pos.
apply: Rdiv_pos_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
apply: pow_le.
now apply Rle_0_minus.
Qed.

Lemma upper_Rneg_over
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  dom x0 ->
  Rneg_over dom (Dn n.+1) ->
  forall x : R, (x0 <= x)%R -> dom x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%R.
Proof.
move=> Hx0 Hsign x Hx Dx [Hc|Hc].
  have ->: x = x0.
    by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_neg_pos.
apply: Rdiv_neg_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
apply: pow_le.
now apply Rle_0_minus.
Qed.

Lemma pow_Rabs_sign (r : R) (n : nat) :
  (r ^ n = powerRZ
    (if Rle_bool R0 r then 1 else -1) (Z_of_nat n) * (Rabs r) ^ n)%R.
Proof.
elim: n =>[|n /= ->]; first by rewrite Rmult_1_l.
case: Rle_bool_spec => Hr.
  rewrite powerRZ_R1 Rmult_1_l SuccNat2Pos.id_succ.
  by rewrite pow1 Rabs_pos_eq // Rmult_1_l.
by rewrite {-1 3}Rabs_left // SuccNat2Pos.id_succ -pow_powerRZ /=; ring.
Qed.

Lemma powerRZ_1_even (k : Z) : (0 <= powerRZ (-1) (2 * k))%R.
Proof.
by case: k =>[|p|p] /=; rewrite ?Pos2Nat.inj_xO ?pow_1_even; auto with real.
Qed.

Lemma ZEven_pow_le (r : R) (n : nat) :
  Z.Even (Z_of_nat n) ->
  (0 <= r ^ n)%R.
Proof.
move=> [k Hk].
rewrite pow_Rabs_sign; case: Rle_bool_spec =>[_|Hr].
  rewrite powerRZ_R1 Rmult_1_l.
  apply: pow_le.
  exact: Rabs_pos.
rewrite Hk.
apply: Rmult_le_pos_pos; first exact: powerRZ_1_even.
by apply: pow_le; exact: Rabs_pos.
Qed.

Lemma Ropp_le_0 (x : R) :
  (0 <= x -> - x <= 0)%R.
Proof. by move=> ?; auto with real. Qed.

Lemma ZOdd_pow_le (r : R) (n : nat) :
  Z.Odd (Z_of_nat n) ->
  (r <= 0 -> r ^ n <= 0)%R.
Proof.
move=> [k Hk] Hneg.
rewrite pow_Rabs_sign; case: Rle_bool_spec =>[Hr|Hr].
  have->: r = R0 by psatzl R.
  rewrite Rabs_R0 pow_ne_zero ?Rmult_0_r; first by auto with real.
  by zify; omega. (* odd => nonzero *)
rewrite Hk.
apply: Rmult_le_neg_pos; last by apply: pow_le; exact: Rabs_pos.
rewrite powerRZ_add; discrR.
apply: Rmult_le_pos_neg; first exact: powerRZ_1_even.
by rewrite /= Rmult_1_r; apply: Ropp_le_0; apply: Rle_0_1.
Qed.

Lemma lower_even_Rpos_over
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  dom x0 ->
  Rpos_over dom (Dn n.+1) ->
  forall x : R, (x <= x0)%R -> dom x -> intvl x x0 c \/ intvl x0 x c ->
  (0 <= Dn n.+1 c / INR (fact n) * (x - x0) ^ n)%R.
Proof.
move=> Hev Hx0 Hsign x Hx Dx [Hc|Hc]; last first.
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_pos_pos.
apply: Rdiv_pos_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
exact: ZEven_pow_le.
Qed.

Lemma lower_even_Rneg_over
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  dom x0 ->
  Rneg_over dom (Dn n.+1) ->
  forall x : R, (x <= x0)%R -> dom x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%R.
Proof.
move=> Hev Hx0 Hsign x Hx Dx [Hc|Hc]; last first.
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_neg_pos.
apply: Rdiv_neg_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
exact: ZEven_pow_le.
Qed.

Lemma lower_odd_Rpos_over
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  dom x0 ->
  Rpos_over dom (Dn n.+1) ->
  forall x : R, (x <= x0)%R -> dom x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%R.
Proof.
move=> Hev Hx0 Hsign x Hx Dx [Hc|Hc]; last first.
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_pos_neg.
apply: Rdiv_pos_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
apply: ZOdd_pow_le Hev _.
now apply Rle_minus.
Qed.

Lemma lower_odd_Rneg_over (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  dom x0 ->
  Rneg_over dom (Dn n.+1) ->
  forall x : R, dom x -> (x <= x0)%R -> intvl x x0 c \/ intvl x0 x c ->
  (0 <= (Dn n.+1 c) / INR (fact n) * (x - x0) ^ n)%R.
Proof.
move=> Hev Hx0 Hsign x Hx Dx [Hc|Hc]; last first.
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
apply: Rmult_le_neg_neg.
apply: Rdiv_neg_compat.
apply: Hsign.
exact: Hdom Hc.
exact: INR_fact_lt_0.
apply: ZOdd_pow_le Hev _.
now apply Rle_minus.
Qed.

Hypothesis Hder_n : forall n x, dom x -> ex_derive_n f0 n x.

Lemma Rderive_delta (Pr : R -> Prop) (n : nat) (x0 : R) :
  dom x0 ->
  Pr x0 ->
  Rderive_over (fun t => dom t /\ Pr t) (Rdelta n x0) (Rdelta' n x0).
Proof.
move=> Dx0 HPr x Hx.
rewrite /Rdelta /Rdelta'.
apply: is_derive_minus.
  apply: Derive_correct.
  now apply (Hder_n 1).
set d := (_ ^`()).[_].
have->: d = scal R1 d by rewrite /scal /= /mult /= Rmult_1_l.
apply: is_derive_comp; last first.
rewrite -[R1]Rminus_0_r; apply: is_derive_minus; by auto_derive.
rewrite /d.
exact: PolR.is_derive_horner.
Qed.

Hypothesis Poly_size : forall (x0 : R) n, PolR.size (P x0 n) = n.+1.
Hypothesis Poly_nth : forall (x : R) n k, dom x -> k <= n ->
  PolR.nth (P x n) k = Rdiv (Dn k x) (INR (fact k)).

Lemma bigXadd'_P (m n : nat) (x0 s : R) :
  dom x0 ->
  ex_derive_n f0 n x0 ->
  m <= n ->
  \big[Rplus/R0]_(0 <= i < m) (PolR.nth (P x0 n) i.+1 * INR i.+1 * s ^ i)%R =
  \big[Rplus/R0]_(0 <= i < m) ((Dn i.+1 x0) / INR (fact i) * s ^ i)%R.
Proof.
move=> H0 Hx0 Hmn; rewrite !big_mkord.
case: m Hmn =>[|m] Hmn; first by rewrite !big_ord0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> ->//|i _].
rewrite Poly_nth //; last by case: i => [i Hi] /=; exact: leq_trans Hi Hmn.
rewrite fact_simpl mult_INR.
field.
split; by [apply: INR_fact_neq_0 | apply: not_0_INR ].
Qed.

(** Proposition 2.2.1 in Mioara Joldes' thesis,
    adapted from Lemma 5.12 in Roland Zumkeller's thesis *)
Theorem Zumkeller_monot_rem (x0 : R) (n : nat) :
  dom x0 ->
  Rcst_sign dom (Dn n.+1) ->
  Rmonot (fun t => dom t /\ (t <= x0)%R) (Rdelta n x0) /\
  Rmonot (fun t => dom t /\ (x0 <= t)%R) (Rdelta n x0).
Proof.
move=> Hx0.
case: n =>[|nm1] ; last set n := nm1.+1.
  move=> Hsign; split; apply (@Rderive_cst_sign _ _ (Dn 1)) =>//.
  - apply: connected_and => //.
    exact: connected_le.
  - move=> x [Hx1 Hx2].
    rewrite -[Dn 1 x]Rminus_0_r.
    apply: is_derive_minus.
      apply: Derive_correct.
      exact: (Hder_n 1).
    auto_derive.
      exact: PolR.ex_derive_horner.
    rewrite Rmult_1_l (Derive_ext _ (fun r => PolR.nth (P x0 0) 0)).
      by rewrite Derive_const.
    by move=> r; rewrite PolR.hornerE Poly_size big_nat1 pow_O Rmult_1_r.
  - case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Rpos_over /Rneg_over.
    + move=> Htop x [Hx1 Hx2]; exact: Htop.
    + move=> Htop x [Hx1 Hx2]; exact: Htop.
  - apply: connected_and => //.
    exact: connected_ge.
  - move=> x [Hx1 Hx2].
    rewrite -[Dn 1 x]Rminus_0_r.
    apply: is_derive_minus.
      apply: Derive_correct.
      exact: (Hder_n 1).
    auto_derive.
      exact: PolR.ex_derive_horner.
    rewrite Rmult_1_l (Derive_ext _ (fun r => PolR.nth (P x0 0) 0)).
      by rewrite Derive_const.
    by move=> r; rewrite PolR.hornerE Poly_size big_nat1 pow_O Rmult_1_r.
  case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Rpos_over /Rneg_over.
  + move=> Htop x [Hx1 Hx2]; exact: Htop.
  + move=> Htop x [Hx1 Hx2]; exact: Htop.
have TL := @ITaylor_Lagrange (fun x => Xreal (Derive f0 x)) dom Hdom n.-1  _ x0 _ Hx0.
case=>[Hpos|Hneg].
  split.
    apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
    * apply: connected_and => //.
      exact: connected_le.
    * apply: Rderive_delta => //.
      exact: Rle_refl.

    { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
      - left.
        move=> x [Hx1 Hx2].
        have [||c [H1 [H2 H3]]] := TL _ x =>//.
          move=> k t Ht.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          exact: (Hder_n k.+2).
        rewrite /Rdelta' PolR.horner_derivE Poly_size.
        rewrite bigXadd'_P //; last exact/Hder_n.
        set b := \big[Rplus/R0]_(_ <= i < _) _.
        set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
        have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
        rewrite /b /b2 H2 -Derive_nS.
        exact: (@lower_even_Rpos_over c x0 nm1).

      - right.
        move=> x [Hx1 Hx2].
        have [||c [H1 [H2 H3]]] := TL _ x =>//.
          move=> k t Ht.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          exact: (Hder_n k.+2).
        rewrite /Rdelta' PolR.horner_derivE Poly_size.
        rewrite bigXadd'_P //; last exact/Hder_n.
        set b := \big[Rplus/R0]_(_ <= i < _) _.
        set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
        have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
        rewrite /b /b2 H2 -Derive_nS.
        exact: (@lower_odd_Rpos_over c x0 nm1).
    }

  apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
  * apply: connected_and => //.
    exact: connected_ge.
  * apply: Rderive_delta => //.
    exact: Rle_refl.

  left.
  move=> x [Hx1 Hx2].
  have [||c [H1 [H2 H3]]] := TL _ x =>//.
    move=> k t Ht.
    case: k => [//|k]; rewrite -ex_derive_nSS.
    exact: (Hder_n k.+2).
  rewrite /Rdelta' PolR.horner_derivE Poly_size.
  rewrite bigXadd'_P //; last exact/Hder_n.
  set b := \big[Rplus/R0]_(_ <= i < _) _.
  set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
  have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
  rewrite /b /b2 H2 -Derive_nS.
  exact: (@upper_Rpos_over c x0 nm1).

split.

  apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
  * apply: connected_and => //.
    exact: connected_le.
  * apply: Rderive_delta => //.
    exact: Rle_refl.

  { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
  - right.
    move=> x [Hx1 Hx2].
    have [||c [H1 [H2 H3]]] := TL _ x =>//.
      move=> k t Ht.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      exact: (Hder_n k.+2).
    rewrite /Rdelta' PolR.horner_derivE Poly_size.
    rewrite bigXadd'_P //; last exact/Hder_n.
    set b := \big[Rplus/R0]_(_ <= i < _) _.
    set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
    have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
    rewrite /b /b2 H2 -Derive_nS.
    exact: (@lower_even_Rneg_over c x0 nm1).

  - left.
    move=> x [Hx1 Hx2].
    have [||c [H1 [H2 H3]]] := TL _ x =>//.
      move=> k t Ht.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      exact: (Hder_n k.+2).
    rewrite /Rdelta' PolR.horner_derivE Poly_size.
    rewrite bigXadd'_P //; last exact/Hder_n.
    set b := \big[Rplus/R0]_(_ <= i < _) _.
    set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
    have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
    rewrite /b /b2 H2 -Derive_nS.
    exact: (@lower_odd_Rneg_over c x0 nm1).
}

apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
* apply: connected_and => //.
  exact: connected_ge.
* apply: Rderive_delta => //.
  exact: Rle_refl.

right.
move=> x [Hx1 Hx2].
have [||c [H1 [H2 H3]]] := TL _ x =>//.
  move=> k t Ht.
  case: k => [//|k]; rewrite -ex_derive_nSS.
  exact: (Hder_n k.+2).
rewrite /Rdelta' PolR.horner_derivE Poly_size.
rewrite bigXadd'_P //; last exact/Hder_n.
set b := \big[Rplus/R0]_(_ <= i < _) _.
set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
rewrite /b /b2 H2 -Derive_nS.
exact: (@upper_Rneg_over c x0 nm1).
Qed.

End aux.

Variable F : I.type -> I.type.
Variable IP : I.type -> nat -> Pol.T.

Hypothesis F_contains : I.extension (Xbind xf) F.

Variables X : I.type.

Class validPoly : Prop := ValidPoly {
  Poly_size : forall (x0 : R) n, PolR.size (P x0 n) = n.+1;
  Poly_nth :
    forall (x : R) n k,
    X >: x ->
    k <= n ->
    PolR.nth (P x n) k = Rdiv (Dn k x) (INR (fact k)) }.

Class validIPoly : Prop := ValidIPoly {
  IPoly_size :
    forall (X0 : I.type) x0 n, eq_size (IP X0 n) (P x0 n);
  IPoly_nth : forall (X0 : I.type) x0 n, X0 >: x0 -> IP X0 n >:: P x0 n;
  IPoly_nai :
    forall X, forall r : R, contains (I.convert X) (Xreal r) -> xf r = Xnan ->
    forall n k, k <= n -> I.convert (Pol.nth (IP X n) k) = IInan
}.

Context { validPoly_ : validPoly }.
Context { validIPoly_ : validIPoly }.

Hypothesis Hder_n : forall n x, X >: x -> ex_derive_n f0 n x.

Lemma Poly_nth0 x n : X >: x -> PolR.nth (P x n) 0 = f0 x.
Proof. by move=> H; rewrite Poly_nth // ?Rcomplements.Rdiv_1 //. Qed.

Theorem i_validTM_TLrem (X0 : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (TLrem IP X0 X n)) xf.
Proof.
move=> Hsubs [t Ht].
pose err := TLrem IP X0 X n.
split=>//=.

(* Def *)
move=> x Hx Nx.
rewrite /TLrem.
apply I.mul_propagate_l.
exact: (IPoly_nai Hx Nx).

(* Nai *)
move=> HX; rewrite /TLrem.
by rewrite I.mul_propagate_r // J.power_int_propagate // I.sub_propagate_l.

(* |- 0 \in err *)
set V := (I.power_int prec (I.sub prec X X0) (Z_of_nat n.+1)).
apply (mul_0_contains_0_r _ (y := Xreal (PolR.nth (P t n.+1) n.+1))).
  apply: IPoly_nth =>//.
  exact: Hsubs.
apply: pow_contains_0 =>//.
exact: subset_sub_contains_0 Ht Hsubs.

move=> x0 Hx0.
(* |- Main condition for i_validTM *)
exists (P x0 n); first by apply: IPoly_nth.
move=> x Hx.
rewrite PolR.hornerE Poly_size //.
have H0 : X >: x0 by exact: Hsubs.
have Hbig :
  \big[Rplus/R0]_(0 <= i < n.+1) (PolR.nth (P x0 n) i * (x - x0) ^ i)%R =
  \big[Rplus/R0]_(0 <= i < n.+1) (Dn i x0 / INR (fact i) * (x - x0)^i)%R.
by apply: eq_big_nat => i Hi; rewrite Poly_nth.
rewrite Hbig.
have Hder' : forall n r, X >: r -> ex_derive_n f0 n r.
  move=> m r Hr.
  exact: Hder_n.
have [c [Hcin [Hc Hc']]] := (@ITaylor_Lagrange xf _ (contains_connected (I.convert X)) n Hder' x0 x H0 Hx).
rewrite Hc {Hc t Ht} /TLrem.
apply: J.mul_correct=>//.
  rewrite -(@Poly_nth _ c n.+1 n.+1) //;
  exact: IPoly_nth.
rewrite pow_powerRZ.
apply: J.power_int_correct.
exact: J.sub_correct.
Qed.

Lemma Ztech_derive_sign (n : nat) :
  isNNegOrNPos (Pol.nth (IP X n.+1) n.+1) = true ->
  Rcst_sign (fun t => contains (I.convert X) (Xreal t)) (Dn n.+1).
Proof.
move=> Hsign.
have: Rcst_sign (fun t => contains (I.convert X) (Xreal t))
  (fun x => (Dn n.+1 x) / INR (fact n.+1))%R.
  move: Hsign; set Gamma := Pol.nth _ _.
  set g := fun x => ((Dn n.+1 x) / INR (fact n.+1))%R.
  have inGamma : forall x, X >: x -> Gamma >: g x.
    move => x Hx.
    rewrite /g -(Poly_nth _ (n:=n.+1)) //.
    exact: IPoly_nth.
  rewrite /isNNegOrNPos.
  case E : I.sign_large =>// _;
    have := I.sign_large_correct Gamma; rewrite E => Hmain.
  - left; move=> x Hx.
    case/(_ _ (inGamma x Hx)): Hmain =>->.
    exact: Rle_refl.
  - right; move=> x Hx.
    now apply (Hmain (Xreal (g x))), inGamma.
  - left; move=> x Hx.
    now apply (Hmain (Xreal (g x))), inGamma.
case=>[Htop|Htop]; [left|right]; intros x Hx.
- apply: Rdiv_pos_compat_rev (Htop x Hx) _.
  exact: INR_fact_lt_0.
- apply: Rdiv_neg_compat_rev (Htop x Hx) _.
  exact: INR_fact_lt_0.
Qed.

Lemma F_Rcontains : forall X x, X >: x -> F X >: f0 x.
Proof.
clear -F_contains.
move => X x /F_contains.
rewrite /f0 /Xbind.
case: xf => //.
by case I.convert.
Qed.

Theorem i_validTM_Ztech (X0 : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (Ztech IP (IP X0 n) F X0 X n)) xf.
Proof.
move=> Hsubs Hne.
case E1 : (isNNegOrNPos (Pol.nth (IP X n.+1) n.+1)); last first.
  rewrite /Ztech E1 /=.
  exact: i_validTM_TLrem.
case E2 : (I.bounded X); last first.
  rewrite /Ztech E2 andbC /=.
  exact: i_validTM_TLrem.
set err := Ztech IP (IP X0 n) F X0 X n.
have Hdef : forall r : R, X >: r -> xf r <> Xnan.
  move=> r Hr Kr.
  have Knai := @IPoly_nai validIPoly_ X r Hr Kr n.+1 n.+1 (leqnn _).
  by rewrite isNNegOrNPos_false in E1.
split=>//.
- by move=> x Hx /(Hdef x Hx).
- apply I.bounded_correct in E2.
  now rewrite (proj2 (I.lower_bounded_correct _ _)).
- rewrite /= /err /Ztech E1 E2 /=.
  apply: I.join_correct; right.
  have [r' Hr'0] := Hne.
  have Hr' : contains (I.convert X) (Xreal r').
    exact: Hsubs.
  have E0 : xf r' = Xreal (PolR.nth (P r' n) 0).
    rewrite Poly_nth0 // /f0.
    by case: (xf r') (Hdef r' Hr').
  pose r'0 := PolR.nth (P r' n) 0.
  have->: Xreal 0 = Xsub (xf r') (Xreal r'0) by rewrite E0 /= Rminus_diag_eq.
  apply: I.sub_correct.
  exact: F_contains Hr'0.
  exact: IPoly_nth.
clear Hdef Hne.
move=> x0 Hx0.
exists (P x0 n); first by move=> k; apply: IPoly_nth.
pose Rdelta0 := Rdelta n x0.
move=> x Hx.

rewrite /err /Ztech E1 E2 /=.
set Delta := I.join (I.join _ _) _; rewrite -/(Rdelta n x0 x) -/(Rdelta0 x).
have [Hbl Hbu] := I.bounded_correct _ E2.
have [Hcl _] := I.lower_bounded_correct _ Hbl.
have [Hcu _] := I.upper_bounded_correct _ Hbu.
set (l := (proj_val (I.convert_bound (I.lower X)))) in Hcl.
set (u := (proj_val (I.convert_bound (I.upper X)))) in Hcu.
have HX: I.convert X = Ibnd (Xreal l) (Xreal u).
  rewrite -Hcl -Hcu.
  now apply I.lower_bounded_correct.
have {Hcl Hbl} Hlower : Delta >: Rdelta0 l.
  apply: I.join_correct; left; apply: I.join_correct; left.
  have Hlower : contains (I.convert (I.bnd (I.lower X) (I.lower X))) (Xreal l).
    rewrite I.bnd_correct Hcl; split; apply Rle_refl.
  apply: J.sub_correct.
  - exact: F_Rcontains.
  - apply: Pol.horner_correct.
    exact: IPoly_nth.
    exact: J.sub_correct.
have {Hcu Hbu} Hupper : Delta >: Rdelta0 u.
  apply: I.join_correct; left; apply: I.join_correct; right.
  have Hupper : contains (I.convert (I.bnd (I.upper X) (I.upper X))) (Xreal u).
    rewrite I.bnd_correct Hcu; split; apply Rle_refl.
  apply: J.sub_correct.
  - exact: F_Rcontains.
  - apply: Pol.horner_correct.
    exact: IPoly_nth.
    exact: J.sub_correct.
have H'x0 : X >: x0 by exact: Hsubs.
have HX0 : Delta >: Rdelta0 x0.
  apply: I.join_correct; right.
  apply: J.sub_correct; first exact: F_Rcontains.
  rewrite Rminus_diag_eq //.
  suff->: ((P x0 n).[0%R]) = PolR.nth (P x0 n) 0 by apply: IPoly_nth.
  rewrite PolR.hornerE Poly_size big_nat_recl // pow_O Rmult_1_r.
  rewrite big1 ?(Rplus_0_r, Rmult_1_r) //.
  move=> i _.
  by rewrite /= Rmult_0_l Rmult_0_r.
clearbody Delta l u.
rewrite -> HX in Hx, H'x0.
have [||Hlow|Hup] := @intvl_lVu l u x0 x => //.
  have [|||H1|H2] := @Rmonot_contains _ (@intvl_connected l x0) Rdelta0 _ _ _ _ _ _ Hlow.
  + have [|||||H _] := @Zumkeller_monot_rem _ (contains_connected (I.convert X)) _ _ _ x0 n => //.
    apply Poly_size.
    apply Poly_nth.
    by rewrite HX.
    exact: Ztech_derive_sign.
    case: H => H ; [left|right] ; intros p q Hp Hq Hpq ; apply H => // ; rewrite HX ; split ;
      try apply: intvl_connected (intvl_l H'x0) (H'x0) _ _ => // ;
      try apply Hp ; try apply Hq.
    exact: intvl_l Hlow.
    exact: intvl_u Hlow.
  + exact: contains_connected H1.
  + exact: contains_connected H2.
have [|||H1|H2] := @Rmonot_contains _ (@intvl_connected x0 u) Rdelta0 _ _ _ _ _ _ Hup.
+ have [|||||_ H] := @Zumkeller_monot_rem _ (contains_connected (I.convert X)) _ _ _ x0 n => //.
  apply Poly_size.
  apply Poly_nth.
  by rewrite HX.
  exact: Ztech_derive_sign.
  case: H => H ; [left|right] ; intros p q Hp Hq Hpq ; apply H => // ; rewrite HX ; split ;
    try apply: intvl_connected (H'x0) (intvl_u H'x0) _ _ => // ;
    try apply Hp ; try apply Hq.
  exact: intvl_l Hup.
  exact: intvl_u Hup.
+ exact: contains_connected H1.
+ exact: contains_connected H2.
Qed.

End GenericProof.

Lemma size_TM_cst (X c : I.type) : Pol.size (approx (TM_cst X c)) = 1.
Proof. by rewrite /TM_cst Pol.polyCE Pol.size_polyCons Pol.size_polyNil. Qed.

Theorem TM_cst_correct (ci X0 X : I.type) (c : ExtendedR) :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  contains (I.convert ci) c ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst X ci) (fun _ => c).
Proof.
move=> Hsubset [t Ht] Hc.
split=>//=.
  move=> x Hx Nx.
  apply I.mask_propagate_r, contains_Xnan.
  by rewrite -Nx.
  by move=> HX; apply I.mask_propagate_l, I.mask_propagate_r.
  apply I.mask_correct', I.mask_correct', J.zero_correct.
move=> x0 Hx0.
case: c Hc => [|c]; first move/contains_Xnan; move => Hc.
exists (PolR.polyC 0%R); first by apply: Pol.polyC_correct; rewrite Hc.
  by move=> x Hx; rewrite I.mask_propagate_r.
exists (PolR.polyC c); first exact: Pol.polyC_correct.
move=> x Hx /=.
rewrite Rmult_0_l Rplus_0_l Rminus_diag_eq //.
apply I.mask_correct', I.mask_correct', J.zero_correct.
Qed.

Theorem TM_cst_correct_strong (ci X0 X : I.type) (f : R -> ExtendedR) :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  is_const f (I.convert X) (I.convert ci) ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst X ci) f.
Proof.
move=> Hsubset Hne [c H1 H2].
apply: TM_fun_eq; last apply: TM_cst_correct Hsubset Hne H1.
move=> x Hx /=.
by apply sym_eq, H2.
Qed.

(** Return a dummy Taylor model of order [n] that contains every point of [Y] *)
Definition TM_any (Y : I.type) (X : I.type) (n : nat) :=
  let mid := I.midpoint' Y in
  let pol := Pol.polyC mid in
  {| approx := if n == 0 then pol
               else Pol.set_nth pol n Pol.Int.zero;
     error := I.mask (I.sub prec Y mid) X
  |}.

Definition sizes := (Pol.size_polyNil, Pol.size_polyCons,
                     PolR.size_polyNil, PolR.size_polyCons,
                     Pol.size_set_nth, PolR.size_set_nth,
                     Pol.polyCE).

Lemma size_TM_any (c X : I.type) n : Pol.size (approx (TM_any c X n)) = n.+1.
Proof.
rewrite /TM_any /=.
case: n =>[|n] /=.
  by rewrite !sizes.
by rewrite Pol.size_set_nth !sizes maxnSS maxn0.
Qed.

Theorem TM_any_correct
  (Y X0 X : I.type) (n : nat) (f : R -> ExtendedR) :
  not_empty (I.convert X0) -> subset' (I.convert X0) (I.convert X) ->
  (forall x : R, contains (I.convert X) (Xreal x) ->
    contains (I.convert Y) (f x)) ->
  i_validTM (I.convert X0) (I.convert X) (TM_any Y X n) f.
Proof.
move=> H0 Hsubset Hf.
have [x0' Hx0'] := H0.
have H'x0': X >: x0' by exact: Hsubset.
have Hrr := Hf _ H'x0'.
set r := proj_val (f x0').
have Hr : contains (I.convert Y) (Xreal r).
  exact: contains_Xreal.
have Hmid := I.midpoint'_correct Y.
have [m Hm] := proj2 Hmid (ex_intro _ r Hr).
split=>//.
  move=> /= x Hx Nx.
  rewrite /TM_any /= in Nx.
  apply I.mask_propagate_l, I.sub_propagate_l, contains_Xnan.
  rewrite -Nx.
  exact: Hf.
  apply I.mask_propagate_r.
  apply I.mask_correct'.
  apply: subset_sub_contains_0 Hm _.
  exact: proj1 Hmid.
move=> x0 Hx0.
set pol0 := PolR.polyC m.
set pol' := if n == 0 then pol0 else PolR.set_nth pol0 n 0%R.
exists pol'.
rewrite /pol' {pol'} /pol0 /TM_any /=.
+ case: ifP => H.
  exact: Pol.polyC_correct.
  apply: Pol.set_nth_correct.
  exact: Pol.polyC_correct.
  exact: J.zero_correct.
+ move=> x Hx /=.
  apply I.mask_correct', J.sub_correct.
  now apply contains_Xreal, Hf.
  rewrite /pol' /pol0; case: ifP => H.
  by rewrite PolR.horner_polyC.
  rewrite PolR.hornerE !sizes maxnSS maxn0.
  step_r (pol0.[x - x0])%R.
  by rewrite PolR.horner_polyC.
  rewrite /pol0 (@PolR.hornerE_wide n.+1) ?sizes //.
  apply: eq_bigr => i _.
  congr Rmult.
  rewrite PolR.polyCE !(PolR.nth_polyCons, PolR.nth_set_nth).
  case: i => [//|i]; first by rewrite eq_sym H.
  by rewrite PolR.nth_polyNil if_same.
Qed.

Lemma size_TM_var (X X0 : I.type) : Pol.size (approx (TM_var X X0)) = 2.
Proof.
rewrite /TM_var Pol.size_set_nth
Pol.polyXE Pol.size_lift Pol.oneE Pol.polyCE.
by rewrite Pol.size_polyCons Pol.size_polyNil.
Qed.

Lemma TM_var_correct (X0 X : I.type) :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X X0) Xreal.
Proof.
move=> Hsubs [t Ht].
split=>//.
  apply I.mask_propagate_r.
  apply I.mask_correct', J.zero_correct.
move=> x0 Hx0 /=.
exists (PolR.set_nth PolR.polyX 0 x0).
  apply: Pol.set_nth_correct =>//.
  exact: Pol.polyX_correct.
move=> x Hx /=.
replace (x - _)%R with R0 by ring.
apply I.mask_correct', J.zero_correct.
Qed.

Theorem TM_var_correct_strong (X0 X : I.type) (f : R -> ExtendedR) :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  (forall x : R, contains (I.convert X) (Xreal x) -> f x = Xreal x) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X X0) f.
Proof.
move=> Hsubset Hne Hid.
apply: TM_fun_eq; last apply: TM_var_correct Hsubset Hne.
by move=> *; rewrite Hid.
Qed.

Lemma size_TM_exp (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_exp X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Lemma TM_exp_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_exp X0 X n) (fun x => Xreal (exp x)).
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_exp tt); last 2 first =>//.
exact: I.exp_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hk; rewrite /PolR.nth.
    elim: k Hk => [|k IHk] Hk.
    - by rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
      rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := k)) // in IHk; last exact: ltnW.
      rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := k.+1)) // nth_rec1upS.
      rewrite {}IHk /TR.exp_rec; last exact: ltnW.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_exp _ _)).
      rewrite fact_simpl mult_INR.
      change eq with (@eq R); field; split.
      apply INR_fact_neq_0.
      now apply not_0_INR.
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
    by move=> *;
      repeat first [apply: J.div_correct
                   |apply: R_from_nat_correct
                   ].
    exact: J.exp_correct.
  }
- done.
- move=> {n} n x Hx; eapply ex_derive_n_is_derive_n; exact: is_derive_n_exp.
Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall k, P k -> P k.+1 -> P k.+2) ->
  forall k, P k.
Proof.
move=> H0 H1 Hind k.
suff : P k /\ P k.+1 by case.
elim: k => [|k [IHk0 IHk1]]; first by split.
split; by [|apply: Hind].
Qed.

Lemma size_TM_sin (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_sin X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma TM_sin_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sin X0 X n) (fun x => Xreal (sin x)).
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_sin tt); last 2 first =>//.
exact: I.sin_correct.
constructor.
- by move=> x m; rewrite /TR.T_sin PolR.size_rec2.
- move=> x m k Dx Hk; rewrite /TR.T_sin.
  rewrite /PolR.nth /PolR.rec2; clear - Hk.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.sin_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1))%R in Hk0 Hk1 *.
      have Hkm : k <= m by do 2![apply: ltnW].
      move/(_ Hkm) in Hk0.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k)) // in Hk0.
      rewrite Hk0 !Derive_nS; clear.
      rewrite [in RHS](Derive_n_ext _ (fun x => - sin x)); last first.
        move=> t; change (Derive _ t) with (Derive_n sin 2 t).
        rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_sin _ _)) /= Rmult_1_r.
        by rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
      rewrite Derive_n_opp 2!fact_simpl 2!mult_INR.
      change (Derive_n (fun x => _)) with (Derive_n sin).
      simpl (k.+2.-1).
      change eq with (@eq R); field; split.
      apply INR_fact_neq_0.
      split ; exact: not_0_INR.
  }
constructor.
- by move=> x m k; rewrite /TR.T_sin Pol.size_rec2 PolR.size_rec2.
- by move=> Y x m Hx; apply: Pol.rec2_correct; first move=> ai bi a b l Ha Hb;
  repeat first [apply: J.div_correct|
                apply: J.neg_correct|
                apply: J.mul_correct|
                apply: R_from_nat_correct|
                apply: J.sin_correct|
                apply: J.cos_correct].
- move=> Y x Hx Dx m k Hk; rewrite /T_sin.
- done.
- move=> *; apply/ex_derive_n_is_derive_n/is_derive_n_sin.
Qed.

Lemma size_TM_cos (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_cos X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma TM_cos_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_cos X0 X n) (fun x => Xreal (cos x)).
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_cos tt); last 2 first =>//.
exact: I.cos_correct.
constructor.
- by move=> x m; rewrite /TR.T_cos PolR.size_rec2.
- move=> x m k Dx Hk; rewrite /TR.T_cos.
  rewrite /PolR.nth /PolR.rec2; clear - Hk.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.cos_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1))%R in Hk0 Hk1 *.
      have Hkm : k <= m by do 2![apply: ltnW].
      move/(_ Hkm) in Hk0.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k)) // in Hk0.
      rewrite Hk0 !Derive_nS; clear.
      rewrite [in RHS](Derive_n_ext _ (fun x => - cos x)); last first.
        move=> t; change (Derive _ t) with (Derive_n cos 2 t).
        rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_cos _ _)) /= Rmult_1_r.
        by rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
      rewrite Derive_n_opp 2!fact_simpl 2!mult_INR.
      change (Derive_n (fun x => _)) with (Derive_n cos).
      simpl (k.+2.-1).
      change eq with (@eq R); field; split.
      apply INR_fact_neq_0.
      split ; exact: not_0_INR.
  }
constructor.
- by move=> x m k; rewrite /TR.T_cos Pol.size_rec2 PolR.size_rec2.
- by move=> Y x m Hx; apply: Pol.rec2_correct; first move=> ai bi a b l Ha Hb;
  repeat first [apply: J.div_correct|
                apply: J.neg_correct|
                apply: J.mul_correct|
                apply: R_from_nat_correct|
                apply: J.sin_correct|
                apply: J.cos_correct].
- done.
- move=> *; apply/ex_derive_n_is_derive_n/is_derive_n_cos.
Qed.

Lemma size_TM_atan (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_atan X0 X n)) = n.+1.
Proof. by rewrite Pol.size_grec1. Qed.

Lemma TM_atan_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_atan X0 X n) (fun x => Xreal (atan x)).
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_atan tt); last 2 first =>//.
exact: I.atan_correct.
constructor.
- by move=> ? ?; rewrite PolR.size_grec1.
- { (* The proof of this goal might be shortened by reusing is_derive_n_atan *)
    move=> {X0 n Hsubset Hex} x n k Hx H;
    rewrite /TR.T_atan /PolR.nth /PolR.grec1
      (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
      nth_grec1up_last.
    case: k H => [|k H]; first by rewrite /= ?Rdiv_1.
    rewrite last_grec1up // head_gloop1.
    rewrite [size _]/= subn1 [_.+1.-1]/=.
    elim: k H x {Hx} =>[|k IHk] H x.
    + rewrite /= Rmult_0_l Rplus_0_l Rmult_1_r Rdiv_1.
      symmetry; apply: is_derive_unique; auto_derive =>//.
      by rewrite Rmult_1_r.
    + move/ltnW in H; move/(_ H) in IHk.
      rewrite [INR]lock [PolR.lift]lock [fact]lock /= -!lock.
      set qk := iteri k
        (fun i c => PolR.div_mixed_r tt _ (INR (i + 1).+1)) PolR.one in IHk *.
      rewrite (@Derive_ext _
        (fun x => qk.[x] / (1+x*x) ^ (k+1) * INR (fact k.+1))%R);
        first last.
        move=> t; move/(_ t) in IHk; rewrite -pow_powerRZ in IHk.
        rewrite IHk /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r //.
        exact: INR_fact_neq_0.
      clear IHk.
      rewrite PolR.horner_div_mixed_r PolR.horner_sub PolR.horner_add.
      rewrite PolR.horner_mul_mixed !PolR.horner_lift Derive_scal_l.
      rewrite Derive_div; first last.
      * by apply: pow_nonzero; apply: Rsqr_plus1_neq0.
      * by auto_derive.
      * exact: PolR.ex_derive_horner.
      rewrite Derive_pow; try by auto_derive.
      rewrite Derive_plus; try by auto_derive.
      rewrite Derive_const ?Rplus_0_l.
      rewrite Derive_mult; try by auto_derive.
      rewrite Derive_id.
      rewrite PolR.Derive_horner.
      rewrite -{1}(Rmult_1_r (qk^`().[x])) -Rmult_plus_distr_l.
      rewrite SuccNat2Pos.id_succ.
      rewrite -addnE addn1 Rmult_1_r Rmult_1_l; simpl predn.
      (* Now, some reals' bookkeeping *)
      rewrite -mul2n (fact_simpl k.+1) 2!mult_INR -[INR 2]/2%R.
      rewrite -pow_mult multE muln2 -addnn addSnnS pow_add.
      have ->: (((1 + x * x) ^ k.+1) = (1 + x ^ 2) * (1 + x * x) ^ k)%R by rewrite /= Rmult_1_r.
      change eq with (@eq R); field.
      repeat first [ split | exact: INR_fact_neq_0 | exact: not_0_INR | apply pow_nonzero, Rsqr_plus1_neq0 ].
  }
constructor.
- by move=> *; rewrite PolR.size_grec1 Pol.size_grec1.
- { move => {X0 X n Hsubset Hex} X0 xi0 n Hx.
    apply: Pol.grec1_correct =>//.
    + move=> qi q m Hq.
      by repeat first [apply: Pol.div_mixed_r_correct|
                       apply: Pol.sub_correct|
                       apply: Pol.add_correct|
                       apply: Pol.deriv_correct|
                       apply: Pol.lift_correct|
                       apply: Pol.mul_mixed_correct|
                       apply: R_from_nat_correct].
    + move=> qi q m Hq.
      by repeat first [apply: J.div_correct|
                       apply: J.power_int_correct|
                       apply: Pol.horner_correct|
                       apply: J.add_correct|
                       apply: J.sqr_correct|
                       apply: I.fromZ_correct|
                       apply: Pol.one_correct].
    + exact: Pol.one_correct.
    + move=> [/=|k]; last by rewrite /PolR.nth !nth_default //; apply: J.zero_correct.
      exact: J.atan_correct.
  }
- done.
- by move=> m x Hx; apply: ex_derive_n_is_derive_n (is_derive_n_atan m x).
Qed.

Definition TM_tan (X0 X : I.type) (n : nat) : rpa :=
  let P := (T_tan prec X0 n) in
  let ic := I.cos prec X in
  if apart0 ic
  then RPA P (Ztech (T_tan prec) P (I.tan prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_tan (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_tan X0 X n)) = n.+1.
Proof. by rewrite /TM_tan; case: apart0; rewrite Pol.size_grec1. Qed.

Lemma TM_tan_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_tan X0 X n) Xtan'.
Proof.
move=> Hsubset Hex.
rewrite /TM_tan.
case E0: apart0.

apply i_validTM_Ztech with (TR.T_tan tt); last 2 first =>//.
exact: I.tan_correct.

constructor.
- by move=> ? ?; rewrite PolR.size_grec1.
- { (* The proof of this goal might be shortened by reusing is_derive_n_tan *)
    move=> {X0 n Hsubset Hex} x n k Hx H;
    rewrite /TR.T_tan /PolR.nth /PolR.grec1
      (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
      nth_grec1up_last.
    have->: Derive_n (fun t => proj_val (Xtan' t)) k x = Derive_n tan k x.
      apply: (@Derive_n_ext_loc _ tan).
      have Hdef : cos x <> 0%R.
        move/apart0_correct in E0.
        by apply: E0; apply: J.cos_correct.
      eapply locally_open with
        (1 := open_comp cos (fun y => y <> 0%R)
          (fun y _ => continuous_cos y)
        (open_neq R0)) (3 := Hdef).
      move=> {Hdef Hx x} x Hdef.
      by rewrite /Xtan' zeroF.
    rewrite last_grec1up // head_gloop1.
    rewrite [size _]/= subn0.
    have Hdef : cos x <> 0%R.
      move/apart0_correct in E0.
      by apply: E0; apply: J.cos_correct.
    elim: k H x {Hx} Hdef =>[|k IHk] H x Hdef.
    + by rewrite /= !Rsimpl.
    + move/ltnW in H; move/(_ H) in IHk.
      rewrite [INR]lock [PolR.lift]lock [fact]lock /= -!lock.
      set qk := iteri k
        (fun i c => PolR.div_mixed_r tt _ (INR (i + 0).+1)) (PolR.lift 1 PolR.one) in IHk *.
      rewrite (@Derive_ext_loc _ (fun x => qk.[tan x] * INR (fact k))%R);
        first last.
        eapply locally_open with
          (1 := open_comp cos (fun y => y <> 0%R)
            (fun y _ => continuous_cos y)
          (open_neq 0%R)) (3 := Hdef).
        move=> t Hdef'; move/(_ t Hdef') in IHk.
        rewrite IHk /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r //.
        exact: INR_fact_neq_0.
      clear IHk.
      rewrite PolR.horner_div_mixed_r.
      rewrite PolR.horner_add addn0.
      rewrite !PolR.horner_lift Derive_scal_l.
      rewrite Derive_comp; first last.
      * by eexists; apply: is_derive_tan.
      * exact: PolR.ex_derive_horner.
      rewrite !PolR.Derive_horner.
      rewrite (is_derive_unique _ _ _ (is_derive_tan _ Hdef)).
      rewrite /Rdiv Rmult_assoc.
      rewrite -simpl_fact Rinv_involutive.
      change eq with (@eq R); ring.
      exact: INR_fact_neq_0.
    }
constructor.
- by move=> *; rewrite PolR.size_grec1 Pol.size_grec1.
- { move => {X0 X n Hsubset Hex E0} X0 xi0 n Hx.
    apply: Pol.grec1_correct =>//.
    + move=> qi q m Hq.
      by repeat first [apply: Pol.div_mixed_r_correct|
                       apply: Pol.sub_correct|
                       apply: Pol.add_correct|
                       apply: Pol.deriv_correct|
                       apply: Pol.lift_correct|
                       apply: Pol.mul_mixed_correct|
                       apply: R_from_nat_correct].
    + move=> qi q m Hq.
      by repeat first [apply: J.div_correct|
                       apply: J.power_int_correct|
                       apply: Pol.horner_correct|
                       apply: J.add_correct|
                       apply: J.sqr_correct|
                       apply: I.fromZ_correct|
                       apply: Pol.one_correct|
                       apply: J.tan_correct].
    + apply: Pol.lift_correct; exact: Pol.one_correct.
    + move=> [/=|k]; rewrite /PolR.nth ?nth_default //; exact: J.zero_correct.
  }
- { move => {X0 X n Hsubset Hex E0} X x Hx Dx n k Hk.
    apply/Pol.grec1_propagate =>//.
      move=> q _.
      apply/Pol.horner_propagate/contains_Xnan.
      rewrite -Dx.
      exact: I.tan_correct Hx.
    by rewrite Pol.size_grec1.
  }
- move=> m x Hx.
  have {E0} E0: cos x <> R0.
    apply: apart0_correct E0.
    exact: J.cos_correct.
  eapply (@ex_derive_n_ext_loc tan); last first.
    exact: ex_derive_n_is_derive_n (is_derive_n_tan m x E0).
  eapply locally_open with
    (1 := open_comp cos (fun y => y <> 0%R)
      (fun y _ => continuous_cos y)
    (open_neq 0%R)) (3 := E0).
  move => /= x0 Hx0.
  by rewrite /Xtan' zeroF.

simpl.
split =>//.
by move=> *; apply I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_tan tt x0 n); last by rewrite I.nai_correct.
apply: Pol.grec1_correct;
  by repeat first [move=> *; apply: Pol.div_mixed_r_correct
                  |apply: Pol.add_correct
                  |apply: Pol.deriv_correct
                  |apply: Pol.lift_correct
                  |apply: Pol.deriv_correct
                  |apply: R_from_nat_correct
                  |move=> *; apply: Pol.horner_correct
                  |apply: J.tan_correct
                  |apply: Pol.lift_correct
                  |apply: Pol.one_correct
                  |move=> [|k]; rewrite /PolR.nth ?nth_default //; exact: J.zero_correct
                  ].
Qed.

(*
Definition Ztech_sqrt prec P X0 X :=
  let F := I.sqrt prec in
  let a := I.lower X in let b := I.upper X in
  let A := I.bnd a a in let B := I.bnd b b in
  (* If need be, we could replace Pol.horner with Bnd.ComputeBound *)
  let Da := I.sub prec (F A) (Pol.horner prec P (I.sub prec A X0)) in
  let Db := I.sub prec (F B) (Pol.horner prec P (I.sub prec B X0)) in
  let Dx0 := I.sub prec (F X0) (Pol.nth P 0) (* :-D *) in
  I.join (I.join Da Db) Dx0.
*)

Definition TM_sqrt (X0 X : I.type) (n : nat) : rpa :=
  (* assuming X0 \subset X *)
  let P := (T_sqrt prec X0 n) in
  if gt0 X
  then RPA P (Ztech (T_sqrt prec) P (I.sqrt prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_sqrt (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_sqrt X0 X n)) = n.+1.
Proof.
by rewrite /TM_sqrt;
  case: gt0; rewrite Pol.size_rec1.
Qed.

Lemma TM_sqrt_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sqrt X0 X n) Xsqrt'.
Proof.
move=> Hsubset Hex.
rewrite /TM_sqrt.
case E1: gt0.

apply i_validTM_Ztech with (TR.T_sqrt tt); last 2 first =>//.
exact: I.sqrt_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ sqrt); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E1].
      by move=> y Hy; rewrite /Xsqrt' negativeF //; apply: Rlt_le.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.sqrt_rec.
      have gt0_x : (0 < x)%R by move/(gt0_correct Hx) in E1.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_sqrt _ _ gt0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%R]_(i < k) _.
      simpl (Rmul_monoid _ _).
      rewrite fact_simpl mult_INR !addn1.
      have->: (/2 - INR k.+1 = /2 - INR k + (- 1))%R
        by rewrite -addn1 plus_INR /=; ring.
      rewrite Rpower_plus Rpower_Ropp Rpower_1 // /Rdiv.
      have->: ((/ 2 - INR k) = (INR 1 - INR 2 * INR k.+1.-1) / INR 2)%R
        by simpl; field.
      move/(gt0_correct Hx)/Rgt_not_eq in E1.
      change eq with (@eq R); field.
      repeat first [exact E1 | split | exact: INR_fact_neq_0 | exact: not_0_INR ].
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex E1} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
    by move=> *;
      repeat first [apply: J.div_correct
                   |apply: J.mul_correct
                   |apply: J.sub_correct
                   |apply: I.fromZ_correct
                   |apply: J.mul_correct
                   |apply: I.fromZ_correct
                   |apply: R_from_nat_correct
                   ].
    exact: J.sqrt_correct.
  }
- move=> I r Ir /= {E1 Hex Hsubset X X0 n}.
  unfold Xsqrt'.
  case: ifP=> // neg_r _ m k leqmk.
  apply: Pol.rec1_propagate; last by rewrite Pol.size_rec1.
  * move=> qi n Hq. rewrite /sqrt_rec.
    rewrite I.div_propagate_l // I.mul_propagate_r //; exact:eqNaiP.
  * apply/contains_Xnan.
    suff <- : Xsqrt (Xreal r) = Xnan by apply: I.sqrt_correct.
    by rewrite /Xsqrt' /= neg_r.
- { clear - E1.
    move=> n x Hx.
    move/(gt0_correct Hx) in E1.
    apply: (ex_derive_n_ext_loc sqrt).
      apply: locally_open E1; first exact: open_gt.
      simpl=> y Hy; rewrite /Xsqrt' negativeF //.
      exact: Rlt_le.
    exact: ex_derive_n_is_derive_n (is_derive_n_sqrt n x E1).
  }

simpl.
split =>//.
by move=> *; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_sqrt tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: J.div_correct
               |apply: J.mul_correct
               |apply: J.sub_correct
               |apply: I.fromZ_correct
               |apply: J.mul_correct
               |apply: I.fromZ_correct
               |apply: R_from_nat_correct
               ].
exact: J.sqrt_correct.
by rewrite I.nai_correct.
Qed.

Definition I_invsqrt prec x := I.inv prec (I.sqrt prec x).

Definition TM_invsqrt (X0 X : I.type) (n : nat) : rpa :=
  (* assuming X0 \subset X *)
  let P := (T_invsqrt prec X0 n) in
  if gt0 X
  then RPA P (Ztech (T_invsqrt prec) P (I_invsqrt prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_invsqrt (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_invsqrt X0 X n)) = n.+1.
Proof. by rewrite /TM_invsqrt; case: gt0; rewrite Pol.size_rec1. Qed.

Ltac Inc :=
  rewrite (*?*) INR_IZR_INZ;
  apply: I.fromZ_correct.

Lemma TM_invsqrt_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_invsqrt X0 X n)
            (fun x => Xinv (Xsqrt (Xreal x))).
Proof.
move=> Hsubset Hex.
rewrite /TM_invsqrt.
case E1: gt0.

apply i_validTM_Ztech with (TR.T_invsqrt tt); last 2 first =>//.
move=> Y y Hy.
replace (Xbind _ y) with (Xinv (Xsqrt y)) by now case y.
apply: I.inv_correct; exact: I.sqrt_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ (fun t => / sqrt t)); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E1].
      move=> y Hy.
      rewrite /Xinv' /Xsqrt' /= negativeF /= ?zeroF //.
      now apply Rgt_not_eq, sqrt_lt_R0.
      exact: Rlt_le.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.invsqrt_rec.
      have gt0_x : (0 < x)%R by move/(gt0_correct Hx) in E1.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_invsqrt _ _ gt0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%R]_(i < k) _.
      simpl (Rmul_monoid _ _).
      rewrite fact_simpl mult_INR !addn1.
      have->: (-/2 - INR k.+1 = -/2 - INR k + (- 1))%R
        by rewrite -addn1 plus_INR /=; ring.
      rewrite Rpower_plus Rpower_Ropp Rpower_1 // /Rdiv.
      have->: (-/ 2 - INR k = - (INR 1 + INR 2 * INR k.+1.-1) / INR 2)%R
        by simpl; field.
      move/(gt0_correct Hx)/Rgt_not_eq in E1.
      change eq with (@eq R); field.
      repeat first [exact E1 | split | exact: INR_fact_neq_0 | exact: not_0_INR ].
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex E1} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
by move=> *;
  repeat first [apply: J.div_correct
               |apply: J.mul_correct
               |apply: J.sub_correct
               |apply: I.fromZ_correct
               |apply: J.mul_correct
               |apply: I.fromZ_correct
               |apply/eqNaiPy: R_from_nat_correct
               |apply: J.add_correct
               |apply: J.neg_correct
               |Inc
               ].
    apply: J.inv_correct; exact: J.sqrt_correct.
  }
- move=> I r Ir {X0 X n Hsubset Hex E1} Dx n k Hkn.
  apply: Pol.rec1_propagate.
  - move=> q m Hq; rewrite /invsqrt_rec.
    rewrite I.div_propagate_l //.
    rewrite I.mul_propagate_r //; exact:eqNaiP.
  - apply/contains_Xnan; rewrite -Dx.
    exact/I.inv_correct/I.sqrt_correct.
    by rewrite Pol.size_rec1.
- { clear - E1.
    move=> n x Hx.
    move/(gt0_correct Hx) in E1.
    apply: (ex_derive_n_ext_loc (fun t => / sqrt t)).
      apply: locally_open E1; first exact: open_gt.
      simpl=> y Hy; rewrite /Xsqrt' /Xinv' /Xbind negativeF ?zeroF //.
      apply: Rgt_not_eq; exact: sqrt_lt_R0.
      exact: Rlt_le.
    exact: ex_derive_n_is_derive_n (is_derive_n_invsqrt n x E1).
  }

constructor =>//.
by move=> *; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_invsqrt tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: J.div_correct
               |apply: J.mul_correct
               |apply: J.sub_correct
               |apply: I.fromZ_correct
               |apply: J.mul_correct
               |apply: I.fromZ_correct
               |apply/eqNaiPy: R_from_nat_correct
               |apply: J.add_correct
               |apply: J.neg_correct
               |Inc
               ].
by apply: J.inv_correct; apply: J.sqrt_correct.
by rewrite I.nai_correct.
Qed.

Definition TM_power_int (p : Z) (X0 X : I.type) (n : nat) :=
  let P := (T_power_int prec p X0 n) in
  if p is Z.neg _ then
    if apart0 X then
      RPA P (Ztech (T_power_int prec p) P
                   (fun x => I.power_int prec x p) X0 X n)
    else RPA P I.nai
  else RPA P (Ztech (T_power_int prec p) P
                    (fun x => I.power_int prec x p) X0 X n).

Lemma size_TM_power_int (p : Z) (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_power_int p X0 X n)) = n.+1.
Proof.
rewrite /TM_power_int.
case: p => [|p|p]; last case: apart0;
  by rewrite (@Pol.size_dotmuldiv (n.+1)) ?(Pol.size_rec1, size_rec1up).
Qed.

Lemma toR_power_int p x : (0 <= p)%Z \/ x <> R0 ->
  powerRZ x p = proj_val (Xpower_int' x p).
Proof.
case => [Hp|Hx].
  by case: p Hp =>// p [].
by case: p =>//; rewrite /Xpower_int' zeroF.
Qed.

Lemma toR_power_int_loc p x : (0 <= p)%Z \/ x <> R0 ->
  locally x (fun t => powerRZ t p = proj_val (Xpower_int' t p)).
Proof.
case: p => [|p|p] Hx.
- eapply (locally_open (fun _ => True)) =>//; exact: open_true.
- eapply (locally_open (fun _ => True)) =>//; exact: open_true.
- eapply (@locally_open _ (fun x => x <> 0)%R) =>//; first exact: open_neq.
  by move => {x Hx} x Hx; rewrite /= zeroF.
  case: Hx => // ; by case.
Qed.

Lemma TM_power_int_correct_aux (p : Z) (X0 X : I.type) n :
  (0 <= p)%Z \/ apart0 X ->
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (let P := (T_power_int prec p X0 n) in
                                          RPA P (Ztech
                                                   (T_power_int prec p) P
                                                   (fun x => I.power_int prec x p)
                                                   X0 X n))
            (fun x => Xpower_int' x p).
Proof.
move=> Hyp Hsubset Hex.
apply i_validTM_Ztech with (TR.T_power_int tt p); last 2 first =>//.
exact: I.power_int_correct.
constructor.
- by move=> {n} ? n;
    rewrite ?(@PolR.size_dotmuldiv n.+1, @Pol.size_dotmuldiv n.+1,
    Pol.size_rec1, size_rec1up, PolR.size_rec1) //.
- { move=> x m k Hx Hk.
    rewrite /TR.T_power_int PolR.nth_dotmuldiv ifF; last first.
      rewrite PolR.size_rec1.
      rewrite size_falling_seq size_fact_seq.
      by rewrite !orbb ltnNge Hk.
    case: k Hk => [|k] Hk.
      simpl Derive_n; simpl INR; rewrite Rdiv_1.
      rewrite falling_seq_correct // fact_seq_correct //.
      rewrite big_mkord big_ord0.
      rewrite [PolR.nth _ _]nth_rec1up /= Rdiv_1 Rmult_1_l.
      rewrite toR_power_int //.
      by case: Hyp => [Hyp|Hyp]; by [left|right; exact: apart0_correct Hyp].
    rewrite -(Derive_n_ext_loc _ _ k.+1 x (toR_power_int_loc _));
      last by case: Hyp => [Hyp|Hyp]; by [left|right; exact: apart0_correct Hyp].
    symmetry; apply: (Rmult_eq_reg_r (INR (fact k.+1))); last exact: INR_fact_neq_0.
    rewrite {1}/Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; last exact: INR_fact_neq_0.
    clear - Hyp Hk Hx.
    rewrite /powerRZ.
    case: p Hyp Hx =>[|p|p] Hyp Hx.
    - rewrite Derive_n_const.
      rewrite /PolR.nth /PolR.rec1 nth_rec1up ifF; last first.
        by apply: negbTE; rewrite ltnNge Hk.
      rewrite iteriS /TR.pow_aux_rec ifF ?(Rmult_0_r, Rmult_0_l) //.
      apply: negbTE; rewrite negb_or /=; apply/negP; move/Z.geb_le.
      by change Z0 with (Z.of_nat O); move/Nat2Z.inj_le/leP; rewrite addn1.
    - rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_pow _ _ _ _)); last first.
        exact/ltP/Pos2Nat.is_pos.
      rewrite falling_seq_correct // fact_seq_correct //.
      have Hpow: PolR.nth (PolR.rec1
        (TR.pow_aux_rec tt (Z.pos p) x) (x ^ Pos.to_nat p) m)%R k.+1 =
        if (Z.of_nat (k + 1) <=? Z.pos p)%Z then (x ^ (Pos.to_nat p - k.+1))%R
        else 0%R.
        rewrite /PolR.nth /PolR.rec1 nth_rec1up.
        rewrite ifF; last first.
          by apply: negbTE; rewrite ltnNge Hk.
        case: Z.leb_spec.
          move=> /Zle_is_le_bool Hpk; rewrite iteriS /TR.pow_aux_rec Z.geb_leb Hpk.
          rewrite orbT pow_powerRZ; congr powerRZ.
          rewrite Nat2Z.inj_sub ?(positive_nat_Z, addn1) //.
          apply/Nat2Z.inj_le; rewrite positive_nat_Z -addn1.
          by move: Hpk; case: Z.leb_spec.
        move=> Hpk; rewrite iteriS /TR.pow_aux_rec Z.geb_leb ifF //.
        apply: negbTE; rewrite negb_or /=.
        by rewrite -Z.ltb_antisym; move/Zlt_is_lt_bool in Hpk.
      case: (Z.leb_spec (Z.of_nat (k + 1)) (Z.pos p)) => Hpk.
        move/Zle_is_le_bool in Hpk.
        rewrite Hpow Hpk.
        rewrite /Rdiv; ring_simplify (*!*).
        rewrite -INR_IZR_INZ Rmult_assoc Rinv_l; last exact: INR_fact_neq_0.
        rewrite Rmult_1_r Rmult_comm; congr Rmult.
        rewrite (big_morph IZR (id1 := 1%R) (op1 := Rmult)) //; last exact: mult_IZR.
        rewrite big_mkord; apply: eq_bigr => [[i Hi] _].
        rewrite INR_IZR_INZ.
        rewrite Nat2Z.inj_sub ?(positive_nat_Z, addn1) //=.
        apply/leP; rewrite ltnS in Hi.
        apply: leq_trans Hi _.
        move/Zle_is_le_bool in Hpk.
        rewrite -positive_nat_Z in Hpk; move/Nat2Z.inj_le/leP in Hpk.
        by apply: leq_trans _ Hpk; rewrite addn1.
      rewrite [in LHS]big_ord_recr big_mkord [in RHS]big_ord_recr.
      simpl (Rmul_monoid _ _).
      have->: Pos.to_nat p - k = 0.
        rewrite -positive_nat_Z addn1 in Hpk; move/Nat2Z.inj_lt/ltP in Hpk.
        rewrite ltnS in Hpk.
        by apply/eqP; rewrite subn_eq0.
      rewrite !Rsimpl Hpow ifF ?Rsimpl //.
      apply: negbTE.
      by move/Zlt_is_lt_bool: Hpk; rewrite Z.ltb_antisym =>->.
    - rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_inv_pow _ _ _ _ _)); first last.
        case: Hyp; first case =>//.
        by move/apart0_correct; apply.
        exact/ltP/Pos2Nat.is_pos.
      rewrite falling_seq_correct // fact_seq_correct //.
      have Hpow: PolR.nth (PolR.rec1
        (TR.pow_aux_rec tt (Z.neg p) x) (/ x ^ Pos.to_nat p) m)%R k.+1 =
        (/ x ^ (Pos.to_nat p + k.+1))%R.
        rewrite /PolR.nth /PolR.rec1 nth_rec1up.
        rewrite ifF; last first.
          by apply: negbTE; rewrite ltnNge Hk.
        rewrite iteriS /TR.pow_aux_rec addn1 /= Pos.of_nat_succ.
        by rewrite Pos2Nat.inj_add Nat2Pos.id.
      rewrite Hpow.
      rewrite /Rdiv; ring_simplify (*!*).
      rewrite -INR_IZR_INZ Rmult_assoc Rinv_l; last exact: INR_fact_neq_0.
      rewrite Rmult_1_r Rmult_comm; congr Rmult.
      rewrite (big_morph IZR (id1 := 1%R) (op1 := Rmult)) //; last exact: mult_IZR.
      rewrite big_mkord; apply: eq_bigr => [[i Hi] _].
      rewrite INR_IZR_INZ -opp_IZR; congr IZR.
      rewrite Nat2Z.inj_add positive_nat_Z.
      by rewrite Z.opp_add_distr.
  }
constructor.
- by move=> {n} ? ? n;
    rewrite ?(@PolR.size_dotmuldiv n.+1, @Pol.size_dotmuldiv n.+1,
      Pol.size_rec1, size_rec1up, PolR.size_rec1) //.
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    unfold T_power_int, TR.T_power_int.
    apply: Pol.dotmuldiv_correct.
    by rewrite size_falling_seq size_fact_seq.
    apply: Pol.rec1_correct =>//.
    + rewrite /pow_aux_rec /TR.pow_aux_rec; move=> _ _ m _.
      case: ifP => H.
      exact: J.power_int_correct.
      apply I.mask_correct', J.zero_correct.
    + exact: J.power_int_correct.
  }
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk.
    rewrite /T_power_int.
    apply: Pol.dotmuldiv_propagate; last 1 first.
    rewrite (@Pol.size_dotmuldiv n.+1) //.
    by rewrite Pol.size_rec1.
    by rewrite size_falling_seq.
    by rewrite size_fact_seq.
    by rewrite Pol.size_rec1 size_falling_seq.
    by rewrite Pol.size_rec1 size_fact_seq.
    apply: Pol.rec1_propagate.
    move=> y m _.
    rewrite /pow_aux_rec ifT.
    apply/contains_Xnan.
    have->: Xnan = Xpower_int^~ (p - Z.of_nat m)%Z (Xreal x).
    move: Dx; rewrite /Xpower_int /Xpower_int' /Xbind.
    by case Ep: p =>//; case: is_zero =>//; case: m.
    exact: I.power_int_correct.
    match goal with |- is_true ?a => rewrite -(negbK a) negb_or end.
    apply/negP; case/andP => /negbTE H0 /negbTE Hm.
    move: Dx; rewrite /Xpower_int.
    by case: {Hyp} p H0 Hm.
    apply/contains_Xnan.
    rewrite -Dx.
    exact: I.power_int_correct Hx.
  }
- move=> k x Hx.
  have [Hp|/(apart0_correct Hx) Nx] := Hyp.
    apply: (ex_derive_n_ext_loc _ _ _ _ (@toR_power_int_loc p x _)).
    by left.
    by apply: ex_derive_n_powerRZ; left.
  apply: (ex_derive_n_ext_loc _ _ _ _ (@toR_power_int_loc p x _)).
  by right.
  by apply: ex_derive_n_powerRZ; right.
Qed.

Lemma TM_power_int_correct (p : Z) (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_power_int p X0 X n) (fun x => Xpower_int' x p).
Proof.
move=> Hsubs Hnex.
rewrite /TM_power_int.
case Ep: p => [|p'|p']; last case E0: apart0;
  try apply: TM_power_int_correct_aux; intuition.
constructor =>//.
by move=> *; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_power_int tt (Z.neg p') x0 n).
apply: Pol.dotmuldiv_correct.
by rewrite size_falling_seq size_fact_seq.
apply: Pol.rec1_correct.
rewrite /pow_aux_rec /TR.pow_aux_rec -Ep.
move=> ai a m Ha.
case: ((p <? 0) || (p >=? Z.of_nat m))%Z.
exact: J.power_int_correct.
apply I.mask_correct', J.zero_correct.
exact: J.power_int_correct.
by move=> x Hx; rewrite I.nai_correct.
Qed.

Definition TM_inv (X0 X : I.type) (n : nat) :=
  let P := (T_inv prec X0 n) in
  if apart0 X then
    RPA P (Ztech (T_inv prec) P (I.inv prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_inv (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_inv X0 X n)) = n.+1.
Proof. by rewrite /TM_inv; case: apart0 =>/=; rewrite Pol.size_rec1. Qed.

Lemma TM_inv_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_inv X0 X n) Xinv'.
Proof.
move=> Hsubset Hex.
rewrite /TM_inv /=.
case E0: apart0.

apply i_validTM_Ztech with (TR.T_inv tt); last 2 first =>//.
exact: I.inv_correct.
constructor.
- by move=> {n} ? n; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ Rinv); last first.
      apply: (locally_open (fun t => t <> 0)%R);
        [exact: open_neq| |exact: apart0_correct E0].
      by move=> y Hy; rewrite /Xinv' zeroF.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.inv_rec.
      have neq0_x : (x <> 0)%R by move/(apart0_correct Hx) in E0.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_inv _ _ neq0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%R]_(i < k) _.
      simpl (Rmul_monoid _).
      rewrite /Rdiv !Rmult_assoc; congr Rmult.
      rewrite fact_simpl mult_INR.
      rewrite !add1n -[(x ^ k.+2)%R]/(x * x ^ k.+1)%R.
      set Xk1 := (x ^ k.+1)%R.
      set k_ := INR (fact k).
      set k1 := INR k.+1.
      rewrite Rinv_mult_distr //; last exact: pow_nonzero.
      rewrite Rinv_mult_distr; try solve [exact: INR_fact_neq_0|exact: not_0_INR].
      rewrite !Rmult_assoc -Ropp_inv_permute //.
      have->: (- k1 * (/ x * (/ Xk1 * (/ k1 * / k_))))%R =
        ((k1 * / k1) * - (/ x * (/ Xk1 * (/ k_))))%R by ring.
      rewrite Rinv_r; last exact: not_0_INR.
      ring.
  }
constructor.
- by move=> {n} ? ? n; rewrite PolR.size_rec1 Pol.size_rec1.
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    apply: Pol.rec1_correct; last exact: J.inv_correct.
    move=> ai a m Ha; apply: J.div_correct =>//.
    exact: J.neg_correct.
  }
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk.
    apply/Pol.rec1_propagate =>//.
    - move=> q m Hqm; apply/contains_Xnan; rewrite /inv_rec.
      by rewrite I.div_propagate_l.
    - apply/contains_Xnan.
      rewrite -Dx.
      exact: (I.inv_correct _ _ (Xreal x)).
    - by rewrite Pol.size_rec1.
  }
- { move=> {X0 n Hsubset Hex} n x Hx.
    move/(apart0_correct Hx) in E0.
    apply: (ex_derive_n_ext_loc Rinv).
      apply: (locally_open (fun t => t <> 0)%R) =>//.
      exact: open_neq.
      by simpl=> y Hy; rewrite /Xinv' zeroF.
    exact: ex_derive_n_is_derive_n (is_derive_n_inv n x E0).
  }

split =>//.
by move=> *; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_inv tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: J.div_correct
               |apply: J.inv_correct
               |apply: J.neg_correct
               ].
exact: J.inv_correct.
by rewrite I.nai_correct.
Qed.

Definition TM_ln (X0 X : I.type) (n : nat) : rpa :=
  let P := (T_ln prec X0 n) in
  if gt0 X then
    RPA P (Ztech (T_ln prec) P (I.ln prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_ln (X0 X : I.type) (n : nat) :
  Pol.size (approx (TM_ln X0 X n)) = n.+1.
Proof.
by rewrite /TM_ln; case: gt0; case: n => [|n] /=; rewrite !sizes
  ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1, size_rec1up, size_behead).
Qed.

Lemma powerRZ_opp x n :
  x <> 0%R -> powerRZ x (- n) = / (powerRZ x n).
Proof.
move=> Hx.
case: n =>[|p|p] //; first by rewrite Rinv_1.
rewrite Rinv_involutive //.
exact: pow_nonzero.
Qed.

Lemma TM_ln_correct (X0 X : I.type) n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_ln X0 X n) Xln'.
Proof.
move=> Hsubset Hex.
rewrite /TM_ln.
case E0: gt0.

apply i_validTM_Ztech with (TR.T_ln tt); last 2 first =>//.
exact: I.ln_correct.
constructor.
- by move=> {n} x [|n]; rewrite /TR.T_ln // !sizes
    ?(@PolR.size_dotmuldiv n.+1, PolR.size_rec1, size_rec1up, size_behead).
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ ln); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E0].
      by move=> y Hy; rewrite /Xln' positiveT.
      rewrite /PolR.nth; case: k Hkn => [|k] Hkn; first by rewrite Rdiv_1.
      case: n Hkn => [|n] Hkn //.
      rewrite [nth _ _ _]PolR.nth_dotmuldiv ifF; last first.
      rewrite PolR.size_rec1.
      rewrite size_falling_seq size_behead size_fact_seq.
      by rewrite !orbb ltnNge -ltnS Hkn.
    move/(gt0_correct Hx) in E0.
    case: k Hkn => [|k] Hkn.
      simpl Derive_n; simpl INR; rewrite Rdiv_1.
      rewrite falling_seq_correct // nth_behead fact_seq_correct //.
      rewrite big_mkord big_ord0.
      rewrite [PolR.nth _ _]nth_rec1up /= Rdiv_1 Rmult_1_l.
      by rewrite (is_derive_unique _ _ _ (is_derive_ln _ E0)) Rmult_1_r.
    symmetry; apply: (Rmult_eq_reg_r (INR (fact k.+2))); last exact: INR_fact_neq_0.
    rewrite {1}/Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; last exact: INR_fact_neq_0.
    rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_ln _ _ _)) //.
    rewrite falling_seq_correct // nth_behead fact_seq_correct //.
    have Hpow: (PolR.nth (PolR.rec1
      (TR.pow_aux_rec tt (-1) x) (powerRZ x (-1)) n)%R k.+1 =
      / x ^ (1 + k.+1))%R.
      rewrite /PolR.nth /PolR.rec1 nth_rec1up.
      rewrite ifF; last first.
        by apply: negbTE; rewrite ltnNge -ltnS Hkn.
      rewrite iteriS /TR.pow_aux_rec.
      suff->: powerRZ x (-1 - Z.of_nat (k + 1))%Z = / (x ^ (1 + k.+1))%R by done.
        rewrite pow_powerRZ -powerRZ_opp; last exact: Rgt_not_eq.
        congr powerRZ; change (-1)%Z with (- Z.of_nat 1)%Z.
        rewrite -Z.add_opp_r -Z.opp_sub_distr -Z.add_opp_r Z.opp_involutive.
        by f_equal; rewrite -Nat2Z.inj_add; f_equal; rewrite plusE addn1.
    rewrite Hpow big_mkord.
    rewrite -INR_IZR_INZ /Rdiv Rmult_assoc.
    rewrite (big_morph IZR (id1 := 1%R) (op1 := Rmult)) //; last exact: mult_IZR.
    set bigRhs := \big[Rmult/1%R]_i IZR _.
    set fk2 := INR (fact k.+2).
    have->: (bigRhs * / fk2 * (/ x ^ (1 + k.+1) * fk2) =
      (/ fk2 * fk2) * bigRhs * / (x ^ (1 + k.+1)))%R by ring.
    rewrite Rinv_l ?Rmult_1_l; last exact: INR_fact_neq_0.
    congr Rmult; rewrite {}/bigRhs.
    apply: eq_bigr => [[i Hi] _].
    rewrite INR_IZR_INZ.
    rewrite Nat2Z.inj_add -opp_IZR; congr IZR.
    simpl Z.of_nat.
    by rewrite Z.opp_add_distr.
  }
constructor.
- by move=> {n X Hsubset E0} X x [|n]; rewrite /TR.T_ln !sizes //=
    ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
      @PolR.size_dotmuldiv n.+1, PolR.size_rec1, size_rec1up, size_behead).
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    rewrite /T_ln /TR.T_ln.
    apply: Pol.polyCons_correct; last exact: J.ln_correct.
    case: n => [|n]; first exact: Pol.polyNil_correct.
    apply: Pol.dotmuldiv_correct;
      first by rewrite size_falling_seq size_behead size_fact_seq.
    apply: Pol.rec1_correct; first move=> *;
      repeat first [apply: J.div_correct
                   |apply: J.power_int_correct
                   |apply: J.ln_correct
                   ];
      exact: I.mask_correct'.
  }
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk.
    apply: Pol.polyCons_propagate.
    - apply/contains_Xnan.
      rewrite -Dx.
      exact: I.ln_correct Hx.
    - case: n Hk => [|n] Hk m; first by rewrite Pol.size_polyNil.
      rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq) //.
      move=> Hm.
      apply: Pol.dotmuldiv_propagate;
      rewrite ?(size_falling_seq, size_behead, size_fact_seq) ?Pol.size_rec1 //.
      apply: Pol.rec1_propagate.
      move=> q l Hq.
      apply J.power_int_propagate, I.mask_propagate_r, contains_Xnan.
      by rewrite -Dx; apply: I.ln_correct Hx.
      apply J.power_int_propagate, I.mask_propagate_r, contains_Xnan.
      by rewrite -Dx; apply: I.ln_correct Hx.
      by rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq).
    - rewrite Pol.size_polyCons.
      case: n Hk => [|n] Hk; first by rewrite ltnS Pol.size_polyNil.
      by rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq).
  }
- { clear - E0.
    move=> n x Hx.
    move/(gt0_correct Hx) in E0.
    apply: (ex_derive_n_ext_loc ln).
      apply: locally_open E0; first exact: open_gt.
      by simpl=> t Ht; rewrite /Xln' positiveT.
    exact: ex_derive_n_is_derive_n (is_derive_n_ln n x E0).
  }
split =>//.
by move=> *; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_ln tt x0 n).
apply: Pol.polyCons_correct; case: n =>[|n]/=; first exact: Pol.polyNil_correct.
- apply: Pol.dotmuldiv_correct;
    first by rewrite size_falling_seq size_behead size_fact_seq.
  apply: Pol.rec1_correct; first move=> *;
    repeat first [apply: J.div_correct
                 |apply: J.power_int_correct
                 |apply: J.ln_correct
                 ];
    exact: I.mask_correct'.
- exact: J.ln_correct.
- exact: J.ln_correct.
by rewrite I.nai_correct.
Qed.

(******************************************************************************)
(** The rest of the file is devoted to arithmetic operations on Taylor models *)
(******************************************************************************)

Local Notation "a + b" := (Xadd a b).
Local Notation "a - b" := (Xsub a b).

Lemma TM_add_correct (X0 X : interval) (TMf TMg : rpa) f g :
  i_validTM X0 X TMf f ->
  i_validTM X0 X TMg g ->
  i_validTM X0 X (TM_add TMf TMg)
    (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> [Fdef Fnai Fzero Fsubs Fmain] [Gdef Gnai Gzero Gsubs Gmain].
have HL :
   forall x : R,
     contains X (Xreal x) ->
     Xadd (f x) (g x) = Xnan -> I.convert (I.add prec (error TMf) (error TMg)) = IInan.
  move=> x Hx.
  case Ef: (f x) => [|fx].
  rewrite I.add_propagate_l //; exact: Fdef Ef.
  case Eg: (g x) => [|gx //].
  rewrite I.add_propagate_r //; exact: Gdef Eg.
split=>//=.
by move=> H; move/(_ H) in Fnai; rewrite I.add_propagate_l.
rewrite -(Rplus_0_l 0).
exact: J.add_correct.
move=> x0 Hx0 /=; move: (Fmain x0 Hx0) (Gmain x0 Hx0) => [pf Hf1 Hf2] [pg Hg1 Hg2].
exists (PolR.add tt pf pg); first exact: Pol.add_correct.
move=> x Hx /=.
rewrite PolR.horner_add.
case E0: (I.convert (I.add prec _ _)) {HL} (HL x Hx) => [|zl zu] //.
set pfx := pf.[_]; set pgx := pg.[_].
case Ef: f => [|fx]. by move => ->.
case Eg: g => [|gx]. by move => ->.
intros _.
rewrite /proj_val /Xbind2 -E0.
replace (fx + gx - (pfx + pgx))%R with ((fx - pfx) + (gx - pgx))%R by ring.
apply: J.add_correct.
rewrite -[fx](f_equal proj_val Ef).
exact: Hf2.
rewrite -[gx](f_equal proj_val Eg).
exact: Hg2.
Qed.

Lemma TM_opp_correct (X0 X : interval) (TMf : rpa) f :
  i_validTM X0 X TMf f ->
  i_validTM X0 X (TM_opp TMf)
    (fun xr => Xneg (f xr)).
Proof.
move=> [Hdef Hnai Hzero Hsubset /= Hmain].
have HL :
  forall x : R,
    contains X (Xreal x) ->
    Xneg (f x) = Xnan -> I.convert (I.neg (error TMf)) = IInan.
  move=> x Hx Dx.
  apply J.neg_propagate, (Hdef x Hx).
  by case: (f x) Dx.
split=>//.
  by move=> HX; rewrite J.neg_propagate // Hnai.
  rewrite -Ropp_0.
  exact: J.neg_correct.
simpl=> x0 Hx0.
move/(_ x0 Hx0) in Hmain.
have [Q H1 H2] := Hmain.
exists (PolR.opp Q); first exact: Pol.opp_correct.
move=> x Hx.
rewrite PolR.horner_opp.
case Efx: (f x) (H2 x Hx) => [|fx] /=.
rewrite /Rminus 2!Rplus_0_l.
exact: J.neg_correct.
replace (- fx - - Q.[x - x0])%R with (-(fx - Q.[x - x0]))%R by ring.
exact: J.neg_correct.
Qed.

Lemma TM_sub_correct (X0 X : interval) (TMf TMg : rpa) f g :
  i_validTM X0 X TMf f ->
  i_validTM X0 X TMg g ->
  i_validTM X0 X (TM_sub TMf TMg)
    (fun xr => Xsub (f xr) (g xr)).
Proof.
move=> [Fdef Fnai Fzero Hsubset /= Fmain] [Gdef Gnai Gzero _ /= Gmain].
have HL :
  forall x : R,
    contains X (Xreal x) ->
    Xsub (f x) (g x) = Xnan -> I.convert (I.sub prec (error TMf) (error TMg)) = IInan.
  move=> x Hx.
  case Ef: (f x) => [|fx].
  rewrite I.sub_propagate_l //; exact: Fdef Ef.
  case Eg: (g x) => [|gx //].
  rewrite I.sub_propagate_r //; exact: Gdef Eg.
split=>//=.
  by move=> HX; rewrite I.sub_propagate_l // Fnai.
  suff->: Xreal 0 = (Xreal 0 - Xreal 0)%XR by apply: I.sub_correct.
  by rewrite /= Rminus_0_r.
move=> x0 Hx0 /=.
move: (Fmain x0 Hx0) (Gmain x0 Hx0) => [pf Hf1 Hf2] [pg Hg1 Hg2].
exists (PolR.sub tt pf pg); first exact: Pol.sub_correct.
move=> x Hx /=.
rewrite PolR.horner_sub.
case E0: (I.convert (I.sub prec _ _)) {HL} (HL x Hx) => [|zl zu] //.
set pfx := pf.[_]; set pgx := pg.[_].
case Ef: f => [|fx]. by move => ->.
case Eg: g => [|gx]. by move => ->.
intros _.
rewrite /Xbind2 /proj_val -E0.
replace (fx - gx - (pfx - pgx))%R with ((fx - pfx) - (gx - pgx))%R by ring.
apply: J.sub_correct.
move: (Hf2 x Hx).
by rewrite Ef.
move: (Hg2 x Hx).
by rewrite Eg.
Qed.

Definition TM_mul_mixed (a : I.type) (M : rpa) : rpa :=
  RPA (Pol.map (I.mul prec a) (approx M))
      (I.mul prec a (error M)).

Definition TM_div_mixed_r (M : rpa) (b : I.type) : rpa :=
  RPA (Pol.map (I.div prec ^~ b) (approx M))
      (I.div prec (error M) b).

Lemma size_TM_mul_mixed (a : I.type) M :
  Pol.size (approx (TM_mul_mixed a M)) = Pol.size (approx M).
Proof. by rewrite Pol.size_map. Qed.

Lemma size_TM_div_mixed_r M (b : I.type) :
  Pol.size (approx (TM_div_mixed_r M b)) = Pol.size (approx M).
Proof. by rewrite Pol.size_map. Qed.

Lemma TM_mul_mixed_correct (a : I.type) M (X0 X : interval) f (y : R) :
  a >: y ->
  i_validTM X0 X M f ->
  i_validTM X0 X (TM_mul_mixed a M)
    (fun x => Xmul (Xreal y) (f x)).
Proof.
move=> Hy [Hdef Hnai Hzero Hsubs Hmain].
split=>//.
  move=> x Hx Dx; apply/contains_Xnan.
  rewrite I.mul_propagate_r //.
  apply (Hdef x Hx).
  by case: (f x) Dx.
  by move=> HX; rewrite I.mul_propagate_r // Hnai.
  have->: (Xreal 0) = (Xmul (Xreal y) (Xreal 0)) by simpl; congr Xreal; ring.
  exact: I.mul_correct.
move=> x0 Hx0.
move/(_ x0 Hx0) in Hmain.
have [q H1 H2] := Hmain.
exists (PolR.map (Rmult y) q).
- apply: Pol.map_correct =>//.
  by rewrite Rmult_0_r.
  by move=> *; apply: J.mul_correct.
- move=> x Hx.
  move/(_ x Hx) in H2.
  rewrite PolR.horner_mul_mixed.
  case Dx: (f x) => [|fx].
  by rewrite I.mul_propagate_r // (Hdef x Hx Dx).
  rewrite /Xbind2 /proj_val.
  replace (y * fx - y * q.[x - x0])%R with (y * (fx - q.[x - x0]))%R by ring.
  rewrite Dx in H2.
  exact: J.mul_correct.
Qed.

Lemma TM_mul_mixed_nai (a : I.type) M f (X0 X : interval) :
  contains (I.convert a) Xnan ->
  i_validTM X0 X M f ->
  I.convert (error (TM_mul_mixed a M)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=> [Hnan Hsubst Hmain].
by rewrite I.mul_propagate_l.
Qed.

Corollary TM_mul_mixed_correct_strong (a : I.type) M (X0 X : interval) f g :
  not_empty X0 ->
  is_const f X (I.convert a) ->
  i_validTM X0 X M g ->
  i_validTM X0 X (TM_mul_mixed a M)
    (fun x => Xmul (f x) (g x)).
Proof.
move=> tHt [[|y] Hy1 Hy2] Hg; move: (Hg) => [Hdef Hnai Hnan Hsubset Hmain].
split=>//.
- move=> x Hx Dx.
  rewrite I.mul_propagate_l; exact/contains_Xnan.
- by rewrite (TM_mul_mixed_nai Hy1 Hg).
- by rewrite (TM_mul_mixed_nai Hy1 Hg).
- move=> /= x0 Hx0.
  move/(_ x0 Hx0) in Hmain.
  have [q H1 H2] := Hmain.
  exists (PolR.map (Rmult (* dummy *) R0) q).
    apply: Pol.map_correct =>//.
      by rewrite Rmult_0_r.
    move=> *; apply: J.mul_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  move/(_ x Hx) in H2.
  rewrite I.mul_propagate_l //.
  exact/contains_Xnan.
- apply: TM_fun_eq; last exact: TM_mul_mixed_correct Hy1 Hg.
  move=> x Hx /=.
  by rewrite Hy2.
Qed.

Lemma TM_div_mixed_r_aux0 M (b : I.type) (X0 X : interval) f :
  b >: 0%R ->
  i_validTM X0 X M f (* hyp maybe too strong *) ->
  i_validTM X0 X (TM_div_mixed_r M b)
    (fun x => Xdiv (f x) (Xreal 0)).
Proof.
move=> Hb0 [Hdef Hnai Hzero Hsubs /= Hmain].
have Lem : contains (I.convert (error (TM_div_mixed_r M b))) Xnan.
  rewrite /TM_div_mixed_r.
  simpl.
  rewrite -(Xdiv_0_r (Xreal R0)).
  exact: I.div_correct.
split=>//.
  by move=> x Hx Dx; apply/contains_Xnan.
  by rewrite (proj1 (contains_Xnan _) Lem).
  by rewrite (proj1 (contains_Xnan _) Lem).
move=> x0 Hx0; have [Q Happrox Herr] := Hmain x0 Hx0.
exists (PolR.map (Rdiv^~ 0)%R Q) =>/=.
apply: Pol.map_correct =>//; first by rewrite /Rdiv Rmult_0_l.
move=> *; exact: J.div_correct.
by move=> x Hx; move/contains_Xnan: Lem ->.
Qed.

Lemma TM_div_mixed_r_correct M (b : I.type) (X0 X : interval) f (y : R) :
  b >: y ->
  i_validTM X0 X M f ->
  i_validTM X0 X (TM_div_mixed_r M b)
    (fun x => Xdiv (f x) (Xreal y)).
Proof.
have [->|Hy0] := Req_dec y R0.
  exact: TM_div_mixed_r_aux0.
move=> Hy [Hdef Hnai Hzero Hsubs Hmain].
split=>//.
  move=> x Hx Dx; rewrite /TM_div_mixed_r /=.
  rewrite I.div_propagate_l //; apply/(Hdef x Hx).
  case: (f x) Dx => [|fx] //=.
  by rewrite /Xdiv' zeroF.
  by move=> HX; rewrite I.div_propagate_l // Hnai.
  have->: (Xreal 0) = (Xdiv (Xreal 0) (Xreal y)).
  by rewrite /Xdiv' /= zeroF // /Rdiv Rmult_0_l.
  exact: I.div_correct.
move=> /= x0 Hx0.
have [q H1 H2] := Hmain x0 Hx0.
exists (PolR.map (Rdiv ^~ y) q).
- apply: Pol.map_correct =>//.
  by rewrite /Rdiv Rmult_0_l.
  by move=> *; apply: J.div_correct.
- move=> x Hx /=.
  move/(_ x Hx) in H2.
  case Df: (f x) => [|fx].
  by rewrite I.div_propagate_l // (Hdef x Hx).
  clear - H2 Hy Hy0 Df Hdef Hx.
  rewrite PolR.horner_div_mixed_r /Xdiv' /Xbind2 zeroF // /proj_val.
  rewrite Df in H2.
  replace (fx / y - q.[x - x0] / y)%R with ((fx - q.[x - x0]) / y)%R by now field.
  exact: J.div_correct.
Qed.

Lemma TM_div_mixed_r_nai M (b : I.type) f (X0 X : interval) :
  contains (I.convert b) Xnan ->
  i_validTM X0 X M f ->
  I.convert (error (TM_div_mixed_r M b)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hdef Hnai Hnan Hsubst Hmain].
exact: I.div_propagate_r.
Qed.

Corollary TM_div_mixed_r_correct_strong M (b : I.type) (X0 X : interval) f g :
  not_empty X0 ->
  i_validTM X0 X M f ->
  is_const g X (I.convert b) ->
  i_validTM X0 X (TM_div_mixed_r M b)
    (fun x => Xdiv (f x) (g x)).
Proof.
move=> tHt Hf [[|y] Hy1 Hy2]; move: (Hf) => [Hdef Hnai Hzero Hsubs Hmain].
split=>//=.
- move=> x Hx Dx.
  rewrite I.div_propagate_r //; exact/contains_Xnan.
- by rewrite (TM_div_mixed_r_nai Hy1 Hf).
- by rewrite (TM_div_mixed_r_nai Hy1 Hf).
- move=> /= x0 Hx0.
  have [q H1 H2] := Hmain x0 Hx0.
  exists (PolR.map (Rdiv ^~ R0) q).
    apply: Pol.map_correct =>//.
    by rewrite /Rdiv Rmult_0_l.
    move=> *; apply: J.div_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  move/(_ x Hx) in H2.
  rewrite I.div_propagate_r //.
  exact/contains_Xnan.
apply: (@TM_fun_eq (fun x => f x / Xreal y)%XR).
- by move=> x Hx /=; rewrite Hy2.
- exact: TM_div_mixed_r_correct.
Qed.

Definition mul_error prec n (f g : rpa) (X0 X : I.type) :=
 let pf := approx f in
 let pg := approx g in
 let sx := (I.sub prec X X0) in
 let B := I.mul prec (Bnd.ComputeBound prec (Pol.mul_tail prec n pf pg) sx)
                (I.power_int prec sx (Z_of_nat n.+1)) in
 let Bf := Bnd.ComputeBound prec pf sx in
 let Bg := Bnd.ComputeBound prec pg sx in
   I.add prec B (I.add prec (I.mul prec (error f) Bg)
     (I.add prec (I.mul prec (error g) Bf)
       (I.mul prec (error f) (error g)))).

Definition TM_mul (Mf Mg : rpa) (X0 X : I.type) n : rpa :=
 RPA (Pol.mul_trunc prec n (approx Mf) (approx Mg))
     (mul_error prec n Mf Mg X0 X).

Lemma TM_mul_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul TMf TMg X0 X n)
    (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> [t Ht0] [Fdef Fnai Fzero HinX Fmain] [Gdef Gnai Gzero _ Gmain].
have Ht : X >: t by exact: HinX.
have Hf0 := Fmain t Ht0.
have Hg0 := Gmain t Ht0.
split =>//.
- move=> x Hx Dx.
  rewrite /= /mul_error.
  do 3![rewrite I.add_propagate_r //].
  case Ef: (f x) => [|fx].
    rewrite I.mul_propagate_l //; exact: Fdef Ef.
  case Eg: (g x) => [|gx //].
    rewrite I.mul_propagate_r //; exact: Gdef Eg.
  by rewrite Ef Eg in Dx.
- move=> HX; rewrite /TM_mul /= /mul_error.
  rewrite I.add_propagate_r // I.add_propagate_r // I.add_propagate_r //.
  by rewrite I.mul_propagate_l // Fnai.
- have [qf Hf1 Hf2] := Hf0.
  have [qg Hg1 Hg2] := Hg0.
  step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
  apply: J.add_correct.
    apply: (mul_0_contains_0_r _
      (y := (Xreal (PolR.mul_tail tt n qf qg).[t - t])));
      last first.
      apply: pow_contains_0 =>//.
      exact: subset_sub_contains_0 Ht0 HinX.
    apply: Bnd.ComputeBound_correct.
      exact: Pol.mul_tail_correct.
    exact: J.sub_correct.
  step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
  apply: J.add_correct.
    apply: (mul_0_contains_0_l _
      (y := (Xreal qg.[t - t]))) =>//.
    apply: Bnd.ComputeBound_correct=>//.
    exact: J.sub_correct.
  step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
  apply: J.add_correct.
    apply: (mul_0_contains_0_l _
      (y := (Xreal qf.[t - t]))) =>//.
    apply: Bnd.ComputeBound_correct=>//.
    exact: J.sub_correct.
  exact: (mul_0_contains_0_l _ (*!*) (y := Xreal 0)).

move=> x0 Hx0 {Hf0 Hg0} /=.
have Hf0 := Fmain x0 Hx0; have Hg0 := Gmain x0 Hx0.
have [pf Hf1 Hf2] := Hf0.
have [pg Hg1 Hg2] := Hg0.
exists (PolR.mul_trunc tt n pf pg); first exact: Pol.mul_trunc_correct.

move=> x Hx.
case Dx: (Xmul (f x) (g x)) => [|mfg].
  step_xi IInan =>//; rewrite /mul_error; do 3![rewrite I.add_propagate_r //].
  case Ef: (f x) Dx => [|fx].
    rewrite I.mul_propagate_l //; exact: Fdef Ef.
  case Eg: (g x) => [|gx //].
    rewrite I.mul_propagate_r //; exact: Gdef Eg.
move/(_ x Hx) in Hf2; move/(_ x Hx) in Hg2.
step_r ((PolR.mul_tail tt n pf pg).[x - x0] * (x - x0)^n.+1 +
  (((proj_val (f x) - pf.[x - x0]) * pg.[x - x0] +
  ((proj_val (g x) - pg.[x - x0]) * pf.[x - x0] +
  (proj_val (f x) - pf.[x - x0]) * (proj_val (g x) - pg.[x - x0])))))%R.
  apply: J.add_correct.
    apply: J.mul_correct.
      apply: Bnd.ComputeBound_correct.
        exact: Pol.mul_tail_correct.
      apply: J.sub_correct =>//; exact: HinX0.
      rewrite pow_powerRZ; apply: J.power_int_correct.
      apply: J.sub_correct=>//; exact: HinX0.
    apply: J.add_correct.
    apply: J.mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: J.sub_correct =>//; exact: HinX0.
  apply: J.add_correct.
    apply: J.mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: J.sub_correct =>//; exact: HinX0.
  exact: J.mul_correct.
clear - Fdef Gdef Dx Hx.
have Hdfx := Fdef x Hx.
have Hdgx := Gdef x Hx.
set sf := pf.[x - x0]%R.
set sg := pg.[x - x0]%R.

rewrite !PolR.hornerE PolR.size_mul_trunc PolR.size_mul_tail.
rewrite (big_endo (fun r => r * (x-x0) ^ n.+1)%R); first last.
  by rewrite Rmult_0_l.
  by move=> a b /=; rewrite Rmult_plus_distr_r.
rewrite (eq_big_nat _ _ (F2 := fun i =>
  PolR.mul_coeff tt pf pg (i + n.+1) * (x - x0) ^ (i + n.+1))%R);
  last first.
  move=> i Hi; rewrite Rmult_assoc; congr Rmult; last by rewrite pow_add.
  rewrite PolR.nth_mul_tail ifF; first by rewrite addnC.
  by case/andP: Hi; case: leqP.
rewrite -(big_addn 0 _ n.+1 predT (fun i =>
  PolR.mul_coeff tt pf pg i * (x - x0) ^ i)%R).
set e := ((proj_val _ - sf) * sg + ((_ - sg) * sf + (_ - sf) * (_ - sg)))%R.
rewrite Rplus_comm.
have->: e = (proj_val (f x * g x)%XR - sf * sg)%R.
(* begin flip-flop *)
rewrite /e.
case: (f x) Dx => [|fx] //.
case: (g x) => [|gx] //.
intros _.
rewrite /=.
ring.
(* end flip-flop *)
rewrite Rplus_assoc -Dx; congr Rplus.
rewrite {}/e {}/sf {}/sg.
rewrite !PolR.hornerE.

apply: (Rplus_eq_reg_r (proj_val (f x * g x)%XR)).
congr Rplus.
rewrite -!PolR.hornerE /=.
rewrite -PolR.horner_mul PolR.hornerE.
set bign1 := \big[Rplus/0%R]_(0 <= i < n.+1) _.
apply: (Rplus_eq_reg_r bign1); rewrite Rplus_opp_l /bign1.
set big := \big[Rplus/0%R]_(0 <= i < _) _.
apply: (Rplus_eq_reg_l big); rewrite -!Rplus_assoc Rplus_opp_r /big Rplus_0_l.
rewrite PolR.size_mul add0n Rplus_0_r.
case: (ltnP n ((PolR.size pf + PolR.size pg).-1)) => Hn.
  rewrite [RHS](big_cat_nat _ _ (n := n.+1)) //=.
  rewrite Rplus_comm; congr Rplus.
  rewrite !big_mkord; apply: eq_bigr.
    move=> [i Hi] _ /=; rewrite PolR.nth_mul_trunc ifF;
      last by apply: negbTE; rewrite -leqNgt.
    rewrite PolR.nth_mul ifF //.
    apply: negbTE; rewrite -ltnNge; rewrite ltnS in Hi.
    exact: leq_ltn_trans Hi Hn.
  rewrite -(add0n n.+1) !big_addn !big_mkord; apply: eq_bigr.
  move=> [i Hi] _ /=; rewrite PolR.nth_mul ifF //.
  apply: negbTE; rewrite -ltnNge.
  by rewrite -addSn leq_addLR.
rewrite -{1}(add0n n.+1) big_addn big_mkord big1; last first.
  move=> [i Hi] _ /=.
  rewrite -subn_eq0 in Hn.
  by rewrite -subn_gt0 subnS (eqP Hn) in Hi.
rewrite Rplus_0_l.
set np := (PolR.size pf + PolR.size pg).-1.
rewrite [in LHS](big_cat_nat _ _ (n := np)) //=;
  last exact: leqW.
set big0 := \big[Rplus/0%R]_(_.-1 <= i < n.+1) _.
have->: big0 = 0%R.
rewrite /big0.
  rewrite /big0 -/np -(add0n np) big_addn big_mkord.
  rewrite big1 // => [[i Hi] _] /=.
  rewrite PolR.nth_mul_trunc ifF; last first.
  rewrite ltn_subRL addnC in Hi.
  by rewrite -ltnS ltnNge Hi.
  rewrite PolR.mul_coeffE PolR.mul_coeff_eq0 ?Rmult_0_l //.
  move=> k Hk.
  case: (leqP (PolR.size pf) k) => Hk0.
    left; rewrite PolR.nth_default //.
  right; rewrite PolR.nth_default //.
  rewrite -leq_addLR //.
  rewrite -(ltn_add2l (PolR.size pg)) [addn (_ pg) (_ pf)]addnC in Hk0.
  move/ltn_leq_pred in Hk0.
  apply: leq_trans Hk0 _.
  by rewrite leq_addl.
rewrite Rplus_0_r !big_mkord; apply: eq_bigr.
move=> [i Hi] _ /=.
rewrite PolR.nth_mul_trunc PolR.nth_mul' ifF ?PolR.mul_coeffE //.
apply: negbTE; rewrite -ltnNge ltnS.
exact: leq_trans (ltnW Hi) Hn.
Qed.

Lemma size_TM_add Mf Mg :
  Pol.size (approx (TM_add Mf Mg)) =
  maxn (Pol.size (approx Mf)) (Pol.size (approx Mg)).
Proof.
by rewrite /TM_add /= Pol.size_add.
Qed.

Lemma size_TM_mul Mf Mg n (X0 X : I.type) :
  Pol.size (approx (TM_mul Mf Mg X0 X n)) = n.+1.
Proof. by rewrite /TM_mul /= Pol.size_mul_trunc. Qed.

Lemma size_TM_sub Mf Mg :
  Pol.size (approx (TM_sub Mf Mg)) =
  maxn (Pol.size (approx Mf)) (Pol.size (approx Mg)).
Proof. by rewrite /TM_sub /= Pol.size_sub. Qed.

Lemma size_TM_opp Mf :
  Pol.size (approx (TM_opp Mf)) = Pol.size (approx Mf).
Proof. by rewrite /TM_opp /= Pol.size_opp. Qed.

Definition TM_horner n p (Mf : rpa) (X0 X : I.type) : rpa :=
  @Pol.fold rpa
  (fun a b => (TM_add (TM_cst X a) (TM_mul b Mf X0 X n)))
  (TM_cst X I.zero) p.

Lemma size_TM_horner n p Mf (X0 X : I.type) :
  Pol.size (approx (TM_horner n p Mf X0 X)) = (if 0 < Pol.size p then n else 0).+1.
Proof.
rewrite /TM_horner.
elim/Pol.poly_ind: p =>[|a p IHp].
  by rewrite Pol.fold_polyNil Pol.size_polyNil size_TM_cst.
by rewrite Pol.fold_polyCons Pol.size_polyCons size_TM_add size_TM_mul
  size_TM_cst max1n.
Qed.

(** A padding function to change the size of a polynomial over R while
    keeping the same coefficients. *)
Definition pad pi pr : PolR.T :=
  take (Pol.size pi) (PolR.set_nth pr (Pol.size pi) 0%R).

Lemma size_pad pi pr : eq_size pi (pad pi pr).
Proof.
rewrite /PolR.size size_take size_set_nth ifT //.
exact: leq_maxl.
Qed.

Lemma pad_correct pi pr : pi >:: pr -> pi >:: pad pi pr.
Proof.
move=> Hp k.
rewrite /PolR.nth nth_take_dflt.
case: ifP => Hk.
rewrite Pol.nth_default //; exact: J.zero_correct.
rewrite nth_set_nth /= ifF; first exact: Hp.
by apply/negP => /eqP K; rewrite K leqnn in Hk.
Qed.

Lemma horner_pad pi pr x : pi >:: pr -> pr.[x] = (pad pi pr).[x].
Proof.
move=> Hp.
rewrite !(@PolR.hornerE_wide (maxn (Pol.size pi) (PolR.size pr))) -?size_pad;
  rewrite ?(leq_maxl, leq_maxr) //.
apply: eq_bigr => i _.
congr Rmult.
rewrite /pad /PolR.nth nth_take_dflt /PolR.nth nth_set_nth.
case: ifP => [Hi| /negbT Hi].
  by rewrite [LHS](Pol.nth_default_alt Hp).
rewrite -ltnNge in Hi; rewrite /= ifF //.
by apply/negbTE; rewrite neq_ltn Hi.
Qed.

Lemma TM_horner_correct (X0 X : I.type) Mf f pi pr n :
  subset' (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  pi >:: pr ->
  i_validTM (I.convert X0) (I.convert X) (TM_horner n pi Mf X0 X) (fun x : R => Xreal pr.[proj_val (f x)]).
Proof.
move=> Hsubs0 /= Hne [Fdef Fnai Fzero Fsubs Fmain] Hp.
have Ht : not_empty (I.convert X0).
  case Hne => t Hts'.
  by exists t.
wlog Hsize : pi pr Hp / Pol.size pi = PolR.size pr => [Hwlog|].
  apply: (@TM_fun_eq (fun x : R => Xreal (pad pi pr).[proj_val (f x)])).
  by move=> x Hx; rewrite /= [in RHS](@horner_pad pi).
  apply: Hwlog.
  exact: pad_correct.
  exact: size_pad.
elim/PolR.poly_ind: pr pi Hp Hsize => [|ar pr IHpr] pi Hp Hsize;
  elim/Pol.poly_ind: pi Hp Hsize =>[|ai pi _] Hp Hsize.
+ rewrite /TM_horner Pol.fold_polyNil /=.
  apply: TM_cst_correct =>//.
  exact: J.zero_correct.
+ by rewrite sizes in Hsize.
+ by rewrite sizes in Hsize.
+ rewrite /= /TM_horner Pol.fold_polyCons.
  apply: (@TM_fun_eq (fun x : R => Xreal ar + Xreal pr.[proj_val (f x)] * Xreal (proj_val (f x)))%XR).
    move=> x Hx /=.
    congr Xreal; ring.
  apply: TM_add_correct.
  apply: TM_cst_correct=>//.
  by have := Hp 0; rewrite Pol.nth_polyCons PolR.nth_polyCons.
  apply: TM_mul_correct =>//.
  apply: IHpr.
  by move=> k; have := Hp k.+1; rewrite Pol.nth_polyCons PolR.nth_polyCons.
  by move: Hsize; rewrite !sizes; case.
Qed.

Definition TM_type := I.type -> I.type -> nat -> rpa.

Definition TMset0 (Mf : rpa) t :=
  RPA (Pol.set_nth (approx Mf) 0 t) (error Mf).

Definition TM_comp (TMg : TM_type) (Mf : rpa) (X0 X : I.type) n :=
  let Bf := Bnd.ComputeBound prec (approx Mf) (I.sub prec X X0) in
  let A0 := Pol.nth (approx Mf) 0 in
  let a0 := Imid A0 in
  let Mg := TMg a0 (I.add prec Bf (error Mf)) n in
  let M1 := TMset0 Mf (I.sub prec A0 a0) in
  let M0 := TM_horner n (approx Mg) M1 X0 X in
  RPA (approx M0) (I.add prec (error M0) (error Mg)).

Lemma TMset0_correct (X0 X c0 : I.type) Mf f :
  let: A0 := Pol.nth (approx Mf) 0 in
  forall a0 alpha0,
  not_empty (I.convert A0) ->
  a0 >: alpha0 ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  i_validTM (I.convert X0) (I.convert X) (TMset0 Mf (I.sub prec A0 a0))
  (fun x => f x - Xreal alpha0).
Proof.
  move=> a0 alpha0 ne_A0 in_a0 Hf.
  rewrite /TMset0.
  have [Mfdef Mfnai Mfzero Mfsubs Mfmain] := Hf.
  split ; try easy.
  intros x Hx Hfx.
  apply (Mfdef x Hx).
  revert Hfx ; clear.
  by case f.
  intros x1 Hx1.
  destruct (Mfmain x1 Hx1) as [Q H1 H2].
  exists (PolR.set_nth Q 0 (PolR.nth Q 0 - alpha0)%R).
  intros k.
  specialize (H1 k).
  clear - H1 ne_A0 in_a0.
  rewrite Pol.nth_set_nth PolR.nth_set_nth.
  destruct k as [|k] ; simpl.
  by apply (I.sub_correct _ _ _ _ (Xreal _) H1).
  exact H1.
  intros x Hx.
  specialize (H2 x Hx).
  move: (Mfdef x Hx).
  clear -H2.
  case Df: (f x) => [|fx].
  by move ->.
  intros _.
  rewrite /Xbind2 /proj_val.
  replace (PolR.set_nth Q 0 (PolR.nth Q 0 - alpha0)%R).[x - x1]
    with (Q.[x - x1] - alpha0)%R.
  replace (fx - alpha0 - (Q.[x - x1] - alpha0))%R
    with (fx - Q.[x - x1])%R by ring.
  by rewrite Df in H2.
  destruct Q as [|q0 Q].
  by rewrite /= Rmult_0_l Rplus_0_l.
  by rewrite /= /Rminus Rplus_assoc.
Qed.

Lemma TM_comp_correct (X0 X : I.type) (TMg : TM_type) (Mf : rpa) g f :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  (forall Y0 Y k, subset' (I.convert Y0) (I.convert Y) ->
    not_empty (I.convert Y0) ->
    i_validTM (I.convert Y0) (I.convert Y) (TMg Y0 Y k) g) ->
  forall n,
  i_validTM (I.convert X0) (I.convert X)
  (TM_comp TMg Mf X0 X n) (fun xr => Xbind g (f xr)).
Proof.
move=> Hne Hf Hg n; rewrite /TM_comp.
set A0 := Pol.nth (approx Mf) 0.
set a0 := Imid A0.
set Bf := Bnd.ComputeBound prec (approx Mf) (I.sub prec X X0).
set BfMf := I.add prec Bf (error Mf).
set Mg := TMg a0 (I.add prec Bf (error Mf)) n.
set M1 := TMset0 Mf (I.sub prec A0 a0).
set M0 := TM_horner n (approx Mg) M1 X0 X.

(* Preliminary facts *)
have [Fdef Fnai Fzero Hsubs Fmain] := Hf.
have ne_A0 : not_empty (I.convert A0).
  have [t Ht] := Hne.
  have [q hq1 hq2] := Fmain t Ht.
  by eexists; eapply hq1.
pose alpha0 := proj_val (I.convert_bound (I.midpoint A0)).
have in_a0 : a0 >: alpha0.
  exact: Xreal_Imid_contains.
have ne_a0 : not_empty (I.convert a0).
  by exists alpha0.
have subs_a0 : subset' (I.convert a0) (I.convert BfMf).
  rewrite /a0 /BfMf.
  move=> [|v] Hv.
    apply/contains_Xnan; rewrite I.add_propagate_r //.
    rewrite /A0 in Hv.
    apply/contains_Xnan.
    by rewrite /Imid I.bnd_correct in Hv.
  rewrite /Bf.
  step_xr (Xadd (Xreal v) (Xreal 0)); last by rewrite Xadd_0_r.
  apply: I.add_correct =>//.
  rewrite /Bf.
  have [t Ht] := Hne.
  have [qf hq1 hq2] := Fmain t Ht.
  apply: (@ComputeBound_nth0 _ _ qf) =>//.
  exact: subset_sub_contains_0 _ Ht Hsubs.
  exact: Imid_subset.
have [Gdef Gnai Gzero Gsubs Gmain] := Hg a0 BfMf n subs_a0 ne_a0.
have inBfMf : forall x : R, X >: x -> contains (I.convert BfMf) (f x).
  move=> x Hx; rewrite /BfMf /Bf.
  have [t Ht] := Hne.
  have [qf hq1 hq2] := Fmain t Ht.
  move/(_ x Hx) in hq2.
  step_xr (Xreal (qf.[x - t]) + (f x - Xreal (qf.[x - t])))%XR =>//.
  apply: I.add_correct.
  apply: Bnd.ComputeBound_correct =>//.
  exact: J.sub_correct.
  case Df: (f x) => [|fx].
  by rewrite (Fdef x Hx Df).
  by rewrite Df in hq2.
  case: (f) =>// r; simpl; congr Xreal; ring.
have HM1 : i_validTM (I.convert X0) (I.convert X) M1 (fun x => f x - Xreal (alpha0)).
  exact: TMset0_correct.

split=>//=.
(* Def *)
- move=> x Hx Dx.
  rewrite I.add_propagate_r //.
  case Efx: (f x) => [|r].
    rewrite Gnai // /Bf.
    rewrite I.add_propagate_r //.
    exact: Fdef Efx.
  rewrite Efx in Dx.
  apply: Gdef Dx.
  rewrite -Efx.
  exact: inBfMf.

(* Nai *)
- move=> HX; rewrite I.add_propagate_r // Gnai //.
  by rewrite I.add_propagate_r // Fnai.

(* Zero *)
rewrite /M0 /Mg /Bf.
step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
have [t Ht] := Hne.
have [a Ha] := ne_a0.
have [Q HQ1 HQ2] := Gmain a Ha.
have [F HF1 HF2] := Fmain t Ht.
apply: I.add_correct =>//.
apply (@TM_horner_correct X0 X M1 _ (approx Mg) Q n Hsubs Hne HM1 HQ1).

(* Main *)
move=> x0 Hx0.
have HMg : i_validTM (I.convert a0) (I.convert BfMf) Mg g by exact: Hg.
(* now we need not [pose smallX0 := IIbnd (Xreal x0) (Xreal x0).] anymore... *)
have [M1def M1nai M1zero M1subs M1main] := HM1.
have [Ga0 HGa0 HGa0'] := Gmain alpha0 in_a0.
pose f0 := (fun x => f x - Xreal alpha0).
have HM0 : i_validTM (I.convert X0) (I.convert X) M0 (fun r => Xreal Ga0.[proj_val (f0 r)]).
  exact: TM_horner_correct.
have [M0def M0nai M0zero M0subs M0main] := HM0.
have [Q0 HQ0 HQ0'] := M0main x0 Hx0.
exists Q0 =>//.
move=> x Hx.
case Enai: (I.convert (I.add prec (error M0) (error Mg))) => [|el eu] //.
rewrite -Enai.
case Efx: (f x) => [|fx].
  rewrite I.add_propagate_r //.
  apply/Gnai/contains_Xnan.
  rewrite -Efx; exact: inBfMf.
rewrite /Xbind.
case Egfx: (g fx) => [|gfx].
  rewrite I.add_propagate_r //.
  apply: Gdef Egfx.
  rewrite -Efx; exact: inBfMf.
pose intermed := Ga0.[proj_val (f0 x)].
rewrite /proj_val.
replace (gfx - Q0.[x - x0])%R with
  (intermed - Q0.[x - x0] + (gfx - intermed))%R by ring.
apply: J.add_correct.
exact: HQ0'.
rewrite /intermed /f0 Efx /=.
rewrite -[gfx](f_equal proj_val Egfx).
apply: HGa0'.
rewrite -Efx.
exact: inBfMf.
Qed.

Definition TM_inv_comp Mf (X0 X : I.type) (n : nat) := TM_comp TM_inv Mf X0 X n.

Lemma TM_inv_comp_correct (X0 X : I.type) (TMf : rpa) f :
  not_empty (I.convert X0) ->
  forall n,
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_inv_comp TMf X0 X n) (fun xr => Xinv (f xr)).
Proof.
move=> Ht n Hf.
apply: TM_comp_correct=> //.
have {Hf} [Hdef Hnai Hzero Hsubs Hmain] := Hf.
move=> Y0 Y k HY HY0.
exact: TM_inv_correct.
Qed.

Definition TM_div Mf Mg (X0 X : I.type) n :=
   TM_mul Mf (TM_inv_comp Mg X0 X n) X0 X n.

Lemma TM_div_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_div TMf TMg X0 X n) (fun xr => Xdiv (f xr) (g xr)).
Proof.
move=> Hne Hf Hg.
apply: (TM_fun_eq (f := fun xr => Xmul (f xr) (Xinv (g xr)))).
  by move=> x; rewrite Xdiv_split.
rewrite /TM_div.
apply: TM_mul_correct =>//.
exact: TM_inv_comp_correct.
Qed.

Lemma size_TM_comp (X0 X : I.type) (Tyg : TM_type) (TMf : rpa) (n : nat) :
  (forall Y0 Y k, 0 < Pol.size (approx (Tyg Y0 Y k))) ->
  Pol.size (approx (TM_comp Tyg TMf X0 X n)) = n.+1.
Proof. by move=> Hsize; rewrite size_TM_horner ifT // Hsize. Qed.

End PrecArgument.

End TaylorModel.


(* FIXME: Generalize TM_integral to handle "X1" and "Y1"
   FIXME: Finish the experiment below to define "TM_atan" using "TM_integral"

Definition TM_atan2 (u : U) (X0 X : I.type) : T :=
  let one := TM_cst u.1 (I.fromZ 1) X0 X u.2 in
  let tm := TM_div u.1 X one (TM_add u X one (TM_power_int u.1 2 X0 X n)) in
  (* prim *) TM_integral u X X1 (I.atan u.1 X1) t'.

Definition atan2 := Eval hnf in fun_gen I.atan TM_atan2.

Lemma Xatan_RInt_f : forall (xF : ExtendedR -> ExtendedR) x1,
let f := toR_fun xF in
let xG := toXreal_fun
  (fun r => RInt (fun x => Derive f x / (1 + (f x)^2)) x1 r + Ratan.atan (f x1))%R in
forall x, xG x = Xatan (xF x).
Proof.

(* TODO: Coquelicot proof *)

Qed.

Theorem atan2_correct :
  forall u (X : I.type) tf xF,
  approximates X tf xF ->
  approximates X (atan2 u X tf) (fun x => Xatan (xF x)).
Proof.
intros.
pose x1 := proj_val (I.convert_bound (I.midpoint X)).
pose f := toR_fun xF.
pose xG := toXreal_fun
  (fun r => RInt (fun x => Derive f x / (1 + (f x)^2)) x1 r + Ratan.atan (f x1))%R.
apply: approximates_ext.
apply: xG.
move=> x; apply: Xatan_RInt_f.
rewrite /atan2.
rewrite /xG /toXreal_fun.
apply: prim_correct.
exact: toXreal_fun (fun r : R => Derive f r / (1 + f r ^ 2)).

(* TODO: midpoint *)

apply: I.atan_correct.
split =>//.

(* TODO: to see later *)

rewrite /atan2 /prim.
case: tf H.
apply: prim_correct.

move=> u Y tf f [Hnan Hnil Hmain].
split=>//; first by rewrite Hnan.
by rewrite /= /tmsize size_TM_any.
move=> Hne; apply: TM_any_correct.
exact: not_empty_Imid.
exact: Imid_subset.
move=> x Hx.
apply: I.atan_correct.
exact: horner_correct.
Qed.
*)
