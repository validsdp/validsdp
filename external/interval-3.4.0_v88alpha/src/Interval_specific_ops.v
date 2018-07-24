(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

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

Require Import ZArith.
Require Import Lia.
Require Import Bool.
From Flocq Require Import Digits Bracket.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_specific_sig.

Import ssrbool.

Inductive s_float (smantissa_type exponent_type : Type) : Type :=
  | Fnan : s_float smantissa_type exponent_type
  | Float : smantissa_type -> exponent_type -> s_float smantissa_type exponent_type.

Arguments Fnan {smantissa_type exponent_type}.
Arguments Float {smantissa_type exponent_type} _ _.

Module SpecificFloat (Carrier : FloatCarrier) <: FloatOps.

Import Carrier.

Definition radix := radix.
Definition even_radix := match radix_val radix with Zpos (xO _) => true | _ => false end.
Definition even_radix_correct := refl_equal even_radix.

Definition type := s_float smantissa_type exponent_type.

Definition toF (x : type) : float radix :=
  match x with
  | Fnan => Interval_definitions.Fnan
  | Float m e =>
    match mantissa_sign m with
    | Mzero => Interval_definitions.Fzero
    | Mnumber s p => Interval_definitions.Float s (MtoP p) (EtoZ e)
    end
  end.

Definition toX (x : type) := FtoX (toF x).

Definition toF_correct := fun x => refl_equal (toX x).

Definition fromF (f : Interval_definitions.float radix) :=
  match f with
  | Interval_definitions.Fnan => Fnan
  | Interval_definitions.Fzero => Float mantissa_zero exponent_zero
  | Interval_definitions.Float false m e => Float (ZtoM (Zpos m)) (ZtoE e)
  | Interval_definitions.Float true m e => Float (ZtoM (Zneg m)) (ZtoE e)
  end.

Definition precision := exponent_type.
Definition sfactor := exponent_type.
Definition prec p := match EtoZ p with Zpos q => q | _ => xH end.
Definition ZtoS := ZtoE.
Definition StoZ := EtoZ.
Definition PtoP n := ZtoE (Zpos n).
Definition incr_prec x y := exponent_add x (ZtoE (Zpos y)).

Definition zero := Float mantissa_zero exponent_zero.
Definition nan := @Fnan smantissa_type exponent_type.
Definition nan_correct := refl_equal Xnan.

Lemma zero_correct :
  toX zero = Xreal 0.
Proof.
generalize (mantissa_sign_correct mantissa_zero).
unfold toX. simpl.
case (mantissa_sign mantissa_zero).
trivial.
rewrite mantissa_zero_correct.
intros s p.
case s ; intros (H, _) ; discriminate H.
Qed.

Definition mag (x : type) :=
  match x with
  | Fnan => exponent_zero
  | Float m e =>
    match mantissa_sign m with
    | Mzero => e
    | Mnumber _ m => exponent_add e (mantissa_digits m)
    end
  end.

Definition real (f : type) := match f with Fnan => false | _ => true end.

Lemma real_correct :
  forall f, real f = match toX f with Xnan => false | _ => true end.
Proof.
intros.
case f ; simpl.
apply refl_equal.
intros m e.
unfold toX.
simpl.
now case (mantissa_sign m).
Qed.

Definition fromZ n := Float (ZtoM n) exponent_zero.

Lemma fromZ_correct :
  forall n, FtoX (toF (fromZ n)) = Xreal (IZR n).
Proof.
intros.
simpl.
generalize (mantissa_sign_correct (ZtoM n)).
case_eq (mantissa_sign (ZtoM n)) ; intros ; rewrite ZtoM_correct in *.
rewrite H0.
apply refl_equal.
rewrite exponent_zero_correct.
rewrite (proj1 H0).
now case s.
Qed.

Lemma match_helper_1 :
  forall A B y2, forall f : A -> B,
  forall x y1,
  f (match mantissa_sign x with Mzero => y1 | Mnumber s p => y2 s p end) =
  match mantissa_sign x with Mzero => f y1 | Mnumber s p => f (y2 s p) end.
Proof.
intros.
now case (mantissa_sign x).
Qed.

Definition float_aux s m e : type :=
  Float ((if s : bool then mantissa_neg else mantissa_pos) m) e.

Lemma toF_float :
  forall s p e, valid_mantissa p ->
  toF (float_aux s p e) = Interval_definitions.Float s (MtoP p) (EtoZ e).
Proof.
intros.
simpl.
generalize (mantissa_sign_correct ((if s then mantissa_neg else mantissa_pos) p)).
case (mantissa_sign ((if s then mantissa_neg else mantissa_pos) p)).
case s.
rewrite mantissa_neg_correct.
intro H0 ; discriminate H0.
exact H.
rewrite mantissa_pos_correct.
intro H0 ; discriminate H0.
exact H.
intros t q.
case s.
rewrite mantissa_neg_correct.
case t ; intros (H1, H2).
now inversion H1.
discriminate H1.
exact H.
rewrite mantissa_pos_correct.
case t ; intros (H1, H2).
discriminate H1.
now inversion H1.
exact H.
Qed.

(*
 * neg
 *)

Definition neg (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber s p => Float ((if s then mantissa_pos else mantissa_neg) p) e
    end
  | _ => f
  end.

Lemma neg_correct :
  forall x, toX (neg x) = Xneg (toX x).
Proof.
intros.
destruct x as [| m e].
apply refl_equal.
unfold toX.
simpl.
generalize (mantissa_sign_correct m).
case_eq (mantissa_sign m).
simpl.
intros -> _.
now rewrite Ropp_0.
intros s p H0 [H1 H2].
generalize (toF_float (negb s) p e H2).
destruct s ; simpl ; intros -> ;
  now rewrite FtoR_neg.
Qed.

(*
 * abs
 *)

Definition abs (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber _ p => Float (mantissa_pos  p) e
    end
  | _ => f
  end.

Lemma abs_correct :
  forall x, toX (abs x) = Xabs (toX x).
Proof.
intros.
destruct x as [| m e].
apply refl_equal.
unfold toX.
simpl.
generalize (mantissa_sign_correct m).
case_eq (mantissa_sign m).
simpl.
intros -> _.
now rewrite Rabs_R0.
intros s p H0 [H1 H2].
generalize (toF_float false p e H2).
simpl ; intros ->.
now rewrite FtoR_abs.
Qed.

(*
 * scale
 *)

Definition scale (f : type) d :=
  match f with
  | Float m e => Float m (exponent_add e d)
  | _ => f
  end.

Lemma scale_correct :
  forall x d, toX (scale x (ZtoS d)) = Xmul (toX x) (Xreal (bpow radix d)).
Proof.
intros x d.
unfold toX.
rewrite <- Fscale_correct.
destruct x as [|m e].
apply refl_equal.
simpl.
destruct (mantissa_sign m) as [|s p].
apply refl_equal.
now rewrite exponent_add_correct, ZtoE_correct.
Qed.

(*
 * scale2
 *)

Definition scale2 (f : type) d :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber s p =>
      match mantissa_scale2 p d with
      | (p2, d2) => float_aux s p2 (exponent_add e d2)
      end
    end
  | _ => f
  end.

Lemma scale2_correct :
  forall x d, even_radix = true ->
  toX (scale2 x (ZtoS d)) = Xmul (toX x) (Xreal (bpow radix2 d)).
Proof.
intros [|m e] d H.
easy.
unfold toX.
simpl.
generalize (mantissa_sign_correct m).
case_eq (mantissa_sign m).
intros Hs _.
simpl.
rewrite Hs.
now rewrite Rmult_0_l.
intros s m' _ (Em,Vm).
simpl.
generalize (mantissa_scale2_correct m' (ZtoS d) Vm).
case mantissa_scale2.
intros p e' (Ep, Vp).
rewrite ZtoE_correct in Ep.
rewrite toF_float with (1 := Vp).
rewrite exponent_add_correct.
simpl.
rewrite 2!FtoR_split.
unfold Defs.F2R.
simpl.
rewrite Rmult_assoc, (Rmult_comm (bpow radix (EtoZ e))).
rewrite 2!IZR_cond_Zopp, <- 2!cond_Ropp_mult_l.
apply (f_equal (fun v => Xreal (cond_Ropp s v))).
rewrite Zplus_comm, bpow_plus, <- 2!Rmult_assoc.
now rewrite <- Ep.
Qed.

(*
 * cmp
 *)

Definition cmp_aux1 m1 m2 :=
  match mantissa_cmp m1 m2 with
  | Eq => Xeq
  | Lt => Xlt
  | Gt => Xgt
  end.

Definition cmp_aux2 m1 e1 m2 e2 :=
  let d1 := mantissa_digits m1 in
  let d2 := mantissa_digits m2 in
  match exponent_cmp (exponent_add e1 d1) (exponent_add e2 d2) with
  | Lt => Xlt
  | Gt => Xgt
  | Eq =>
    let nb := exponent_sub e1 e2 in
    match exponent_cmp nb exponent_zero with
    | Gt => cmp_aux1 (mantissa_shl m1 nb) m2
    | Lt => cmp_aux1 m1 (mantissa_shl m2 (exponent_neg nb))
    | Eq => cmp_aux1 m1 m2
    end
  end.

Lemma cmp_aux2_correct :
  forall m1 e1 m2 e2,
  valid_mantissa m1 -> valid_mantissa m2 ->
  cmp_aux2 m1 e1 m2 e2 = Fcmp_aux2 radix (MtoP m1) (EtoZ e1) (MtoP m2) (EtoZ e2).
Proof.
intros m1 e1 m2 e2 H1 H2.
unfold cmp_aux2, Fcmp_aux2.
rewrite exponent_cmp_correct.
do 2 rewrite exponent_add_correct.
do 2 (rewrite mantissa_digits_correct ; [idtac | assumption]).
unfold radix.
case (EtoZ e1 + Zpos (count_digits Carrier.radix (MtoP m1))
   ?= EtoZ e2 + Zpos (count_digits Carrier.radix (MtoP m2)))%Z ;
  try apply refl_equal.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
rewrite exponent_sub_correct.
case_eq (EtoZ e1 - EtoZ e2)%Z ; intros ; simpl ;
  unfold cmp_aux1, Fcmp_aux1.
now rewrite mantissa_cmp_correct.
generalize (mantissa_shl_correct p m1 (exponent_sub e1 e2) H1).
rewrite exponent_sub_correct.
refine (fun H0 => _ (proj1 (H0 H)) (proj2 (H0 H))).
clear H0.
intros H3 H4.
rewrite mantissa_cmp_correct.
rewrite H3.
apply refl_equal.
exact H4.
exact H2.
generalize (mantissa_shl_correct p m2 (exponent_neg (exponent_sub e1 e2)) H2).
rewrite exponent_neg_correct.
rewrite exponent_sub_correct.
rewrite H.
refine (fun H0 => _ (proj1 (H0 (refl_equal _))) (proj2 (H0 (refl_equal _)))).
clear H0.
intros H3 H4.
rewrite mantissa_cmp_correct.
rewrite H3.
apply refl_equal.
exact H1.
exact H4.
Qed.

Definition cmp (f1 f2 : type) :=
  match f1, f2 with
  | Fnan, _ => Xund
  | _, Fnan => Xund
  | Float m1 e1, Float m2 e2 =>
    match mantissa_sign m1, mantissa_sign m2 with
    | Mzero, Mzero => Xeq
    | Mzero, Mnumber true _ => Xgt
    | Mzero, Mnumber false _ => Xlt
    | Mnumber true _, Mzero => Xlt
    | Mnumber false _, Mzero => Xgt
    | Mnumber true _, Mnumber false _ => Xlt
    | Mnumber false _, Mnumber true _ => Xgt
    | Mnumber true p1, Mnumber true p2 => cmp_aux2 p2 e2 p1 e1
    | Mnumber false p1, Mnumber false p2 => cmp_aux2 p1 e1 p2 e2
    end
  end.

Lemma cmp_correct :
  forall x y, cmp x y = Xcmp (toX x) (toX y).
Proof.
intros.
unfold toX.
rewrite <- Fcmp_correct.
destruct x as [| mx ex].
apply refl_equal.
destruct y as [| my ey].
simpl.
case (mantissa_sign mx) ; intros ; try case s ; apply refl_equal.
simpl.
generalize (mantissa_sign_correct mx) (mantissa_sign_correct my).
case (mantissa_sign mx) ; case (mantissa_sign my).
trivial.
intros sy py.
now case sy.
intros sx px.
now case sx.
intros sy py sx px.
intros (Hx1, Hx2) (Hy1, Hy2).
do 2 (rewrite cmp_aux2_correct ; try assumption).
apply refl_equal.
Qed.

(*
 * min
 *)

Definition min x y :=
  match cmp x y with
  | Xlt => x
  | Xeq => x
  | Xgt => y
  | Xund => nan
  end.

Lemma min_correct :
  forall x y,
  toX (min x y) = Xmin (toX x) (toX y).
Proof.
intros.
unfold min.
rewrite cmp_correct.
unfold toX.
rewrite <- Fcmp_correct, <- Fmin_correct.
unfold Fmin.
now case Fcmp.
Qed.

(*
 * max
 *)

Definition max x y :=
  match cmp x y with
  | Xlt => y
  | Xeq => y
  | Xgt => x
  | Xund => nan
  end.

Lemma max_correct :
  forall x y,
  toX (max x y) = Xmax (toX x) (toX y).
Proof.
intros.
unfold max.
rewrite cmp_correct.
unfold toX.
rewrite <- Fcmp_correct, <- Fmax_correct.
unfold Fmax.
now case Fcmp.
Qed.

(*
 * round
 *)

Definition adjust_mantissa mode m pos sign :=
  if need_change mode (mantissa_even m) pos sign then mantissa_add m mantissa_one else m.

Lemma adjust_mantissa_correct :
  forall mode m pos sign,
  valid_mantissa m ->
  MtoP (adjust_mantissa mode m pos sign) = Interval_generic.adjust_mantissa mode (MtoP m) pos sign /\
  valid_mantissa (adjust_mantissa mode m pos sign).
Proof.
intros mode m pos sign Hm.
unfold adjust_mantissa, Interval_generic.adjust_mantissa.
rewrite mantissa_even_correct with (1 := Hm).
unfold Z.even.
case need_change.
2: now split.
destruct mantissa_one_correct as (Oe, Ov).
rewrite Pplus_one_succ_r.
rewrite <- Oe.
now apply mantissa_add_correct.
Qed.

Definition round_aux mode prec sign m1 e1 pos :=
  let prec := match exponent_cmp prec exponent_zero with Gt => prec | _ => exponent_one end in
  let nb := exponent_sub (mantissa_digits m1) prec in
  let e2 := exponent_add e1 nb in
  match exponent_cmp nb exponent_zero with
  | Gt =>
    let (m2, pos2) := mantissa_shr m1 nb pos in
    float_aux sign (adjust_mantissa mode m2 pos2 sign) e2
  | Eq => float_aux sign (adjust_mantissa mode m1 pos sign) e1
  | Lt =>
    if need_change_radix even_radix mode (mantissa_even m1) pos sign then
      let m2 := mantissa_add (mantissa_shl m1 (exponent_neg nb)) mantissa_one in
      float_aux sign m2 e2
    else float_aux sign m1 e1
  end.

Lemma round_aux_correct :
  forall mode p sign m1 e1 pos,
  valid_mantissa m1 ->
  FtoX (toF (round_aux mode p sign m1 e1 pos)) =
  FtoX (Fround_at_prec mode (prec p) (@Interval_generic.Ufloat radix sign (MtoP m1) (EtoZ e1) pos)).
Proof.
intros mode p' sign m1 e1 pos Hm1.
apply f_equal.
unfold round_aux.
set (p := match exponent_cmp p' exponent_zero with Gt => p' | _ => exponent_one end).
assert (Hp: Zpos (prec p') = EtoZ p).
unfold p.
rewrite exponent_cmp_correct, exponent_zero_correct.
unfold prec.
case_eq (EtoZ p') ; try easy ; intros ; apply sym_eq ;
  apply exponent_one_correct.
clearbody p.
rewrite exponent_cmp_correct.
rewrite exponent_sub_correct.
rewrite exponent_zero_correct.
rewrite mantissa_digits_correct with (1 := Hm1).
unfold Fround_at_prec.
rewrite Hp.
unfold radix.
case_eq (Zpos (count_digits Carrier.radix (MtoP m1)) - EtoZ p)%Z ;
  unfold Zcompare.
(* *)
intros Hd.
destruct (adjust_mantissa_correct mode m1 pos sign Hm1) as (H1,H2).
rewrite toF_float with (1 := H2).
now rewrite H1.
(* *)
intros dp Hd.
refine (_ (mantissa_shr_correct dp m1 (exponent_sub (mantissa_digits m1) p) pos Hm1 _ _)).
case mantissa_shr.
intros sq sl.
case Zdiv_eucl.
intros q r (Hq, (Hl, Vq)).
rewrite <- Hq.
destruct (adjust_mantissa_correct mode sq sl sign Vq) as (Ha, Va).
rewrite toF_float with (1 := Va).
rewrite Ha.
rewrite exponent_add_correct, exponent_sub_correct, mantissa_digits_correct with (1 := Hm1).
now rewrite Hd, Hl.
now rewrite exponent_sub_correct, mantissa_digits_correct.
rewrite shift_correct, Zmult_1_l.
change (Zpower Carrier.radix (Zpos dp) <= Zabs (Zpos (MtoP m1)))%Z.
apply Zpower_le_Zdigits.
rewrite <- Hd, <- Hp.
rewrite <- digits_conversion.
clear ; zify ; omega.
(* *)
intros dp Hd.
rewrite mantissa_even_correct with (1 := Hm1).
unfold need_change_radix2, even_radix, radix, Z.even.
case need_change_radix.
2: now apply toF_float.
generalize (mantissa_shl_correct dp m1 (exponent_neg (exponent_sub (mantissa_digits m1) p)) Hm1).
rewrite exponent_neg_correct, exponent_sub_correct, mantissa_digits_correct with (1 := Hm1).
rewrite Hd.
intros H1.
specialize (H1 (refl_equal _)).
assert (H2 := mantissa_add_correct (mantissa_shl m1 (exponent_neg (exponent_sub (mantissa_digits m1) p)))
  mantissa_one (proj2 H1) (proj2 mantissa_one_correct)).
rewrite toF_float. 2: easy.
rewrite (proj1 H2).
rewrite (proj1 H1).
rewrite (proj1 (mantissa_one_correct)).
rewrite Pplus_one_succ_r.
rewrite exponent_add_correct, exponent_sub_correct, mantissa_digits_correct with (1 := Hm1).
now rewrite Hd.
Qed.

Definition round_at_exp_aux mode e2 sign m1 e1 pos :=
  let nb := exponent_sub e2 e1 in
  match exponent_cmp nb exponent_zero with
  | Gt =>
    match exponent_cmp (mantissa_digits m1) nb with
    | Gt =>
      let (m2, pos2) := mantissa_shr m1 nb pos in
      float_aux sign (adjust_mantissa mode m2 pos2 sign) e2
    | Eq =>
      let pos2 := mantissa_shrp m1 nb pos in
      if need_change_zero mode pos2 sign then
        float_aux sign mantissa_one e2
      else zero
    | Lt =>
      let pos2 := match pos with pos_Eq => pos_Eq | _ => pos_Lo end in
      if need_change_zero mode pos_Lo sign then
        float_aux sign mantissa_one e2
      else zero
    end
  | Eq => float_aux sign (adjust_mantissa mode m1 pos sign) e1
  | Lt =>
      if need_change_radix even_radix mode (mantissa_even m1) pos sign then
        let m2 := mantissa_add (mantissa_shl m1 (exponent_neg nb)) mantissa_one in
        float_aux sign m2 e2
      else float_aux sign m1 e1
  end.

Lemma toF_zero : toF zero = Fzero.
Proof.
unfold toF; simpl.
generalize (mantissa_sign_correct mantissa_zero).
rewrite mantissa_zero_correct.
now destruct mantissa_sign; try easy; destruct s; intros []; discriminate.
Qed.

Lemma round_at_exp_aux_correct :
  forall mode e2 sign m1 e1 pos,
  valid_mantissa m1 ->
  FtoX (toF (round_at_exp_aux mode e2 sign m1 e1 pos)) =
  FtoX (Fround_at_exp mode (EtoZ e2) (@Interval_generic.Ufloat radix sign (MtoP m1) (EtoZ e1) pos)).
Proof.
intros mode p' sign m1 e1 pos Hm1.
apply f_equal.
unfold round_at_exp_aux.
rewrite exponent_cmp_correct.
rewrite exponent_sub_correct.
rewrite exponent_zero_correct.
unfold Fround_at_exp.
unfold radix.
case_eq (EtoZ p' - EtoZ e1)%Z ;
  unfold Zcompare.
(* *)
intros Hd.
destruct (adjust_mantissa_correct mode m1 pos sign Hm1) as (H1,H2).
now rewrite toF_float, H1.
(* *)
intros dp Hd.
rewrite exponent_cmp_correct, mantissa_digits_correct, exponent_sub_correct; try easy.
rewrite Hd; simpl Zcompare.
case Pcompare_spec.
- intros Hc.
  rewrite <- mantissa_shrp_correct with (z := (exponent_sub p' e1)); try easy; last 2 first.
  - now rewrite exponent_sub_correct.
  - rewrite shift_correct, Z.pow_pos_fold.
    rewrite <- Hc, <- digits_conversion.
    destruct (Zdigits_correct Carrier.radix (Z.pos (MtoP m1))).
    now lia.
  - destruct need_change_zero; try easy.
    - destruct mantissa_one_correct as [Ho1 Ho2].
      now rewrite toF_float, Ho1.
    - now apply toF_zero.
- intros Hc.
  rewrite fun_if with (f := toF).
  destruct mantissa_one_correct as [Ho1 Ho2].
  now rewrite toF_zero, toF_float, Ho1.
- intros Hc.
  refine ( _ (mantissa_shr_correct dp m1 (exponent_sub p' e1) pos Hm1 _ _)); last 2 first.
  - now rewrite exponent_sub_correct.
  - rewrite shift_correct, Z.pow_pos_fold.
  - assert (He: (Zpos dp <= Zpos ( count_digits Carrier.radix (MtoP m1)) -1)%Z) by lia.
    generalize (Zpower_le Carrier.radix  _ _ He).
    rewrite <- digits_conversion.
    destruct (Zdigits_correct Carrier.radix (Z.pos (MtoP m1))).
    now lia.
  case mantissa_shr.
  intros sq sl.
  case Zdiv_eucl.
  intros q r (Hq, (Hl, Vq)).
  rewrite <- Hq.
  destruct (adjust_mantissa_correct mode sq sl sign Vq) as (Ha, Va).
  rewrite toF_float with (1 := Va).
  now rewrite Ha, <- Hl.
(* *)
intros dp Hd.
rewrite mantissa_even_correct with (1 := Hm1).
unfold need_change_radix2, even_radix, radix, Z.even.
case need_change_radix.
2: now apply toF_float.
generalize (mantissa_shl_correct dp m1 (exponent_neg (exponent_sub p' e1)) Hm1).
rewrite exponent_neg_correct, exponent_sub_correct.
rewrite Hd.
intros H1.
specialize (H1 (refl_equal _)).
assert (H2 := mantissa_add_correct (mantissa_shl m1 (exponent_neg (exponent_sub p' e1)))
  mantissa_one (proj2 H1) (proj2 mantissa_one_correct)).
rewrite toF_float. 2: easy.
rewrite (proj1 H2).
rewrite (proj1 H1).
rewrite (proj1 (mantissa_one_correct)).
now rewrite Pplus_one_succ_r.
Qed.

Definition round mode prec (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => zero
    | Mnumber s p => round_aux mode prec s p e pos_Eq
    end
  | _ => f
  end.

(*
 * mul_exact
 *)

Definition mul_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => x
    | _, Mzero => y
    | Mnumber sx px, Mnumber sy py =>
      float_aux (xorb sx sy) (mantissa_mul px py) (exponent_add ex ey)
    end
  end.

Lemma mul_exact_correct :
  forall x y, toX (mul_exact x y) = Xmul (toX x) (toX y).
Proof.
intros x y.
unfold toX.
rewrite <- Fmul_exact_correct.
destruct x as [| mx ex].
apply refl_equal.
simpl.
destruct y as [| my ey].
now case (mantissa_sign mx).
generalize (mantissa_sign_correct mx) (mantissa_sign_correct my).
case_eq (mantissa_sign mx) ; simpl ; case_eq (mantissa_sign my) ; simpl.
intros _ Hx _ _.
rewrite Hx.
apply refl_equal.
intros sy py _ Hx _ _.
rewrite Hx.
apply refl_equal.
intros Hy sx px _ _ _.
rewrite Hy.
apply refl_equal.
intros sy py _ sx px _ (_, Hx2) (_, Hy2).
generalize (mantissa_mul_correct px py).
intro H.
destruct (H Hx2 Hy2).
clear H.
generalize (mantissa_sign_correct ((if xorb sx sy then mantissa_neg else mantissa_pos)
  (mantissa_mul px py))).
case (mantissa_sign ((if xorb sx sy then mantissa_neg else mantissa_pos)
  (mantissa_mul px py))).
case (xorb sx sy).
rewrite mantissa_neg_correct.
intro H. discriminate H.
exact (proj2 (mantissa_mul_correct _ _ Hx2 Hy2)).
rewrite mantissa_pos_correct.
intro H. discriminate H.
exact (proj2 (mantissa_mul_correct _ _ Hx2 Hy2)).
intros sz pz (Hz1, Hz2).
simpl.
rewrite exponent_add_correct.
rewrite <- H0.
assert (forall A B, forall b : bool, forall f1 f2 : A -> B, forall x, (if b then f1 else f2) x = if b then f1 x else f2 x).
intros.
now case b.
do 2 rewrite H in Hz1.
clear H.
assert (forall A B, forall f : A -> B, forall b : bool, forall x1 x2, f (if b then x1 else x2) = if b then f x1 else f x2).
intros.
now case b.
rewrite (H _ _ MtoZ) in Hz1.
clear H.
rewrite mantissa_neg_correct in Hz1 ; [idtac | exact H1].
rewrite mantissa_pos_correct in Hz1 ; [idtac | exact H1].
generalize Hz1. clear Hz1.
case (xorb sx sy) ; case sz ; intro H ; try discriminate H ; inversion H ; apply refl_equal.
Qed.

(*
 * mul
 *)

Definition mul mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => x
    | _, Mzero => y
    | Mnumber sx mx, Mnumber sy my =>
      round_aux mode prec (xorb sx sy) (mantissa_mul mx my) (exponent_add ex ey) pos_Eq
    end
  end.

Lemma mul_correct :
  forall mode p x y,
  toX (mul mode p x y) = Xround radix mode (prec p) (Xmul (toX x) (toX y)).
Proof.
intros mode p x y.
unfold toX.
rewrite <- Fmul_correct.
destruct x as [|mx ex] ; destruct y as [|my ey] ; try easy.
simpl.
now case (mantissa_sign mx).
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx).
simpl.
intros.
rewrite H.
now case (mantissa_sign my).
intros sx px Hx (Hx1, Hx2).
rewrite (match_helper_1 _ _ (fun s py => round_aux mode p (Datatypes.xorb sx s) (mantissa_mul px py)
  (exponent_add ex ey) pos_Eq) (fun a => FtoX (toF a))).
rewrite (match_helper_1 _ _ (fun s p => Interval_definitions.Float s (MtoP p) (EtoZ ey))
  (fun a => FtoX (Fmul mode (prec p) (Interval_definitions.Float sx (MtoP px) (EtoZ ex)) a))).
simpl.
generalize (mantissa_sign_correct my).
case (mantissa_sign my).
trivial.
intros sy py (_, Hy2).
destruct (mantissa_mul_correct px py) as (H1, H2) ; try assumption.
rewrite round_aux_correct.
rewrite H1. clear H1.
rewrite exponent_add_correct.
apply refl_equal.
exact H2.
Qed.

(*
 * add_exact
 *)

Definition add_exact_aux1 sx sy mx my e :=
  if eqb sx sy then
    float_aux sx (mantissa_add mx my) e
  else
    match mantissa_cmp mx my with
    | Eq => zero
    | Gt => float_aux sx (mantissa_sub mx my) e
    | Lt => float_aux sy (mantissa_sub my mx) e
    end.

Definition add_exact_aux2 sx sy mx my ex ey :=
  let nb := exponent_sub ex ey in
  match exponent_cmp nb exponent_zero with
  | Gt => add_exact_aux1 sx sy (mantissa_shl mx nb) my ey
  | Lt => add_exact_aux1 sx sy mx (mantissa_shl my (exponent_neg nb)) ex
  | Eq => add_exact_aux1 sx sy mx my ex
  end.

Definition add_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => y
    | _, Mzero => x
    | Mnumber sx mx, Mnumber sy my =>
      add_exact_aux2 sx sy mx my ex ey
    end
  end.

Lemma add_exact_aux_correct :
  forall sx mx ex sy my ey,
  valid_mantissa mx -> valid_mantissa my ->
  FtoX (toF (add_exact_aux2 sx sy mx my ex ey)) =
  FtoX (Fround_none (Fadd_slow_aux2 radix sx sy (MtoP mx) (MtoP my) (EtoZ ex) (EtoZ ey))).
Proof.
assert (Aux: forall sx mx sy my e,
  valid_mantissa mx -> valid_mantissa my ->
  FtoX (toF (add_exact_aux1 sx sy mx my e)) = FtoX (Fround_none (Fadd_slow_aux1 radix sx sy (MtoP mx) (MtoP my) (EtoZ e)))).
intros sx mx sy my e Mx My.
unfold add_exact_aux1, Fadd_slow_aux1.
case eqb.
destruct (mantissa_add_correct _ _ Mx My) as (Ep,Mp).
rewrite toF_float with (1 := Mp).
now rewrite Ep.
rewrite (mantissa_cmp_correct _ _ Mx My).
simpl.
rewrite Z.pos_sub_spec.
case Pcompare_spec.
intros _.
apply zero_correct.
intros H.
destruct (mantissa_sub_correct _ _ My Mx H) as (Ep,Mp).
rewrite toF_float with (1 := Mp).
now rewrite Ep.
intros H.
destruct (mantissa_sub_correct _ _ Mx My H) as (Ep,Mp).
rewrite toF_float with (1 := Mp).
now rewrite Ep.
intros sx mx ex sy my ey Mx My.
unfold add_exact_aux2, Fadd_slow_aux2.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
rewrite <- exponent_sub_correct.
case_eq (EtoZ (exponent_sub ex ey)).
simpl.
intros H.
now apply Aux.
simpl.
intros p Hp.
destruct (mantissa_shl_correct _ _ _ Mx Hp) as (Ep,Mp).
rewrite Aux ; try easy.
now rewrite Ep.
simpl.
intros p Hp.
assert (Hn: EtoZ (exponent_neg (exponent_sub ex ey)) = Zpos p).
rewrite exponent_neg_correct.
now rewrite Hp.
destruct (mantissa_shl_correct _ _ _ My Hn) as (Ep,Mp).
rewrite Aux ; try easy.
now rewrite Ep.
Qed.

Lemma add_exact_correct :
  forall x y, toX (add_exact x y) = Xadd (toX x) (toX y).
Proof.
intros x y.
unfold toX.
rewrite <- Fadd_exact_correct.
destruct x as [|mx ex].
apply refl_equal.
destruct y as [|my ey].
simpl.
now case (mantissa_sign mx).
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx).
simpl.
now case (mantissa_sign my).
intros sx px Hx (Hx1, Hx2).
generalize (mantissa_sign_correct my).
case (mantissa_sign my).
simpl.
now rewrite Hx.
intros sy py (Hy1, Hy2).
unfold Fadd_exact, Fadd_slow_aux.
now apply add_exact_aux_correct.
Qed.

(*
 * add
 *)

Definition add_slow_aux1 mode prec sx sy mx my e :=
  if eqb sx sy then
    round_aux mode prec sx (mantissa_add mx my) e pos_Eq
  else
    match mantissa_cmp mx my with
    | Eq => zero
    | Gt => round_aux mode prec sx (mantissa_sub mx my) e pos_Eq
    | Lt => round_aux mode prec sy (mantissa_sub my mx) e pos_Eq
    end.

Lemma add_slow_aux1_correct :
  forall mode p sx sy mx my e,
  valid_mantissa mx ->
  valid_mantissa my ->
  FtoX (toF (add_slow_aux1 mode p sx sy mx my e)) = FtoX (Fround_at_prec mode (prec p) (Fadd_slow_aux1 radix sx sy (MtoP mx) (MtoP my) (EtoZ e))).
Proof.
intros mode p sx sy mx my e Vx Vy.
unfold add_slow_aux1, Fadd_slow_aux1.
case eqb.
- destruct (mantissa_add_correct mx my Vx Vy) as [H1 H2].
  rewrite <- H1.
  now apply round_aux_correct.
- change (Zpos (MtoP mx) + Zneg (MtoP my))%Z with (Zpos (MtoP mx) - Zpos (MtoP my))%Z.
  rewrite (mantissa_cmp_correct mx my Vx Vy).
  rewrite Z.compare_sub.
  case_eq (Zpos (MtoP mx) - Zpos (MtoP my))%Z ; unfold Zcompare.
  + intros H.
    simpl.
    generalize (mantissa_sign_correct mantissa_zero).
    case mantissa_sign.
    easy.
    rewrite mantissa_zero_correct.
    now intros [|].
  + intros m H.
    assert (H': (Zpos (MtoP my) < Zpos (MtoP mx))%Z).
      clear -H ; zify ; omega.
    destruct (mantissa_sub_correct mx my Vx Vy H') as [H1 H2].
    rewrite round_aux_correct by exact H2.
    rewrite H1.
    simpl in H.
    rewrite Z.pos_sub_gt in H by exact H'.
    injection H.
    now intros ->.
  + intros m H.
    assert (H': (Zpos (MtoP mx) < Zpos (MtoP my))%Z).
      clear -H ; zify ; omega.
    destruct (mantissa_sub_correct my mx Vy Vx H') as [H1 H2].
    rewrite round_aux_correct by exact H2.
    rewrite H1.
    simpl in H.
    rewrite Z.pos_sub_lt in H by exact H'.
    injection H.
    now intros ->.
Qed.

Definition add_slow_aux2 mode prec sx sy mx my ex ey :=
  let nb := exponent_sub ex ey in
  match exponent_cmp nb exponent_zero with
  | Gt => add_slow_aux1 mode prec sx sy (mantissa_shl mx nb) my ey
  | Lt => add_slow_aux1 mode prec sx sy mx (mantissa_shl my (exponent_neg nb)) ex
  | Eq => add_slow_aux1 mode prec sx sy mx my ex
  end.

Lemma add_slow_aux2_correct :
  forall mode p sx sy mx my ex ey,
  valid_mantissa mx ->
  valid_mantissa my ->
  FtoX (toF (add_slow_aux2 mode p sx sy mx my ex ey)) = FtoX (Fround_at_prec mode (prec p) (Fadd_slow_aux2 radix sx sy (MtoP mx) (MtoP my) (EtoZ ex) (EtoZ ey))).
Proof.
intros mode p sx sy mx my ex ey Vx Vy.
unfold add_slow_aux2, Fadd_slow_aux2.
rewrite exponent_cmp_correct, exponent_sub_correct, exponent_zero_correct.
case_eq (EtoZ ex - EtoZ ey)%Z ; unfold Zcompare.
- intros _.
  now apply add_slow_aux1_correct.
- intros d Hd.
  generalize (mantissa_shl_correct d mx (exponent_sub ex ey) Vx).
  intros H'.
  destruct H' as [H1 H2].
  rewrite <- Hd.
  apply exponent_sub_correct.
  rewrite add_slow_aux1_correct by assumption.
  now rewrite H1.
- intros d Hd.
  generalize (mantissa_shl_correct d my (exponent_neg (exponent_sub ex ey)) Vy).
  intros H'.
  destruct H' as [H1 H2].
  change (Zpos d) with (Zopp (Zneg d)).
  rewrite <- Hd.
  rewrite exponent_neg_correct.
  apply f_equal, exponent_sub_correct.
  rewrite add_slow_aux1_correct by assumption.
  now rewrite H1.
Qed.

Definition add_slow mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, Mzero => x
    | Mzero, Mnumber sy py => round_aux mode prec sy py ey pos_Eq
    | Mnumber sx px, Mzero => round_aux mode prec sx px ex pos_Eq
    | Mnumber sx px, Mnumber sy py =>
      add_slow_aux2 mode prec sx sy px py ex ey
    end
  end.

Lemma add_slow_correct :
  forall mode p x y,
  toX (add_slow mode p x y) = Xround radix mode (prec p) (Xadd (toX x) (toX y)).
Proof.
intros mode p x y.
unfold toX.
rewrite <- Fadd_correct.
unfold add_slow, Fadd_slow, Fadd_slow_aux.
destruct x as [|mx ex] ; try easy.
destruct y as [|my ey].
simpl.
now destruct (mantissa_sign mx).
unfold toF.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx).
- intros Hx _.
  generalize (mantissa_sign_correct my).
  destruct (mantissa_sign my) as [|sy ny].
  now rewrite Hx.
  intros [My Vy].
  rewrite <- round_aux_correct by exact Vy.
  case round_aux.
  reflexivity.
  intros m e.
  generalize (mantissa_sign_correct m).
  case_eq (mantissa_sign m).
  simpl.
  now intros ->.
  intros s n.
  simpl.
  now intros ->.
- intros sx nx Hx [Hmx Vx].
  generalize (mantissa_sign_correct my).
  destruct (mantissa_sign my) as [|sy ny].
  + intros Hy.
    rewrite <- round_aux_correct by exact Vx.
    case round_aux.
    reflexivity.
    intros m e.
    generalize (mantissa_sign_correct m).
    case_eq (mantissa_sign m).
    simpl.
    now intros ->.
    intros s n.
    simpl.
    now intros ->.
+ intros [Hmy Vy].
  rewrite <- (add_slow_aux2_correct mode p sx sy nx ny ex ey Vx Vy).
  case add_slow_aux2.
  reflexivity.
  intros m e.
  generalize (mantissa_sign_correct m).
  case_eq (mantissa_sign m).
  simpl.
  now intros ->.
  simpl.
  now intros s n ->.
Qed.

Definition add := add_slow.

Lemma add_correct :
  forall mode p x y,
  toX (add mode p x y) = Xround radix mode (prec p) (Xadd (toX x) (toX y)).
Proof.
exact add_slow_correct.
Qed.

(*
 * sub_exact
 *)

Definition sub_exact (x y : type) := add_exact x (neg y).

Lemma sub_exact_correct :
  forall x y, toX (sub_exact x y) = Xsub (toX x) (toX y).
Proof.
intros x y.
unfold sub_exact.
rewrite add_exact_correct.
rewrite neg_correct.
now rewrite Xsub_split.
Qed.

(*
 * sub
 *)

Definition sub mode prec (x y : type) := add mode prec x (neg y).

Lemma sub_correct :
  forall mode p x y,
  toX (sub mode p x y) = Xround radix mode (prec p) (Xsub (toX x) (toX y)).
Proof.
intros.
rewrite Xsub_split.
unfold sub.
rewrite add_correct.
now rewrite neg_correct.
Qed.

(*
 * div
 *)

Definition div_aux mode prec s mx my e :=
  let (q, pos) := mantissa_div mx my in
  round_aux mode prec s q e pos.

Definition div mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    let prec := match exponent_cmp prec exponent_zero with Gt => prec | _ => exponent_one end in
    match mantissa_sign mx, mantissa_sign my with
    | _, Mzero => Fnan
    | Mzero, _ => x
    | Mnumber sx px, Mnumber sy py =>
      let dx := mantissa_digits px in
      let dy := mantissa_digits py in
      let e := exponent_sub ex ey in
      let nb := exponent_sub (exponent_add dy prec) dx in
      match exponent_cmp nb exponent_zero with
      | Gt =>
        div_aux mode prec (xorb sx sy) (mantissa_shl px nb) py (exponent_sub e nb)
      | _ => div_aux mode prec (xorb sx sy) px py e
      end
    end
  end.

Theorem div_correct :
  forall mode p x y,
  toX (div mode p x y) = Xround radix mode (prec p) (Xdiv (toX x) (toX y)).
Proof.
intros mode p x y.
unfold toX.
rewrite <- Fdiv_correct.
destruct x as [|mx ex] ; destruct y as [|my ey] ; try easy.
simpl.
now case (mantissa_sign mx).
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx) ; [ intros Hx Mx | intros sx nx Hx (Mx, Vmx) ].
destruct (mantissa_sign my) as [|sy ny].
apply refl_equal.
simpl.
now rewrite Hx.
generalize (mantissa_sign_correct my).
case_eq (mantissa_sign my) ; [ intros Hy My | intros sy ny Hy (My, Vmy) ].
apply refl_equal.
rewrite exponent_cmp_correct.
rewrite exponent_sub_correct, exponent_add_correct, exponent_zero_correct.
rewrite 2!mantissa_digits_correct ; try easy.
rewrite <- 2!digits_conversion.
unfold Fdiv, Fdiv_aux, Fdiv_aux2.
set (p' := match exponent_cmp p exponent_zero with Gt => p | _ => exponent_one end).
assert (Hp: EtoZ p' = Zpos (prec p)).
unfold p', prec.
rewrite exponent_cmp_correct, exponent_zero_correct.
case_eq (EtoZ p) ; try (intros ; apply exponent_one_correct).
easy.
rewrite Hp.
unfold radix.
set (d := (Zdigits Carrier.radix (Zpos (MtoP ny)) + Zpos (prec p) - Zdigits Carrier.radix (Zpos (MtoP nx)))%Z).
set (nd := exponent_sub (exponent_add (mantissa_digits ny) p') (mantissa_digits nx)).
assert (Hs := fun d' (H : EtoZ nd = Zpos d') => mantissa_shl_correct d' nx nd Vmx H).
assert (Hs': forall d', d = Zpos d' -> MtoP (mantissa_shl nx nd) = shift Carrier.radix (MtoP nx) d' /\ valid_mantissa (mantissa_shl nx nd)).
intros d' H.
apply Hs.
unfold nd.
rewrite exponent_sub_correct, exponent_add_correct, 2!mantissa_digits_correct, <- 2!digits_conversion ; trivial.
now rewrite Hp.
replace (match (d ?= 0)%Z with
  | Gt => div_aux mode p' (xorb sx sy) (mantissa_shl nx nd) ny (exponent_sub (exponent_sub ex ey) nd)
  | _ => div_aux mode p' (xorb sx sy) nx ny (exponent_sub ex ey)
  end) with (div_aux mode p' (xorb sx sy) (match d with Zpos _ => mantissa_shl nx nd | _ => nx end)
    ny (match d with Zpos _ => exponent_sub (exponent_sub ex ey) nd | _ => exponent_sub ex ey end))
  by now case d.
unfold div_aux.
(* *)
assert (Vmx': valid_mantissa (match d with Zpos _ => mantissa_shl nx nd | _ => nx end)).
destruct d as [|pd|pd] ; trivial.
now apply (Hs' pd).
assert (Hxy: (Zpos (MtoP ny) <= Zpos (MtoP (match d with Zpos _ => mantissa_shl nx nd | _ => nx end)))%Z).
apply Zlt_le_weak.
apply (lt_Zdigits Carrier.radix).
easy.
case_eq d.
unfold d.
clear ; zify ; omega.
intros p0 Hp0.
specialize (Hs' p0 Hp0).
rewrite (proj1 Hs').
rewrite shift_correct.
fold (Zpower Carrier.radix (Zpos p0)).
rewrite Zdigits_mult_Zpower ; try easy.
rewrite <- Hp0.
unfold d.
clear ; zify ; omega.
intros p0.
unfold d.
clear ; zify ; omega.
(* *)
clear Hs.
generalize (mantissa_div_correct _ ny Vmx' Vmy Hxy).
destruct (mantissa_div (match d with Zpos _ => mantissa_shl nx nd | _ => nx end) ny) as (nq, nl).
assert (H: Zpos (MtoP (match d with Zpos _ => mantissa_shl nx nd | _ => nx end)) =
  match d with Zpos p0 => (Zpos (MtoP nx) * Zpower_pos Carrier.radix p0)%Z | _ => Zpos (MtoP nx) end).
destruct d as [|pd|pd] ; trivial.
rewrite <- shift_correct.
apply f_equal.
now apply Hs'.
rewrite H. clear H.
intros (H1, (H2, H3)).
rewrite round_aux_correct with (1 := H3).
apply (f_equal2 (fun v w => FtoX (Fround_at_prec mode v w))).
unfold prec.
now rewrite Hp.
replace (match d with Zpos p0 => ((Zpos (MtoP nx) * Zpower_pos Carrier.radix p0), (EtoZ ex - EtoZ ey + Zneg p0))%Z | _ => (Zpos (MtoP nx), (EtoZ ex - EtoZ ey)%Z) end)
  with (match d with Zpos p0 => (Zpos (MtoP nx) * Zpower_pos Carrier.radix p0)%Z | _ => Zpos (MtoP nx) end, match d with Zpos p0 => (EtoZ ex - EtoZ ey + Zneg p0)%Z | _ => (EtoZ ex - EtoZ ey)%Z end)
  by now case d.
revert H1.
unfold Zdiv.
generalize (Z_div_mod (match d with Zpos p0 => (Zpos (MtoP nx) * Zpower_pos Carrier.radix p0)%Z | _ => Zpos (MtoP nx) end) (Zpos (MtoP ny)) (refl_equal _)).
rewrite Zfast_div_eucl_correct.
case Zdiv_eucl.
intros q r (Hq,Hr) H1.
rewrite <- H1.
apply f_equal2.
case_eq d ; try (intros ; apply exponent_sub_correct).
intros p0 Hp0.
rewrite 2!exponent_sub_correct.
unfold Zminus.
apply f_equal.
change (Zneg p0) with (-Zpos p0)%Z.
rewrite <- Hp0.
unfold nd.
rewrite exponent_sub_correct, exponent_add_correct, 2!mantissa_digits_correct, <- 2!digits_conversion ; trivial.
now rewrite Hp.
replace nl with (convert_location (convert_location_inv nl)) by now case nl.
apply f_equal.
destruct (Zle_or_lt (Zpos (MtoP ny)) 1) as [Ky|Ky].
(* . *)
assert (Zpos (MtoP ny) = 1%Z /\ r = Z0).
clear -Hr Ky ;zify ; omega.
rewrite (proj1 H), (proj2 H).
inversion_clear H2.
easy.
apply False_ind.
revert H0.
rewrite (proj1 H).
unfold Rdiv.
rewrite Rinv_1, Rmult_1_r.
intros (H0, H2).
generalize (lt_IZR _ _ H0) (lt_IZR _ _ H2).
clear ; omega.
(* . *)
apply Bracket.inbetween_unique with (1 := H2).
rewrite plus_IZR.
replace 1%R with (IZR (Zpos (MtoP ny)) * /IZR (Zpos (MtoP ny)))%R.
apply Bracket.new_location_correct ; trivial.
apply Rinv_0_lt_compat.
now apply IZR_lt.
constructor.
rewrite Hq, H1.
rewrite plus_IZR.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
rewrite mult_IZR, <- (Rmult_comm (IZR q)), Rmult_assoc.
rewrite Rinv_r.
now rewrite Rmult_1_r.
now apply IZR_neq.
apply Rinv_r.
now apply IZR_neq.
Qed.

(*
 * sqrt
 *)

Definition sqrt mode prec (f : type) :=
  match f with
  | Fnan => f
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber true _ => Fnan
    | Mnumber false p =>
      let d := mantissa_digits p in
      let prec := match exponent_cmp prec exponent_zero with Gt => prec | _ => exponent_one end in
      let s := exponent_sub (exponent_add prec prec) d in
      let s := match exponent_cmp s exponent_zero with Gt => s | _ => exponent_zero end in
      let (e', r) := exponent_div2_floor (exponent_sub e s) in
      let s := if r then exponent_add s exponent_one else s in
      let m := match exponent_cmp s exponent_zero with Gt => mantissa_shl p s | _ => p end in
      let (m', pos) := mantissa_sqrt m in
      round_aux mode prec false m' e' pos
    end
  end.

Lemma sqrt_correct :
  forall mode p x,
  toX (sqrt mode p x) = Xround radix mode (prec p) (Xsqrt (toX x)).
Proof.
intros mode p x.
unfold toX.
rewrite <- Fsqrt_correct.
destruct x as [|mx ex] ; try easy.
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx) ; [ intros Hx Mx | intros sx nx Hx (Mx, Vx) ].
simpl.
now rewrite Hx.
destruct sx ; try easy.
set (p' := match exponent_cmp p exponent_zero with Gt => p | _ => exponent_one end).
assert (Hp: EtoZ p' = Zpos (prec p)).
  unfold p', prec.
  rewrite exponent_cmp_correct, exponent_zero_correct.
  case_eq (EtoZ p) ; try (intros ; apply exponent_one_correct).
  easy.
clearbody p'.
rewrite exponent_cmp_correct.
rewrite exponent_sub_correct.
rewrite exponent_add_correct.
rewrite exponent_zero_correct.
unfold Fsqrt, Fsqrt_aux, Fsqrt_aux2.
set (s1 := match Zcompare (EtoZ p' + EtoZ p' - EtoZ (mantissa_digits nx)) 0 with Gt => exponent_sub (exponent_add p' p') (mantissa_digits nx) | _ => exponent_zero end).
set (s2 := Zmax (2 * Zpos (prec p) - Zdigits radix (Zpos (MtoP nx))) 0).
assert (Hs: EtoZ s1 = s2).
  revert s1 s2 ; cbv zeta.
  replace (2 * Zpos (prec p))%Z with (Zpos (prec p) + Zpos (prec p))%Z by ring.
  rewrite digits_conversion.
  change radix with Carrier.radix.
  rewrite <- mantissa_digits_correct with (1 := Vx).
  case Zcompare_spec ;
    rewrite Hp ;
    try rewrite exponent_zero_correct ;
    intros H ;
    apply eq_sym ;
    try apply Zmax_right.
  now apply Zlt_le_weak.
  now apply Zeq_le.
  rewrite exponent_sub_correct.
  rewrite exponent_add_correct.
  rewrite Hp.
  apply Zmax_left.
  now apply Zle_ge, Zlt_le_weak.
clearbody s1 s2.
generalize (exponent_div2_floor_correct (exponent_sub ex s1)).
case exponent_div2_floor ; intros e1 r He.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
set (s3 := if r then exponent_add s1 exponent_one else s1).
set (s4e2 := if Z.even (EtoZ ex - s2) then (s2, EtoZ ex - s2)%Z else (s2 + 1, EtoZ ex - s2 - 1)%Z).
assert (Hes: EtoZ e1 = Z.div2 (snd s4e2) /\ EtoZ s3 = fst s4e2).
  clear -He Hs.
  generalize (Zdiv2_odd_eqn (EtoZ ex - s2)).
  rewrite Zodd_even_bool.
  rewrite exponent_sub_correct, Hs in He.
  assert (Z.even (EtoZ ex - s2) = negb r).
    rewrite He at 1 3.
    rewrite (Zplus_comm (2 * EtoZ e1)).
    rewrite Z.even_add_mul_2.
    now case r.
  rewrite H.
  rewrite negb_involutive.
  change Zeven with Z.even in s4e2.
  intros H'.
  revert s4e2 s3 ; cbv zeta.
  rewrite H.
  destruct r ; simpl.
  split.
  rewrite H'.
  replace (2 * Z.div2 (EtoZ ex - s2) + 1 - 1)%Z with (2 * Z.div2 (EtoZ ex - s2))%Z by ring.
  rewrite Z.div2_div.
  rewrite Zmult_comm, Z_div_mult by easy.
  omega.
  rewrite exponent_add_correct.
  rewrite exponent_one_correct.
  now rewrite Hs.
  split.
  omega.
  exact Hs.
clearbody s4e2 s3.
destruct s4e2 as [s4 e2].
simpl in Hes.
rewrite <- (proj2 Hes).
rewrite <- (proj1 Hes).
clear He Hes.
set (m1 := match Zcompare (EtoZ s3) 0 with Gt => mantissa_shl nx s3 | _ => nx end).
set (m2 := match EtoZ s3 with Zpos p => (Zpos (MtoP nx) * Z.pow_pos radix p)%Z | _ => Zpos (MtoP nx) end).
assert (Hm: valid_mantissa m1 /\ Zpos (MtoP m1) = m2).
  revert m1 m2 ; cbv zeta.
  case_eq (EtoZ s3) ; simpl Zcompare ; cbv iota.
  intros _.
  now split.
  intros q Hq.
  generalize (mantissa_shl_correct q nx s3 Vx Hq).
  intros [-> H].
  apply (conj H).
  apply shift_correct.
  intros q Hq.
  now split.
generalize (mantissa_sqrt_correct m1 (proj1 Hm)).
rewrite <- (proj2 Hm).
clearbody m1 m2.
clear Hm.
destruct (mantissa_sqrt m1) as [q l].
destruct (Z.sqrtrem (Z.pos (MtoP m1))) as [s r'].
intros [<- [H1 H2]].
rewrite round_aux_correct with (1 := H2).
unfold prec at 1.
rewrite Hp.
clear -H1.
apply (f_equal (fun l => FtoX (Fround_at_prec mode (prec p) (Ufloat _ _ _ l)))).
destruct l.
now rewrite Zeq_bool_true.
rewrite Zeq_bool_false.
now rewrite Zle_bool_true.
now apply Zgt_not_eq.
easy.
rewrite Zeq_bool_false.
now rewrite Zle_bool_false.
apply Zgt_not_eq.
now apply Zlt_trans with (2 := H1).
Qed.

(*
 * nearbyint
 *)

Definition nearbyint mode (f : type) :=
  match f with
  | Fnan => f
  | Float m e =>
    match mantissa_sign m with
    | Mnumber s m => round_at_exp_aux mode exponent_zero s m e pos_Eq
    | Mzero => zero
    end
  end.

Lemma nearbyint_correct :
  forall mode x,
  toX (nearbyint mode x) = Xnearbyint mode (toX x).
Proof.
intros mode x.
unfold toX.
destruct x as [|mx ex] ; try easy.
simpl.
generalize (mantissa_sign_correct mx).
case (mantissa_sign mx).
- rewrite toF_zero.
  simpl.
  now rewrite (Rnearbyint_IZR mode 0).
intros s m [_ H].
rewrite <- Fnearbyint_exact_correct.
rewrite round_at_exp_aux_correct; try easy.
unfold Fnearbyint_exact.
eapply f_equal.
eapply f_equal2; try easy.
now rewrite exponent_zero_correct.
Qed.

End SpecificFloat.
