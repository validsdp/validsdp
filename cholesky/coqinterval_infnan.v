(** * CoqInterval floats satisfy hypothesis in [Float_infnan_spec] *)

Require Import Reals.

Require Import BigZ.

Require Import float_spec flx64 float_infnan_spec.

Require Import Flocq.Core.Fcore_Zaux.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Core.Fcore_defs.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_FLX.
Require Import Flocq.Core.Fcore_float_prop.

Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_generic.
Require Import Interval.Interval_generic_proof.
Require Import Interval.Interval_xreal.

Module F := SpecificFloat BigIntRadix2.

Require Import Psatz.

Open Scope R_scope.

Section Coqinterval_infnan.

Let prec := 53%Z.

(** Binary64 defined in [Fappli_IEEE_bits]. *)
Definition FI := F.type.

Definition FI0 := F.zero.

Definition finite (x : FI) :=
  match F.toF x with
    | Fnan => False
    | Fzero => True
    | Float _ m e => (Zpos m < Z.pow 2 53)%Z
  end.

Lemma finite0 : finite FI0.
Proof. now unfold finite, FI0. Qed.

Definition fis := flx64.flx64 (fun m => negb (Zeven m)).

Definition m := 2.

Lemma m_ge_2 : 2 <= m.
Proof. apply Rle_refl. Qed.

Let FI2F_proof (s : bool) (m : positive) (e : Z)
    (H : (Zpos m < Z.pow 2 53)%Z) :
  generic_format radix2 (FLX_exp 53) (FtoR radix2 s m e).
Proof.
apply generic_format_FLX.
unfold FLX_format.
exists {| Fnum := if s then Z.neg m else Z.pos m; Fexp := e |}.
split.
{ unfold FtoR, F2R; simpl.
  case e; [|intro p|intro p].
  { now rewrite Rmult_1_r. }
  { now rewrite Z2R_mult. }
  now simpl. }
simpl; case s.
{ rewrite (Z.abs_neq _ (Pos2Z.neg_is_nonpos _)).
  now rewrite Pos2Z.opp_neg. }
now rewrite (Z.abs_eq _ (Zle_0_pos _)).
Qed.

Definition FI2F (x : FI) : F fis :=
  match F.toF x with
    | Fnan => F0 fis
    | Fzero => F0 fis
    | Float s m e =>
      match Z_lt_ge_dec (Z.pos m) (2 ^ 53) with
        | left H =>
          {| F_val := FtoR radix2 s m e; F_prop := FI2F_proof s m e H |}
        | right _ => F0 fis
      end
  end.

Lemma FI2F_spec x : (FI2F x <> 0 :> R) -> finite x.
Proof.
unfold finite, FI2F; case (F.toF x); auto; intros s m e.
case (Z_lt_ge_dec _ _); auto.
now simpl; intros _ H0; casetype False; apply H0.
Qed.

Lemma FI2F0 : FI2F (FI0) = F0 fis :> R.
Proof. now simpl. Qed.

Definition firnd (x : R) : FI :=
  let f := frnd fis x in
  let m := Ztrunc (scaled_mantissa radix2 (FLX_exp 53) f) in
  let e := canonic_exp radix2 (FLX_exp 53) f in
  let f' := match m with
    | Zpos p => Float false p e
    | Z0 => Fzero
    | Zneg p => Float true p e end in
  F.fromF f'.

Lemma toF_fromF_id (x : float radix2) : F.toF (F.fromF x) = x.
Proof.
unfold F.toF, F.fromF.
case x; auto.
intros s m e; case s; auto.
{ unfold BigIntRadix2.mantissa_sign, BigIntRadix2.ZtoM; simpl.
  unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
  rewrite Cyclic31.spec_0, BigN.BigN.spec_of_pos; simpl.
  unfold BigIntRadix2.MtoP; rewrite BigN.BigN.spec_of_pos.
  now rewrite BigIntRadix2.ZtoE_correct. }
unfold BigIntRadix2.mantissa_sign, BigIntRadix2.ZtoM; simpl.
unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
rewrite Cyclic31.spec_0, BigN.BigN.spec_of_pos; simpl.
unfold BigIntRadix2.MtoP; rewrite BigN.BigN.spec_of_pos.
now rewrite BigIntRadix2.ZtoE_correct.
Qed.

Lemma firnd_spec x : finite (firnd x) -> FI2F (firnd x) = frnd fis x :> R.
Proof.
unfold FI2F, firnd, finite; simpl; rewrite toF_fromF_id.
set (f := Fcore_generic_fmt.round _ _ _ _).
set (m := Ztrunc _).
case_eq m; [intros Hm _|intros p Hp Frx|intros p Hp Frx]; simpl.
{ rewrite <- (Rmult_0_l (bpow radix2 (canonic_exp radix2 (FLX_exp 53) f))).
  change 0 with (Z2R 0); rewrite <- Hm.
  change (_ * _) with (Fcore_generic_fmt.round radix2 (FLX_exp 53) Ztrunc f).
  rewrite round_generic; auto; [now apply valid_rnd_ZR|].
  now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N]. }
{ case (Z_lt_ge_dec _ _); intro H; simpl.
  { rewrite Interval_generic_proof.FtoR_split, <- Hp.
    change (F2R _) with (Fcore_generic_fmt.round radix2 (FLX_exp 53) Ztrunc f).
    rewrite round_generic; auto; [now apply valid_rnd_ZR|].
    now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N]. }
  now casetype False. }
case (Z_lt_ge_dec _ _); intro H; simpl.
{ rewrite Interval_generic_proof.FtoR_split.
  unfold cond_Zopp, Z.opp; rewrite <- Hp.
  change (F2R _) with (Fcore_generic_fmt.round radix2 (FLX_exp 53) Ztrunc f).
  rewrite round_generic; auto; [now apply valid_rnd_ZR|].
  now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N]. }
now casetype False.
Qed.

Lemma Zceil_lt n x : (n < Zceil x)%Z -> Z2R n < x.
Proof.
intro H.
case (Rlt_or_le (Z2R n) x); [now auto|intro Hle; casetype False].
now revert H; apply Zle_not_lt; rewrite <- Zceil_Z2R; apply Zceil_le.
Qed.

Lemma Zfloor_lt x n : (Zfloor x < n)%Z -> x < Z2R n.
Proof.
intro H.
case (Rlt_or_le x (Z2R n)); [now auto|intro Hle; casetype False].
now revert H; apply Zle_not_lt; rewrite <- (Zfloor_Z2R n); apply Zfloor_le.
Qed.

Lemma Ztrunc_gt_0 : forall x, (0 < Ztrunc x)%Z -> 0 < x.
Proof.
intros x Hx.
case (Rlt_or_le 0 x); [now auto|intro Hle].
rewrite (Ztrunc_ceil _ Hle) in Hx.
now change 0 with (Z2R 0); apply Zceil_lt.
Qed.

Lemma Ztrunc_lt_0 : forall x, (Ztrunc x < 0)%Z -> x < 0.
Proof.
intros x Hx.
case (Rlt_or_le x 0); [now auto|intro Hle].
rewrite (Ztrunc_floor _ Hle) in Hx.
now change 0 with (Z2R 0); apply Zfloor_lt.
Qed.

Lemma firnd_spec_f_aux x : finite (firnd x).
Proof.
unfold finite, firnd; rewrite toF_fromF_id.
set (m := scaled_mantissa _ _ _).
assert (Hm : (Ztrunc (Rabs m) < 2 ^ 53)%Z).
{ rewrite (Ztrunc_floor _ (Rabs_pos _)).
  apply lt_Z2R, (Rle_lt_trans _ _ _ (Zfloor_lb _)).
  apply (Rlt_le_trans _ _ _ (abs_scaled_mantissa_lt_bpow _ _ _)).
  unfold canonic_exp, FLX_exp.
  rewrite Z.sub_sub_distr, Z.sub_diag, Z.add_0_l.
  now rewrite <- Z2R_Zpower; [apply Rle_refl|]. }
set (zm := Ztrunc m).
case_eq zm; auto; intros p Hp.
{ rewrite <- Hp; unfold zm.
  rewrite <- (Rabs_pos_eq m); [assumption|].
  now apply Rlt_le, Ztrunc_gt_0; fold m zm; rewrite Hp. }
rewrite <- Pos2Z.opp_neg, <- Hp; unfold m.
rewrite <- Z.abs_neq; [|now rewrite Hp].
now unfold zm; rewrite <- Ztrunc_abs.
Qed.

Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
Proof. intros _; apply firnd_spec_f_aux. Qed.

Definition X2F (x : ExtendedR) : F fis :=
  match x with
  | Xnan => F0 fis
  | Xreal r => frnd fis r
  end.

Lemma FI2F_X2F_FtoX x : finite x -> FI2F x = X2F (FtoX (F.toF x)) :> R.
Proof.
case x; [now simpl|]; intros m e.
unfold FI2F, F.toF, finite; simpl.
case (BigIntRadix2.mantissa_sign m).
{ now simpl; unfold frnd; rewrite round_0; [|apply valid_rnd_N]. }
intros s m' Hm'.
case (Z_lt_ge_dec _ _); [|now simpl].
intro H; simpl.
now rewrite round_generic; [|apply valid_rnd_N|apply FI2F_proof].
Qed.

Definition fiopp := F.neg.

Lemma fiopp_spec_f1 x : finite (fiopp x) -> finite x.
Proof.
unfold finite, fiopp.
case x; [now simpl|]; intros m e.
unfold F.neg, F.toF.
case (BigIntRadix2.mantissa_sign m); [now simpl|]; intros s m'.
case s.
{ unfold BigIntRadix2.mantissa_sign, BigIntRadix2.mantissa_pos.
  case_eq (BigZ.BigZ.eqb (BigZ.BigZ.Pos m') (BigZ.BigZ.Pos 0)); [|now auto].
  intro Hbe; apply BigZ.BigZeqb_correct in Hbe.
  unfold BigZ.BigZ.eq in Hbe; simpl in Hbe.
  now unfold BigIntRadix2.MtoP; rewrite Hbe, Cyclic31.spec_0. }
unfold BigIntRadix2.mantissa_sign, BigIntRadix2.mantissa_neg.
case_eq (BigZ.BigZ.eqb (BigZ.BigZ.Neg m') (BigZ.BigZ.Pos 0)); [|now auto].
intro Hbe; apply BigZ.BigZeqb_correct in Hbe.
unfold BigZ.BigZ.eq in Hbe; simpl in Hbe.
apply (f_equal Z.opp) in Hbe.
rewrite Cyclic31.spec_0, <- Z.opp_0 in Hbe.
do 2 (rewrite Z.opp_involutive in Hbe).
now unfold BigIntRadix2.MtoP; rewrite Hbe.
Qed.

Lemma fiopp_spec_f x : finite x -> finite (fiopp x).
Proof.
unfold finite, fiopp.
case x; [now simpl|]; intros m e.
unfold F.neg, F.toF.
case_eq (BigIntRadix2.mantissa_sign m).
{ now intro Hm; rewrite Hm. }
intros s m' Hm Hm'.
case s.
{ unfold BigIntRadix2.mantissa_sign, BigIntRadix2.mantissa_pos.
  now case_eq (BigZ.BigZ.eqb (BigZ.BigZ.Pos m') (BigZ.BigZ.Pos 0)). }
unfold BigIntRadix2.mantissa_sign, BigIntRadix2.mantissa_neg.
now case_eq (BigZ.BigZ.eqb (BigZ.BigZ.Neg m') (BigZ.BigZ.Pos 0)).
Qed.

Lemma fiopp_spec x : finite (fiopp x) -> FI2F (fiopp x) = fopp (FI2F x) :> R.
Proof.
intro Fox.
rewrite (FI2F_X2F_FtoX _ Fox).
rewrite F.neg_correct, Fneg_correct.
simpl.
change flx64.format with (format fis).
rewrite (FI2F_X2F_FtoX _ (fiopp_spec_f1 _ Fox)).
unfold Xneg; case (FtoX _).
{ now unfold X2F, F0; simpl; rewrite Ropp_0. }
intro r; apply Fcore_rnd_ne.round_NE_opp.
Qed.

Definition fiplus : FI -> FI -> FI := F.add rnd_NE 53%bigZ.

Lemma fiplus_spec_fl x y : finite (fiplus x y) -> finite x.  (* faux *)
Proof.
case x; case y; unfold finite, fiplus; simpl; try auto.
now intros b b'; case (Bool.eqb b' b).
Qed.

Lemma fiplus_spec_fr x y : finite (fiplus x y) -> finite y.
Proof.
case x; case y; unfold finite, fiplus; simpl; try auto.
now intros b b'; case (Bool.eqb b' b).
Qed.

Lemma fiplus_spec x y : finite (fiplus x y) ->
  FI2F (fiplus x y) = fplus (FI2F x) (FI2F y) :> R.
Proof.
intro Fxy.
assert (Fx := fiplus_spec_fl _ _ Fxy); assert (Fy := fiplus_spec_fr _ _ Fxy).
unfold FI2F, fiplus, b64_plus, prec, emax.
change ((53 ?= 1024)%Z) with Lt; simpl.
assert (H := Bplus_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           binop_nan_pl64 mode_NE _ _ Fx Fy).
revert H; case (Rlt_bool _ _); intro H; destruct H as (H, _); [now rewrite H|].
casetype False; revert Fxy H.
change Lt with ((0 ?= 53)%Z) at 1.
change Lt with ((53 ?= 1024)%Z).
fold b64_plus; fold (fiplus x y).
now case (fiplus x y).
Qed.

Lemma fiplus_spec_f x y : finite x -> finite y ->
  Rabs (fplus (FI2F x) (FI2F y)) < m -> finite (fiplus x y).
Proof.
intros Fx Fy Hm.
assert (H := Bplus_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           binop_nan_pl64 mode_NE _ _ Fx Fy).
revert H.
replace (round _ _ _ _) with (fplus (FI2F x) (FI2F y) : R); [|now simpl].
now fold emax m; rewrite (Rlt_bool_true _ _ Hm); intro.
Qed.

Definition fimult (x y : FI) : FI := b64_mult mode_NE x y.

Lemma fimult_spec_fl x y : finite (fimult x y) -> finite x.
Proof.
case x; case y; unfold finite, fimult; auto.
Qed.

Lemma fimult_spec_fr x y : finite (fimult x y) -> finite y.
Proof.
case x; case y; unfold finite, fimult; auto.
Qed.

Lemma fimult_spec x y : finite (fimult x y) ->
  FI2F (fimult x y) = fmult (FI2F x) (FI2F y) :> R.
Proof.
intro Fxy.
unfold FI2F, fimult, b64_mult, prec, emax.
change (53 ?= 1024)%Z with Lt; simpl.
assert (H := Bmult_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           binop_nan_pl64 mode_NE x y).
revert H; case (Rlt_bool _ _); intro H; [now rewrite (proj1 H)|].
casetype False; revert Fxy H.
change Lt with ((0 ?= 53)%Z) at 1.
change Lt with ((53 ?= 1024)%Z).
fold b64_mult; fold (fimult x y).
now case (fimult x y).
Qed.

Lemma fimult_spec_f x y : finite x -> finite y ->
  Rabs (fmult (FI2F x) (FI2F y)) < m -> finite (fimult x y).
Proof.
intros Fx Fy Hm.
assert (H := Bmult_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           binop_nan_pl64 mode_NE x y).
revert H.
replace (round _ _ _ _) with (fmult (FI2F x) (FI2F y) : R); [|now simpl].
fold emax m; rewrite (Rlt_bool_true _ _ Hm).
now fold prec; rewrite Fx, Fy; intro H.
Qed.

Definition fidiv (x y : FI) : FI := b64_div mode_NE x y.

Lemma fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x.
Proof.
case x; case y; unfold finite, fidiv; auto.
Qed.

Lemma F2R_cond_pos_not_0 (b : bool) (m : positive) (e : Z) :
  F2R (Float radix2 (cond_Zopp b (Z.pos m)) e) <> 0.
Proof.
cut (0 < F2R (Float radix2 (Z.pos m) e)).
{ now rewrite F2R_cond_Zopp; case b; simpl; lra. }
now apply F2R_gt_0_compat.
Qed.

Lemma fidiv_spec x y : finite (fidiv x y) -> finite y ->
  FI2F (fidiv x y) = fdiv (FI2F x) (FI2F y) :> R.
Proof.
unfold FI2F, fidiv, b64_div, prec, emax.
change (53 ?= 1024)%Z with Lt; simpl.
intros Fxy Fy.
assert (Nzy : B2R prec emax y <> 0).
{ revert Fxy Fy; case x; case y; unfold finite, Bdiv, B2R; auto;
  intros; apply F2R_cond_pos_not_0. }
assert (H := Bdiv_correct 53 1024
                          (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                          binop_nan_pl64 mode_NE x _ Nzy).
revert H; case (Rlt_bool _ _); intro H.
{ now rewrite (proj1 H). }
casetype False; revert Fxy H.
change Lt with ((0 ?= 53)%Z) at 1.
change Lt with ((0 ?= 53)%Z) at 2.
change Lt with ((53 ?= 1024)%Z).
fold b64_div; fold (fidiv x y).
now case (fidiv x y).
Qed.

Lemma fidiv_spec_f x y : finite x -> (FI2F y <> 0 :> R) ->
  Rabs (fdiv (FI2F x) (FI2F y)) < m -> finite (fidiv x y).
Proof.
intros Fx Nzy Hm.
assert (H := Bdiv_correct 53 1024
                          (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                          binop_nan_pl64 mode_NE x _ Nzy).
revert H.
replace (round _ _ _ _) with (fdiv (FI2F x) (FI2F y) : R); [|now simpl].
fold emax m; rewrite (Rlt_bool_true _ _ Hm).
now fold prec; rewrite Fx; intro H.
Qed.

Definition fisqrt (x : FI) : FI := b64_sqrt mode_NE x.

Lemma fisqrt_spec_f1 x : finite (fisqrt x) -> finite x.
Proof.
case x; unfold finite, fisqrt; simpl; try auto.
now intros b; case b.
Qed.

Lemma fisqrt_spec x : finite (fisqrt x) ->
  FI2F (fisqrt x) = fsqrt (FI2F x) :> R.
Proof.
unfold FI2F, fisqrt, b64_sqrt, prec, emax.
change (53 ?= 1024)%Z with Lt; simpl.
intros Fx.
assert (H := Bsqrt_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           unop_nan_pl64 mode_NE x).
now rewrite (proj1 H).
Qed.

Lemma fisqrt_spec_f x : finite x -> FI2F x >= 0 -> finite (fisqrt x).
Proof.
assert (H := Bsqrt_correct 53 1024
                           (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                           unop_nan_pl64 mode_NE x).
destruct H as (_, (H, _)); revert H; fold prec emax.
replace (Bsqrt _ _ _ _ _ _ _ : binary_float prec emax) with (fisqrt x).
{ intro H; unfold finite; rewrite H; unfold is_finite, FI2F, B2R; simpl.
  case x; try auto; intros b m e _ _; case b; [|now auto].
  unfold F2R, Z2R; simpl; intro H'; casetype False; revert H'.
  apply Rgt_not_ge; rewrite <- Ropp_0, Ropp_mult_distr_l_reverse.
  apply Ropp_lt_gt_contravar, Rmult_lt_0_compat; [|now apply bpow_gt_0].
  rewrite P2R_INR; change 0 with (INR 0); apply lt_INR, Pos2Nat.is_pos. }
now simpl.
Qed.

Definition binary64_infnan : Float_infnan_spec :=
  @Build_Float_infnan_spec
    FI
    FI0
    finite
    finite0
    fis
    m
    m_ge_2
    FI2F
    FI2F_spec
    FI2F0
    firnd
    firnd_spec
    firnd_spec_f
    fiopp
    fiopp_spec
    fiopp_spec_f1
    fiopp_spec_f
    fiplus
    fiplus_spec
    fiplus_spec_fl
    fiplus_spec_fr
    fiplus_spec_f
    fimult
    fimult_spec
    fimult_spec_fl
    fimult_spec_fr
    fimult_spec_f
    fidiv
    fidiv_spec
    fidiv_spec_fl
    fidiv_spec_f
    fisqrt
    fisqrt_spec
    fisqrt_spec_f1
    fisqrt_spec_f.

End Binary64_infnan.
