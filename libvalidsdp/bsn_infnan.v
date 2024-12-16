Require Import ZArith Bool Reals mathcomp.analysis.Rstruct Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype.

Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLX.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Core.Round_NE.
Import Zaux.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.
Import BinarySingleNaN.
Require float_infnan_spec.
Import Defs SpecFloat Float_prop.
Require Import float_infnan_spec float_spec flocq_float.

Section Flocq_infnan.


  Context {precp: positive}.
  Context {emax: Z}.
  Definition prec := Zpos precp.
  Context {prec_gt_1: (1 < prec)%Z}.  (* need this for sqrt rounding *)
  Context {prec_lt_emax_bool: Z.ltb prec emax}.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.

Local Instance Hprec : FLX.Prec_gt_0 prec := refl_equal _.

Local Instance Hprec_emax : Prec_lt_emax prec emax :=
  @prec_lt_emax _ _ prec_lt_emax_bool.

Let Hemax : (3 <= emax)%Z.
Proof.
pose proof prec_gt_1.
pose proof Hprec_emax. red in H0.
lia.
Qed.

(** Binary64 defined in [Fappli_IEEE_bits]. *)
Definition FI := BinarySingleNaN.binary_float prec emax.

Definition FI0 : FI := B754_zero false.

Definition FI1 := Bone. (* B754_finite false big_mantissa (1-prec) FI1_proof. *)

Definition finite (x : FI) := is_finite x = true.

Lemma finite0 : finite FI0.
Proof. now simpl. Qed.

Lemma finite1 : finite FI1.
Proof. apply is_finite_Bone. Qed.

Definition fis := @flocq_float _ _ prec_gt_1 prec_lt_emax_bool.

Definition m := bpow radix2 emax.

Lemma m_ge_2 : 2 <= m.
Proof. pose proof Hprec_emax. red in H.
   unfold m. 
   change 2 with (bpow radix2 1); apply bpow_le. lia.
Qed.

Program Definition FI2FS (x : FI) : FS fis := @Build_FS_of _ (B2R x) _.
Next Obligation.
move=> x; apply/eqP; apply (generic_format_B2R prec emax x).
Qed.

Lemma FI2FS_spec x : (FI2FS x <> 0 :> R) -> finite x.
Proof. case x; unfold finite; auto. Qed.

Lemma FI2FS0 : FI2FS (FI0) = F0 fis :> R.
Proof. by []. Qed.

Lemma FI2FS1 : FI2FS (FI1) = F1 fis :> R.
Proof.
  apply Bone_correct.
Qed.

Definition firnd (x : R) : FI :=
  BinarySingleNaN.binary_normalize
    prec emax (Logic.eq_refl _) Hprec_emax
    mode_NE
    (round_mode mode_NE (scaled_mantissa radix2 fexp x))
    (cexp radix2 fexp x)
    false.

Lemma firnd_spec x : finite (firnd x) -> FI2FS (firnd x) = float_spec.frnd fis x :> R.
Proof.
intro Frx.
unfold FI2FS, firnd; simpl.
set (mx := round_mode mode_NE (scaled_mantissa radix2 fexp x)).
set (ex := cexp radix2 fexp x).
assert (H := binary_normalize_correct prec emax _ _ mode_NE mx ex false).
revert H; simpl; case (Rlt_bool (Rabs _) _).
{ unfold mx, round_mode; intro H; destruct H as (H, _); rewrite H.
  rewrite round_generic; [now unfold round|].
  now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N]. }
unfold binary_overflow, overflow_to_inf.
change (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _) with (firnd x).
revert Frx; unfold finite, is_finite, B2SF; case (firnd x); try discriminate.
Qed.

Lemma firnd_spec_f x : Rabs (float_spec.frnd fis x) < m -> finite (firnd x).
Proof.
intro Hm.
set (mx := round_mode mode_NE (scaled_mantissa radix2 fexp x)).
set (ex := cexp radix2 fexp x).
assert (H := binary_normalize_correct
               prec emax _ _
               mode_NE mx ex false).
revert H; simpl.
replace (round _ _ _ _) with (float_spec.frnd fis x : R).
rewrite (Rlt_bool_true _ _ Hm); intros [? [? ?]]; auto.
rewrite round_generic; [now unfold round|].
now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
Qed.

Definition fiopp : FI -> FI := Bopp.

Lemma fiopp_spec x : finite (fiopp x) -> FI2FS (fiopp x) = fopp (FI2FS x) :> R.
Proof. now intro Hox; rewrite /= B2R_Bopp. Qed.

Lemma fiopp_spec_f1 x : finite (fiopp x) -> finite x.
Proof. case x; unfold finite; auto. Qed.

Lemma fiopp_spec_f x : finite x -> finite (fiopp x).
Proof. case x; unfold finite; auto. Qed.

Definition fiplus (x y : FI) : FI := Bplus mode_NE x y.

Lemma fiplus_spec_fl x y : finite (fiplus x y) -> finite x.
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
  FI2FS (fiplus x y) = fplus (FI2FS x) (FI2FS y) :> R.
Proof.
intro Fxy.
assert (Fx := fiplus_spec_fl _ _ Fxy); assert (Fy := fiplus_spec_fr _ _ Fxy).
unfold FI2FS, fiplus, fplus, FS_val, float_spec.frnd, fis, flocq_float, frnd.
assert (H := Bplus_correct _ _ Hprec Hprec_emax mode_NE _ _ Fx Fy).
revert H; case (Rlt_bool _ _); intro H; destruct H as (H, _); [now rewrite H|].
exfalso; revert Fxy H.
fold (fiplus x y).
now case (fiplus x y).
Qed.

Lemma fiplus_spec_f x y : finite x -> finite y ->
  Rabs (fplus (FI2FS x) (FI2FS y)) < m -> finite (fiplus x y).
Proof.
intros Fx Fy Hm.
assert (H := Bplus_correct _ _ Hprec Hprec_emax mode_NE _ _ Fx Fy).
revert H.
replace (round _ _ _ _) with (fplus (FI2FS x) (FI2FS y) : R); [|now simpl].
rewrite (Rlt_bool_true _ _ Hm); intro.
apply H.
Qed.

Definition fimult (x y : FI) : FI := Bmult mode_NE x y.

Lemma fimult_spec_fl x y : finite (fimult x y) -> finite x.
Proof.
case x; case y; unfold finite, fimult; auto.
Qed.

Lemma fimult_spec_fr x y : finite (fimult x y) -> finite y.
Proof.
case x; case y; unfold finite, fimult; auto.
Qed.

Lemma fimult_spec x y : finite (fimult x y) ->
  FI2FS (fimult x y) = fmult (FI2FS x) (FI2FS y) :> R.
Proof.
intro Fxy.
unfold FI2FS, fimult, fmult, float_spec.frnd, fis, flocq_float, FS_val, frnd.
assert (H := Bmult_correct _ _ Hprec Hprec_emax mode_NE x y).
revert H; case (Rlt_bool _ _); intro H; [now rewrite (proj1 H)|].
exfalso; revert Fxy H.
fold (fimult x y).
now case (fimult x y).
Qed.

Lemma fimult_spec_f x y : finite x -> finite y ->
  Rabs (fmult (FI2FS x) (FI2FS y)) < m -> finite (fimult x y).
Proof.
intros Fx Fy Hm.
assert (H := Bmult_correct _ _ Hprec Hprec_emax mode_NE x y).
revert H.
replace (round _ _ _ _) with (fmult (FI2FS x) (FI2FS y) : R); [|now simpl].
rewrite (Rlt_bool_true _ _ Hm).
rewrite Fx Fy; intro H. apply H.
Qed.

Definition fidiv (x y : FI) : FI := Bdiv mode_NE x y.

Lemma fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x.
Proof.
case x; case y; unfold finite, fidiv; auto.
Qed.


Lemma F2R_cond_pos_not_0 (b : bool) (m : positive) (e : Z) :
  F2R (Float radix2 (cond_Zopp b (Z.pos m)) e) <> 0.
Proof.
cut (0 < F2R (Float radix2 (Z.pos m) e)).
{ now rewrite F2R_cond_Zopp; case b; simpl; lra. }
now apply F2R_gt_0.
Qed.

Lemma fidiv_spec x y : finite (fidiv x y) -> finite y ->
  FI2FS (fidiv x y) = fdiv (FI2FS x) (FI2FS y) :> R.
Proof.
unfold FI2FS, fidiv.
intros Fxy Fy => /=.
assert (Nzy : B2R y <> 0).
{ revert Fxy Fy; case x; case y; unfold finite, Bdiv, B2R; auto;
  intros; apply F2R_cond_pos_not_0. }
assert (H := Bdiv_correct _ _ Hprec Hprec_emax mode_NE x _ Nzy).
revert H; case (Rlt_bool _ _); intro H.
{ now rewrite (proj1 H). }
exfalso; revert Fxy H.
fold (fidiv x y).
now case (fidiv x y).
Qed.

Lemma fidiv_spec_f x y : finite x -> (FI2FS y <> 0 :> R) ->
  Rabs (fdiv (FI2FS x) (FI2FS y)) < m -> finite (fidiv x y).
Proof.
intros Fx Nzy Hm.
assert (H := Bdiv_correct _ _ Hprec Hprec_emax mode_NE x _ Nzy).
revert H.
replace (round _ _ _ _) with (fdiv (FI2FS x) (FI2FS y) : R); [|now simpl].
rewrite (Rlt_bool_true _ _ Hm).
now fold prec; rewrite Fx; intro H.
Qed.

Definition fisqrt (x : FI) : FI := Bsqrt mode_NE x.

Lemma fisqrt_spec_f1 x : finite (fisqrt x) -> finite x.
Proof.
case x; unfold finite, fisqrt; simpl; try auto.
now intros b; case b.
Qed.

Lemma fisqrt_spec x : finite (fisqrt x) -> FI2FS (fisqrt x) = fsqrt (FI2FS x) :> R.
Proof.
unfold FI2FS, fisqrt.
intros Fx => /=.
assert (H := Bsqrt_correct _ _ Hprec Hprec_emax mode_NE x).
now rewrite (proj1 H).
Qed.

Lemma fisqrt_spec_f x : finite x -> FI2FS x >= 0 -> finite (fisqrt x).
Proof.
assert (H := Bsqrt_correct _ _ Hprec Hprec_emax mode_NE x).
destruct H as (_, (H, _)); revert H.
replace (Bsqrt _ _ : binary_float prec emax) with (fisqrt x).
{ intro H; unfold finite; rewrite H; unfold is_finite, FI2FS, B2R; simpl.
  case x; try auto; intros b m e _ _; case b; [|now auto].
  unfold F2R, IZR; simpl; intro H'; exfalso; revert H'.
  change R0 with 0%Re.
  apply Rgt_not_ge; rewrite <- Ropp_0, Ropp_mult_distr_l_reverse.
  apply Ropp_lt_gt_contravar, Rmult_lt_0_compat; [|now apply bpow_gt_0].
  rewrite <-INR_IPR; apply pos_INR_nat_of_P. }
now simpl.
Qed.

Definition ficompare (x y : FI) : PrimFloat.float_comparison :=
  FloatAxioms.flatten_cmp_opt (Bcompare x y).

Lemma ficompare_spec (x y: FI) : Flocq_infnan.finite x -> Flocq_infnan.finite y ->
  ficompare x y = FloatAxioms.flatten_cmp_opt (Some (Rcompare (FI2FS x) (FI2FS y))).
Proof. now intros Fx Fy; unfold ficompare; rewrite Bcompare_correct. Qed.

Lemma ficompare_spec_eq x y : ficompare x y = PrimFloat.FEq -> FI2FS x = FI2FS y :> R.
Proof.
unfold ficompare => H /=; move: H.
case x; case y; try now simpl.
{ now intro b; case b. }
{ now intros b m e e' b'; case b'. }
{ now intros b b'; case b'. }
{ now intros b b'; case b'; case b. }
intros s m e Hb s' m' e' Hb'; case s', s; simpl;
  (destruct (Z.compare_spec e' e) as [He|He|He]; try discriminate;
   rewrite He Pos.compare_cont_spec; unfold Pos.switch_Eq;
   destruct (Pos.compare_spec m' m) as [Hm|Hm|Hm]; try discriminate;
   now rewrite Hm).
Qed.

Lemma ficompare_spec_eq_f x y : ficompare x y = PrimFloat.FEq ->
  (Flocq_infnan.finite x <-> Flocq_infnan.finite y).
Proof.
unfold ficompare.
case x; case y; try now simpl;
  try (now intros b pl Hpl b'; case b').
{ now intro b; case b. }
{ now intros b b'; simpl; case b'. }
{ now intros b m e He b'; simpl; case b'. }
now intros b b'; case b'; case b.
Qed.

Definition bsn_infnan : Float_infnan_spec :=
  @Build_Float_infnan_spec
    FI
    FI0
    FI1
    is_finite
    finite0
    finite1
    fis
    m
    m_ge_2
    FI2FS
    FI2FS_spec
    FI2FS0
    FI2FS1
    Flocq_infnan.firnd
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
    fisqrt_spec_f
    ficompare
    ficompare_spec
    ficompare_spec_eq
    ficompare_spec_eq_f.

End Flocq_infnan.


