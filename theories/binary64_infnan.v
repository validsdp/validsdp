(** * IEEE754 binary64 format satisfies hypothesis in [Float_infnan_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_infnan_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest with overflows and NaN. *)

Require Import Reals.

Require Import float_spec binary64 float_infnan_spec.

Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.

Require Import Flocq.Core.Fcore_Zaux.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Core.Fcore_defs.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_FLT.
Require Import Flocq.Core.Fcore_float_prop.

Require Import Psatz.

Open Scope R_scope.

Section Binary64_infnan.

Let prec := 53%Z.
Let emax := 1024%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.

(** Binary64 defined in [Fappli_IEEE_bits]. *)
Definition FI := binary64.

Definition FI0 := B754_zero prec emax false.

Lemma FI1_proof : bounded prec emax 4503599627370496 (-52) = true.
Proof. now simpl. Qed.

Definition FI1 := B754_finite prec emax false 4503599627370496 (-52) FI1_proof.

Definition finite (x : FI) := is_finite prec emax x = true.

Lemma finite0 : finite FI0.
Proof. now simpl. Qed.

Lemma finite1 : finite FI1.
Proof. now simpl. Qed.

Definition fis := binary64.binary64 (fun m => negb (Zeven m)).

Definition m := bpow radix2 emax.

Lemma m_ge_2 : 2 <= m.
Proof. now change 2 with (bpow radix2 1); apply bpow_le. Qed.

(* FIXME: rename to FI2FS ? *)
Definition FI2F (x : FI) : F fis :=
  {| F_val := B2R prec emax x; F_prop := generic_format_B2R prec emax x |}.

Lemma FI2F_spec x : (FI2F x <> 0 :> R) -> finite x.
Proof. case x; unfold finite; auto. Qed.

Lemma FI2F0 : FI2F (FI0) = F0 fis :> R.
Proof. now simpl. Qed.

Lemma FI2F1 : FI2F (FI1) = F1 fis :> R.
Proof.
apply Rinv_r; change 0 with (Z2R 0).
now change 4503599627370496 with (Z2R 4503599627370496); apply Z2R_neq.
Qed.

Definition firnd (x : R) : FI :=
  binary_normalize
    prec emax (@eq_refl comparison Lt) (@eq_refl comparison Lt)
    mode_NE
    (round_mode mode_NE (scaled_mantissa binary64.radix2 fexp x))
    (canonic_exp binary64.radix2 fexp x)
    false.

Lemma firnd_spec x : finite (firnd x) -> FI2F (firnd x) = frnd fis x :> R.
Proof.
intro Frx.
unfold FI2F, firnd; simpl.
set (mx := round_mode mode_NE (scaled_mantissa binary64.radix2 fexp x)).
set (ex := canonic_exp binary64.radix2 fexp x).
assert (H := binary_normalize_correct prec emax
                                      (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                                      mode_NE mx ex false).
revert H; case (Rlt_bool (Rabs _) _).
{ unfold mx, round_mode; intro H; destruct H as (H, _); rewrite H.
  rewrite round_generic; [now unfold round|now apply valid_rnd_N|].
  now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N]. }
unfold binary_overflow, overflow_to_inf.
change (binary_normalize _ _ _ _ _ _ _ _) with (firnd x).
revert Frx; unfold finite, is_finite, B2FF; case (firnd x); try discriminate.
Qed.

Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
Proof.
intro Hm.
set (mx := round_mode mode_NE (scaled_mantissa binary64.radix2 fexp x)).
set (ex := canonic_exp binary64.radix2 fexp x).
assert (H := binary_normalize_correct prec emax
                                      (@eq_refl comparison Lt) (@eq_refl comparison Lt)
                                      mode_NE mx ex false).
revert H.
replace (round _ _ _ _) with (frnd fis x : R).
{ now fold emax m; rewrite (Rlt_bool_true _ _ Hm); intro. }
rewrite round_generic; [now unfold round|now apply valid_rnd_N|].
now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
Qed.

Definition fiopp := b64_opp.

Lemma fiopp_spec x : finite (fiopp x) -> FI2F (fiopp x) = fopp (FI2F x) :> R.
Proof.
now intro Hox; unfold FI2F, fiopp, b64_opp, fopp; simpl; rewrite B2R_Bopp.
Qed.

Lemma fiopp_spec_f1 x : finite (fiopp x) -> finite x.
Proof. case x; unfold finite; auto. Qed.

Lemma fiopp_spec_f x : finite x -> finite (fiopp x).
Proof. case x; unfold finite; auto. Qed.

Definition fiplus (x y : FI) : FI := b64_plus mode_NE x y.

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

Definition ficompare (x y : FI) : option comparison := Bcompare 53 1024 x y.

Lemma ficompare_spec x y : finite x -> finite y ->
  ficompare x y = Some (Rcompare (FI2F x) (FI2F y)).
Proof. apply Bcompare_correct. Qed.

Lemma ficompare_spec_eq x y : ficompare x y = Some Eq -> FI2F x = FI2F y :> R.
Proof.
unfold ficompare.
case x; case y; try now simpl.
{ now intro b; case b. }
{ now intros b m e e' b'; case b'. }
{ now intros b b'; case b'. }
{ now intros b b'; case b'; case b. }
{ now intros b n b'; case b'. }
intros b m e B b' m' e' B'; simpl; case b'; case b; try now simpl.
{ case_eq (Z.compare e' e); try now simpl.
  intro He; apply Z.compare_eq in He; rewrite Pos.compare_cont_antisym; simpl.
  intro Hm; inversion Hm as (Hm'); apply Pcompare_Eq_eq in Hm'.
  now rewrite He, Hm'. }
case_eq (Z.compare e' e); try now simpl.
intro He; apply Z.compare_eq in He.
intro Hm; inversion Hm as (Hm'); apply Pcompare_Eq_eq in Hm'.
now rewrite He, Hm'.
Qed.

Lemma ficompare_spec_eq_f x y : ficompare x y = Some Eq ->
  (finite x <-> finite y).
Proof.
unfold ficompare.
case x; case y; try now simpl.
{ now intro b; case b. }
{ now intros b b'; simpl; case b'. }
{ now intros b m e He b'; simpl; case b'. }
{ now intros b b'; case b'; case b. }
now intros b n b'; case b'.
Qed.

Definition binary64_infnan : Float_infnan_spec :=
  @Build_Float_infnan_spec
    FI
    FI0
    FI1
    (is_finite prec emax)
    finite0
    finite1
    fis
    m
    m_ge_2
    FI2F
    FI2F_spec
    FI2F0
    FI2F1
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
    fisqrt_spec_f
    ficompare
    ficompare_spec
    ficompare_spec_eq
    ficompare_spec_eq_f.

End Binary64_infnan.
