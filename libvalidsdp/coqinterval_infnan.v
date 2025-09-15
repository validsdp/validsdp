(** * CoqInterval floats satisfy hypothesis in [Float_infnan_spec] *)

Require Import Reals.
Require Import Floats.
From Bignums Require Import BigZ.

Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Digits.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLX.

Require Import Interval.Float.Specific_bigint.
Require Import Interval.Float.Specific_ops.
Require Import Interval.Float.Basic.
Require Import Interval.Float.Generic_proof.
Require Import Interval.Real.Xreal.
Require Import Interval.Missing.Stdlib.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

From mathcomp Require Import Rstruct.

Require Import float_spec flx64 float_infnan_spec misc zulp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[global] Obligation Tactic := idtac.  (* no automatic intro *)

Module Bir := BigIntRadix2.

Module F := SpecificFloat Bir.
Module F' := Interval.Float.Sig.FloatExt F.

Notation toR := (fun f => proj_val (F.toX f)).

Lemma Xreal_inj x y : Xreal x = Xreal y -> x = y.
Proof. by case. Qed.

Require Import Psatz.

Open Scope R_scope.

Definition X_real (x : ExtendedR) :=
  match x with
  | Xnan => false
  | Xreal _ => true
  end.

Lemma FtoX_real (f : F.type) : F.real f = X_real (F.toX f).
Proof.
unfold F.real, X_real, F.toX; simpl; case f; [now simpl|].
now intros m e; simpl; case (Bir.mantissa_sign m).
Qed.

Lemma real_FtoX_toR f : F.real f -> F.toX f = Xreal (toR f).
Proof. by rewrite FtoX_real; rewrite /X_real; case: F.toX. Qed.

Section Signif_digits.

Let prec := 53%bigZ.

Definition x_bounded (x : ExtendedR) : Set :=
  ( x = Xnan ) + { r | x = Xreal r & FLX_format radix2 (BigZ.to_Z prec) r }.

Definition mantissa_bounded (x : F.type) := x_bounded (F.toX x).

(** * Number of radix2 digits of a [bigZ] number *)

Definition digits (m : bigZ) : bigZ :=
  match m with
  | BigZ.Pos n => Bir.mantissa_digits n
  | BigZ.Neg n => Bir.mantissa_digits n
  end.

Lemma digits_spec n : BigZ.to_Z (digits n) = Zdigits2 (BigZ.to_Z n).
Proof.
rewrite /digits; case: n => n.
have Hn : BigN.to_Z n = Z0 \/ BigN.to_Z n <> Z0.
{ case E: (BigN.to_Z n) => [|p|p]; [by left|by right|exfalso].
  by have := BigN.spec_pos n; rewrite E; auto. }
have {Hn} [Zn|NZn] := Hn.
{ rewrite /= Zn /= BigN.spec_sub.
  apply/Z.max_l_iff.
  rewrite BigN.spec_Ndigits BigN.spec_head00 //.
  lia. }
{ rewrite [LHS]Bir.mantissa_digits_correct; last first.
  { case E: (BigZ.to_Z (BigZ.Pos n)) NZn => [|p|p] //= NZn.
    exists p; by rewrite -E.
    clear NZn; exfalso; simpl in E.
    by have := BigN.spec_pos n; rewrite E; auto. }
  rewrite -digits_conversion.
  rewrite /Zdigits2; f_equal.
  rewrite /= /Bir.MtoP; simpl in NZn.
  have := BigN.spec_pos n; case: (BigN.to_Z n) NZn => [p|p|] NZn; try done. }
(* almost same proof *)
have Hn : BigN.to_Z n = Z0 \/ BigN.to_Z n <> Z0.
{ case E: (BigN.to_Z n) => [|p|p]; [by left|by right|exfalso].
  by have := BigN.spec_pos n; rewrite E; auto. }
have {Hn} [Zn|NZn] := Hn.
{ rewrite /= Zn /= BigN.spec_sub.
  apply/Z.max_l_iff.
  rewrite BigN.spec_Ndigits BigN.spec_head00 //.
  lia. }
{ rewrite [LHS]Bir.mantissa_digits_correct; last first.
  { case E: (BigZ.to_Z (BigZ.Pos n)) NZn => [|p|p] //= NZn.
    exists p; by rewrite -E.
    clear NZn; exfalso; simpl in E.
    by have := BigN.spec_pos n; rewrite E; auto. }
  rewrite -digits_conversion.
  rewrite [RHS]Zdigits_opp /Zdigits2; f_equal.
  rewrite /= /Bir.MtoP; simpl in NZn.
  have := BigN.spec_pos n; case: (BigN.to_Z n) NZn => [p|p|] NZn; try done. }
Qed.

Lemma digits_ge0 n :(0 <= digits n)%bigZ.
Proof.
apply/BigZ.leb_le.
rewrite BigZ.spec_leb digits_spec //.
exact/Z.leb_le/Zdigits_ge_0.
Qed.

Lemma digits_gt0 n : BigZ.to_Z n <> Z0 -> (0 < digits n)%bigZ.
Proof.
move=> NZn; apply/BigZ.ltb_lt.
rewrite BigZ.spec_ltb digits_spec //.
exact/Z.ltb_lt/Zdigits_gt_0.
Qed.

(** * Number of significant radix2 digits of a [bigZ] number *)

Definition signif_digits (m : bigZ) :=
  let d := digits m in
  let d' := digits (bigZulp m) in
  BigZ.succ (d - d').

Lemma signif_digits_correct m e :
  (signif_digits m <=? prec)%bigZ <=>
  mantissa_bounded (Specific_ops.Float m e).
Proof.
split => H.
{ rewrite /mantissa_bounded /x_bounded; right.
  exists (toR (Specific_ops.Float m e)); first by rewrite -real_FtoX_toR.
  rewrite /signif_digits in H.
  exists (Defs.Float radix2
                      (BigZ.to_Z (m / bigZulp m))
                      (BigZ.to_Z (digits (bigZulp m) - 1 + e))).
  { rewrite /F.toX /F.toF.
    case: Bir.mantissa_sign (Bir.mantissa_sign_correct m) =>[/=|s n].
    { rewrite /F2R /= BigZ.spec_div.
      by rewrite /Bir.MtoZ =>->; rewrite Zdiv.Zdiv_0_l Rmult_0_l. }
    case=> Hm Vn; rewrite /= FtoR_split.
    case: s Hm => Hm; rewrite /= -Hm /F2R /= /Bir.MtoZ /Bir.EtoZ.
    { rewrite BigZ.spec_add bpow_plus /= -Rmult_assoc; congr Rmult.
      rewrite -IZR_Zpower; last first.
      { rewrite BigZ.spec_sub digits_spec.
        apply(*:*) Z.lt_le_pred.
        apply: Zdigits_gt_0.
        rewrite /bigZulp BigZ.spec_land BigZ.spec_opp -/(Zulp (BigZ.to_Z m)).
        apply: Zulp_neq0.
        by move: Hm; rewrite /Bir.MtoZ =>->. }
      rewrite BigZ.spec_sub digits_spec.
      rewrite -mult_IZR; congr IZR.
      rewrite BigZ.spec_div BigZ.spec_land BigZ.spec_opp.
      rewrite -/(Zulp (BigZ.to_Z m)) /= Zulp_digits;
        last by move=> K; rewrite /Bir.MtoZ K in Hm.
      by rewrite Zulp_mul. }
    rewrite BigZ.spec_add bpow_plus /= -Rmult_assoc; congr Rmult.
    rewrite -IZR_Zpower; last first.
    { rewrite BigZ.spec_sub digits_spec.
      apply(*:*) Z.lt_le_pred.
      apply: Zdigits_gt_0.
      rewrite /bigZulp BigZ.spec_land BigZ.spec_opp -/(Zulp (BigZ.to_Z m)).
      apply: Zulp_neq0.
      by move: Hm; rewrite /Bir.MtoZ =>->. }
    rewrite BigZ.spec_sub digits_spec.
    rewrite -mult_IZR; congr IZR.
    rewrite BigZ.spec_div BigZ.spec_land BigZ.spec_opp.
    rewrite -/(Zulp (BigZ.to_Z m)) /= Zulp_digits;
      last by move=> K; rewrite /Bir.MtoZ K in Hm.
    by rewrite Zulp_mul. }
  (* could be extracted to some lemma *)
  have [_ H1] := Zdigits_correct radix2 (BigZ.to_Z (m / bigZulp m)).
  have H2 := @Zdigits2_Zulp_le (BigZ.to_Z m) (BigZ.to_Z prec).
  rewrite BigZ.spec_leb BigZ.spec_succ BigZ.spec_sub in H.
  rewrite !digits_spec bigZulp_spec in H.
  move/Z.leb_le in H.
  move/(_ H) in H2.
  rewrite !BigZ.spec_div !bigZulp_spec in H1 *.
  apply: (Z.lt_le_trans _ _ _ H1); exact: Zaux.Zpower_le. }
have {H} [|[r H1 [f Hf1 Hf2]]] := H; first by rewrite real_FtoX_toR.
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
case: Z.leb (Zbool.Zle_cases (Z.abs (BigZ.to_Z m)) (Z.abs f1)) => [Hle|Hlt].
{ move/(Zdigits_le radix2 _ _ (Z.abs_nonneg _)) in Hle.
  rewrite Zdigits_abs in Hle.
  move/(Zdigits_le_Zpower radix2) in Hf2.
  apply/Z.leb_le.
  have NZm : (BigZ.to_Z m) <> 0%Z by rewrite Hm; case: (s).
  have NZum : Zulp (BigZ.to_Z m) <> 0%Z by apply: Zulp_neq0.
  have H0 := Zdigits_gt_0 radix2 _ NZum.
  rewrite Zdigits_abs in Hle.
  clear - Hle Hf2 H0; rewrite /Zdigits2; lia. }
have NZf1 : f1 <> Z0.
{ move=> K; rewrite /F2R -/f1 K /= Rsimpl in H1.
  case: H1; rewrite FtoR_split /F2R /=.
  case/Rmult_integral.
  { by apply: eq_IZR_contrapositive; case: (s). }
  by apply: Rgt_not_eq; apply: bpow_gt_0. }
move/(Zdigits_le_Zpower radix2) in Hf2.
apply/Z.leb_le.
rewrite -/(Z.succ _) -Zdigits_div_ulp; last by rewrite Hm; case: (s).
apply: Z.le_trans _ Hf2.
rewrite /Zdigits2 -Zdigits_abs -(Zdigits_abs _ f1).
apply Zdigits_le; first exact: Z.abs_nonneg.
apply Znumtheory.Zdivide_bounds =>//.
apply Z.divide_abs_l.
have Hmf : (IZR (BigZ.to_Z m) * bpow radix2 (BigZ.to_Z e) = F2R f)%Re.
{ rewrite Hm; apply Xreal_inj; rewrite -{}H1; congr Xreal.
  rewrite FtoR_split /F2R /=.
  by case: (s). }
have Hlte : (bpow radix2 (BigZ.to_Z e) < bpow radix2 (Fexp f))%Re.
{ rewrite /F2R in Hmf.
  move/Z.gt_lt/IZR_lt in Hlt.
  rewrite !abs_IZR in Hlt.
  rewrite -/f1 in Hmf.
  move/(congr1 (Rdiv ^~ (bpow radix2 (BigZ.to_Z e)))) in Hmf.
  rewrite /Rdiv Rinv_r_simpl_l in Hmf; last exact/Rgt_not_eq/bpow_gt_0.
  rewrite {}Hmf in Hlt.
  rewrite !Rabs_mult in Hlt.
  apply/Rdiv_gt_1; first exact: bpow_gt_0.
  move/Rdiv_gt_1: Hlt.
  rewrite (_ : ?[a] * Rabs ?[b] * Rabs ?[c] / ?a = ?b * ?c)%Re; last first.
    rewrite (Rabs_pos_eq (bpow _ _)); last exact: bpow_ge_0.
    rewrite (Rabs_pos_eq (/ bpow _ _));
      last exact/Rlt_le/Rinv_0_lt_compat/bpow_gt_0.
    field.
    split; last by apply/Rabs_no_R0; exact: eq_IZR_contrapositive.
    exact/Rgt_not_eq/bpow_gt_0.
  apply.
  by apply/Rabs_pos_lt; exact: eq_IZR_contrapositive. }
move/lt_bpow in Hlte.
have {}Hmf : (BigZ.to_Z m = f1 * 2 ^ (Fexp f - BigZ.to_Z e))%Z.
{ clear - Hlte Hmf.
  rewrite /F2R - /f1 in Hmf.
  move/(congr1 (Rmult ^~ (bpow radix2 (- BigZ.to_Z e)))) in Hmf.
  rewrite !Rmult_assoc -!bpow_plus Z.add_opp_diag_r /= Rmult_1_r in Hmf.
  rewrite -IZR_Zpower in Hmf; last lia.
  rewrite -mult_IZR in Hmf.
  exact: eq_IZR. }
have Hdiv : (Z.abs (BigZ.to_Z m / Zulp (BigZ.to_Z m)) | BigZ.to_Z m)%Z.
{ apply/Z.divide_abs_l.
  apply Zdivide_div_l.
  by apply Zulp_divides. }
rewrite {3}Hmf Z.mul_comm in Hdiv.
apply (Znumtheory.Gauss _ (2 ^ (Fexp f - BigZ.to_Z e))) =>//.
apply: Zulp_rel_prime; last lia.
by rewrite Hm; case: (s).
Qed.

Definition is_mantissa_bounded (x : F.type) :=
  match x with
  | Specific_ops.Fnan => true
  | Specific_ops.Float m e => (signif_digits m <=? prec)%bigZ
  end.

Lemma mantissa_boundedP x : is_mantissa_bounded x <=> mantissa_bounded x.
Proof.
case: x => [|m e] /=; first by split =>//; left.
exact: signif_digits_correct.
Qed.

Record FI := { FI_val :> F.type; FI_prop : is_mantissa_bounded FI_val }.

Definition F2FI_val (f : F.type) : F.type :=
  match f with
    | Specific_ops.Fnan => Specific_ops.Fnan
    | Specific_ops.Float m e =>
      if (signif_digits m <=? 53)%bigZ then f else Specific_ops.Fnan
  end.

Lemma F2FI_proof (x : F.type) : is_mantissa_bounded (F2FI_val x).
Proof.
case: x => [|m e]; apply/mantissa_boundedP; first by left.
rewrite /F2FI_val.
case E: BigZ.leb; last by left.
exact/signif_digits_correct.
Qed.

Definition F2FI (f : F.type) : FI := Build_FI (F2FI_proof f).

(** See F2FI_correct below *)

End Signif_digits.

Section Coqinterval_infnan.

Let prec := 53%bigZ.

Definition FI0_proof : is_mantissa_bounded F.zero.
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded; simpl; right; exists 0; [now simpl|].
apply FLX_format_generic; [now simpl|]; apply generic_format_0.
Qed.

Definition FI0 := Build_FI FI0_proof.

Lemma mantissa_bounded_bpow n :
  is_mantissa_bounded (Specific_ops.Float 1%bigZ n).
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded; simpl; right; exists (bpow radix2 (BigZ.to_Z n)).
{ unfold F.toX, F.toF, FtoX.
  change (Bir.mantissa_sign 1) with (Specific_sig.Mnumber false 1%bigN).
  simpl.
  unfold FtoR, Bir.EtoZ; simpl.
  case (BigZ.to_Z n); [now simpl| |]; intro p; unfold bpow; simpl.
  { now case (Z.pow_pos 2 p). }
  now unfold Rdiv; rewrite Rmult_1_l. }
apply FLX_format_generic; [now simpl|]; apply generic_format_bpow.
unfold FLX_exp;
  (try change (phi 53) with 53%Z); (try change (Uint63.to_Z _) with 53%Z);
  lia.
Qed.

Definition FI1 := Build_FI (mantissa_bounded_bpow 0%bigZ).

Let finite (x : FI) := F.real x.

Lemma finite0 : finite FI0.
Proof. now unfold finite, FI0, F.real; simpl. Qed.

Lemma finite1 : finite FI1.
Proof. now unfold finite, FI0, F.real; simpl. Qed.

Definition fis := flx64.flx64' (fun m => negb (Z.even m)).

Definition m := 2.  (* anything larger or equal 2 would do the job *)

Lemma m_ge_2 : 2 <= m.
Proof. apply Rle_refl. Qed.

Lemma toR_Float (m e : bigZ) :
  toR (Specific_ops.Float m e) = (IZR (BigZ.to_Z m) * bpow F.radix (BigZ.to_Z e))%Re.
Proof.
rewrite /F.toX /F.toF /=.
have := Bir.mantissa_sign_correct m.
case E_m: (Bir.mantissa_sign m) => [|s m']; last case.
  by rewrite /Bir.MtoZ =>-> /=; rewrite Rmult_0_l.
rewrite /proj_val /FtoX.
rewrite (FtoR_split radix2 s (Bir.MtoP m') (BigZ.to_Z e)).
rewrite /F2R /= /cond_Zopp => H1 H2; congr Rmult.
move: H1; case: (s) => H1.
by rewrite Pos2Z.opp_pos -H1.
by rewrite -H1.
Qed.

Program Definition FI2FS (x : FI) : FS fis :=
  @Build_FS_of (@format fis) (toR (FI_val x)) _.
Next Obligation.
move=> x; apply/eqP.
case: x => [f Hf] => /=.
move/mantissa_boundedP in Hf.
case: Hf => [->|].
exact: generic_format_0.
case => r.
case: f => // m e.
rewrite real_FtoX_toR // => [H1].
rewrite /flx64.format => H; apply generic_format_FLX.
by rewrite H1 /=.
Qed.

Lemma F2FI_correct (f : F.type) : F.real (F2FI f) ->
                                  FI2FS (F2FI f) = toR f :> R.
Proof. by rewrite /FI2FS /F2FI /=; case: f =>//= m e; case (_ <=? _)%bigZ. Qed.

Lemma FI2FS_spec x : (FI2FS x <> 0 :> R) -> finite x.
Proof. by case x => [[|m e] Hf]. Qed.

Lemma FI2FS0 : FI2FS (FI0) = F0 fis :> R.
Proof. by []. Qed.

Lemma FI2FS1 : FI2FS (FI1) = F1 fis :> R.
Proof. by []. Qed.

Lemma toF_fromF_id (x : float radix2) : F.toF (F.fromF x) = x.
Proof.
unfold F.toF, F.fromF.
case x; auto.
intros s m e; case s; auto.
{ unfold Bir.mantissa_sign, Bir.ZtoM; simpl.
  unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
  rewrite Uint63.to_Z_0 BigN.BigN.spec_of_pos; simpl.
  unfold Bir.MtoP; rewrite BigN.BigN.spec_of_pos.
  now rewrite [_ (_ e)]Bir.ZtoE_correct. }
unfold BigIntRadix2.mantissa_sign, BigIntRadix2.ZtoM; simpl.
unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
rewrite Uint63.to_Z_0 BigN.BigN.spec_of_pos; simpl.
unfold BigIntRadix2.MtoP; rewrite BigN.BigN.spec_of_pos.
now rewrite [_ (_ e)]BigIntRadix2.ZtoE_correct.
Qed.

Definition firnd_val (x : R) : F.type :=
  let f := frnd fis x in
  let m := Ztrunc (scaled_mantissa radix2 (FLX_exp 53) f) in
  let e := cexp radix2 (FLX_exp 53) f in
  let f' := match m with
    | Zpos p => Float false p e
    | Z0 => Fzero
    | Zneg p => Float true p e end in
  F.fromF f'.

Lemma firnd_proof x : is_mantissa_bounded (firnd_val x).
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded, firnd_val, F.toX.
rewrite toF_fromF_id; right; exists (frnd fis x).
{ set (f := frnd fis x).
  set (fexp := FLX_exp 53).
  assert (Hfr : Generic_fmt.round radix2 fexp Ztrunc f = f).
  { rewrite round_generic =>//.
    apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N]. }
  set (m := scaled_mantissa _ _ _).
  set (zm := Ztrunc m).
  unfold FtoX; case_eq zm.
  { intro Hzm; rewrite <- Hfr; unfold Generic_fmt.round, F2R.
    now fold m zm; rewrite Hzm Rmult_0_l. }
  { intros p Hp; rewrite <- Hfr at 2; unfold Generic_fmt.round.
    unfold FtoR; case (cexp radix2 fexp f).
    { now fold m zm; rewrite <- Hp; unfold F2R; rewrite Rmult_1_r. }
    { now intro p'; fold m zm; rewrite <- Hp, mult_IZR; unfold F2R. }
    now intro p'; fold m zm; rewrite <- Hp. }
  intros p Hp; rewrite <- Hfr at 2; unfold Generic_fmt.round.
  unfold FtoR; case (cexp radix2 fexp f).
  { now fold m zm; rewrite <- Hp; unfold F2R; rewrite Rmult_1_r. }
  { now intro p'; fold m zm; rewrite <- Hp, mult_IZR; unfold F2R. }
  now intro p'; fold m zm; rewrite <- Hp. }
apply FLX_format_generic; [now simpl|].
apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition firnd (x : R) : FI :=
  {| FI_val := firnd_val x; FI_prop := firnd_proof x |}.

Lemma firnd_spec_aux x : FI2FS (firnd x) = frnd fis x :> R.
Proof.
rewrite /FI2FS /=.
set (f := Generic_fmt.round _ _ _ _).
assert (Hfr : Generic_fmt.round radix2 (FLX_exp 53) Ztrunc f = f).
{ rewrite round_generic =>//.
  apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N]. }
unfold F.toF, firnd, firnd_val; simpl; fold f.
set (m := scaled_mantissa _ _ _).
set (e := cexp _ _ _).
set (zm := Ztrunc m).
rewrite <- Hfr; unfold Generic_fmt.round, F2R; simpl; fold m zm e.
unfold F.toX; rewrite toF_fromF_id; unfold FtoX; case_eq zm.
{ now rewrite Rmult_0_l. }
{ intros p Hp; unfold FtoR; case e.
  { now rewrite Rmult_1_r. }
  { now intros p'; rewrite mult_IZR. }
  now simpl. }
intros p Hp; unfold FtoR; case e.
{ now rewrite Rmult_1_r. }
{ now intro p'; rewrite mult_IZR. }
now simpl.
Qed.

Lemma firnd_spec x : finite (firnd x) -> FI2FS (firnd x) = frnd fis x :> R.
Proof. intros _; apply firnd_spec_aux. Qed.

Lemma firnd_spec_f_aux x : finite (firnd x).
Proof.
now unfold finite, firnd, firnd_val, F.real, F.fromF; simpl; case (Ztrunc _).
Qed.

Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
Proof. intros _; apply firnd_spec_f_aux. Qed.

Lemma fiopp_proof (x : FI) : is_mantissa_bounded (F.neg x).
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded; rewrite F'.neg_correct.
rewrite /x_bounded.
case: x => [[|m e] Hx]; first by left.
right; simpl.
have /mantissa_boundedP [|[r H1 H2]] := Hx.
by rewrite real_FtoX_toR //.
exists (-r); first by rewrite H1.
apply FLX_format_generic; [now simpl|].
now apply generic_format_opp, generic_format_FLX.
Qed.

Definition fiopp (x : FI) : FI :=
  {| FI_val := F.neg x; FI_prop := fiopp_proof x |}.

Lemma fiopp_spec_f1 x : finite (fiopp x) -> finite x.
Proof.
unfold finite, fiopp; simpl; do 2 rewrite FtoX_real.
now rewrite F'.neg_correct; case (F.toX _).
Qed.

Lemma fiopp_spec_f x : finite x -> finite (fiopp x).
Proof.
unfold finite, fiopp; simpl; do 2 rewrite FtoX_real.
now rewrite F'.neg_correct; case (F.toX _).
Qed.

Definition X2F (x : ExtendedR) : FS fis :=
  match x with
  | Xnan => F0 fis
  | Xreal r => frnd fis r
  end.

Ltac caseFI x Hx H1 H2 :=
  case: x => [[//|? ?] Hx] /=; last
  do [move/mantissa_boundedP in Hx;
      case: Hx => [|[? H1 H2]]; first by rewrite real_FtoX_toR].

Lemma FI2FS_X2F_FtoX x : FI2FS x = X2F (F.toX x) :> R.
Proof.
rewrite /FI2FS /X2F /=.
caseFI x Hx H1 H2.
rewrite real_FtoX_toR // -real_FtoX_toR //.
apply sym_eq, round_generic; [apply valid_rnd_N|apply generic_format_FLX].
by rewrite H1.
Qed.

Lemma fiopp_spec_aux x : FI2FS (fiopp x) = fopp (FI2FS x) :> R.
Proof.
rewrite (FI2FS_X2F_FtoX _).
unfold fiopp; rewrite F'.neg_correct /= /X2F.
caseFI x Hx H1 H2; first by rewrite Ropp_0.
rewrite real_FtoX_toR //.
rewrite /= Round_NE.round_NE_opp H1 /=.
rewrite round_generic //.
by apply: generic_format_FLX.
Qed.

Lemma fiopp_spec x : finite (fiopp x) -> FI2FS (fiopp x) = fopp (FI2FS x) :> R.
Proof. intros _; apply fiopp_spec_aux. Qed.

Lemma fiplus_proof rm (x y : FI) : is_mantissa_bounded (F.add_slow rm 53%bigZ x y).
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded.
rewrite F.add_slow_correct; set (z := Xadd _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set r'' := round _ _ _ _; exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_of_mode].
Qed.

Definition fiplus (x y : FI) : FI := Build_FI (fiplus_proof rnd_NE x y).

Lemma fiplus_spec_fl x y : finite (fiplus x y) -> finite x.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.add_slow_correct /Xround /Xbind; case: (F.toX x).
Qed.

Lemma fiplus_spec_fr x y : finite (fiplus x y) -> finite y.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.add_slow_correct /Xround /Xbind; case (F.toX y)=>//; rewrite Xadd_comm.
Qed.

Lemma fiplus_spec_f_aux x y : finite x -> finite y -> finite (fiplus x y).
Proof.
unfold finite, fiplus; simpl; do 3 rewrite FtoX_real.
now rewrite F.add_slow_correct; case (F.toX y); [|intro r]; case (F.toX x).
Qed.

Lemma fiplus_spec_f x y : finite x -> finite y ->
  Rabs (fplus (FI2FS x) (FI2FS y)) < m -> finite (fiplus x y).
Proof. now intros Fx Fy _; apply fiplus_spec_f_aux. Qed.

Lemma fiplus_spec x y : finite (fiplus x y) ->
  FI2FS (fiplus x y) = fplus (FI2FS x) (FI2FS y) :> R.
Proof.
unfold finite; rewrite (FI2FS_X2F_FtoX _) FtoX_real.
unfold fiplus; simpl; rewrite F.add_slow_correct.
set (z := Xadd _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic //.
{ apply f_equal; revert Hr; unfold z.
  case_eq (F.toX x); [now simpl|]; intros rx Hrx.
  case_eq (F.toX y); [now simpl|]; intros ry Hry.
  by case =><-. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fiminus (x y : FI) : FI := fiplus x (fiopp y).

Lemma fiminus_spec_fl x y : finite (fiminus x y) -> finite x.
Proof. exact: fiplus_spec_fl. Qed.

Lemma fiminus_spec_fr x y : finite (fiminus x y) -> finite y.
Proof. by move/fiplus_spec_fr/fiopp_spec_f1. Qed.

Lemma fiminus_spec x y : finite (fiminus x y) ->
  FI2FS (fiminus x y) = fminus (FI2FS x) (FI2FS y) :> R.
Proof.
move=> fxmy; rewrite fiplus_spec//; congr (fplus _ _).
by apply/val_inj/fiopp_spec; apply: fiplus_spec_fr fxmy.
Qed.

Lemma fiminus_spec_f_aux x y : finite x -> finite y -> finite (fiminus x y).
Proof.
move => Hx Hy. apply fiopp_spec_f in Hy. move :Hx Hy.
unfold finite, fiminus; simpl; do 3 rewrite FtoX_real.
now rewrite F.add_slow_correct; case (F.toX (F.neg y)); [|intro r]; case (F.toX x).
Qed.

Lemma fiminus_spec_f x y : finite x -> finite y ->
  Rabs (fminus (FI2FS x) (FI2FS y)) < m -> finite (fiminus x y).
Proof. now intros Fx Fy _; apply fiminus_spec_f_aux. Qed.

Lemma fimult_proof rm (x y : F.type) : is_mantissa_bounded (F.mul rm 53%bigZ x y).
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded.
rewrite F.mul_correct; set (z := Xmul _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set r'' := round _ _ _ _; exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_of_mode].
Qed.

Definition fimult (x y : FI) : FI := Build_FI (fimult_proof rnd_NE x y).

Lemma fimult_spec_fl x y : finite (fimult x y) -> finite x.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.mul_correct; case (F.toX x); [|intro r].
Qed.

Lemma fimult_spec_fr x y : finite (fimult x y) -> finite y.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.mul_correct; case (F.toX y); [|intro r]; case (F.toX).
Qed.

Lemma fimult_spec_f_aux x y : finite x -> finite y -> finite (fimult x y).
Proof.
unfold finite; simpl; do 3 rewrite FtoX_real.
now rewrite F.mul_correct; case (F.toX y); [|intro r]; case (F.toX x).
Qed.

Lemma fimult_spec_f x y : finite x -> finite y ->
  Rabs (fmult (FI2FS x) (FI2FS y)) < m -> finite (fimult x y).
Proof. now intros Fx Fy _; apply fimult_spec_f_aux. Qed.

Lemma fimult_spec x y : finite (fimult x y) ->
  FI2FS (fimult x y) = fmult (FI2FS x) (FI2FS y) :> R.
Proof.
move=> H.
suff: FI2FS (fimult x y) = fmult (FI2FS x) (FI2FS y) :> R; [by []|].
move: H.
unfold finite; rewrite (FI2FS_X2F_FtoX _) FtoX_real.
unfold fimult; simpl; rewrite F.mul_correct.
set (z := Xmul _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic.
{ apply f_equal; revert Hr; unfold z.
  case_eq (F.toX x); [now simpl|]; intros rx Hrx.
  case_eq (F.toX y); [now simpl|]; intros ry Hry.
  by case => <-. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Lemma fidiv_proof rm (x y : F.type) : is_mantissa_bounded (F.div rm 53%bigZ x y).
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded.
rewrite F.div_correct; set (z := Xdiv _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_of_mode].
Qed.

Definition fidiv (x y : FI) : FI := Build_FI (fidiv_proof rnd_NE x y).

Lemma fidiv_spec_fl_aux x y : finite (fidiv x y) -> finite x.
Proof.
unfold finite, fidiv; simpl; do 2 rewrite FtoX_real.
now rewrite F.div_correct; case (F.toX x); [|intro r].
Qed.

Lemma fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x.
Proof. now intros Fxy _; revert Fxy; apply fidiv_spec_fl_aux. Qed.

Lemma fidiv_spec_f_aux x y : finite x -> (FI2FS y <> 0 :> R) -> finite (fidiv x y).
Proof.
unfold finite, fidiv; simpl; do 2 rewrite FtoX_real.
rewrite F.div_correct.
case (F.toX x); [now simpl|]; intros r Hr.
case: (F.toX y) => [|ry] Hry //.
rewrite /Xdiv' /=.
by case: is_zero_spec.
Qed.

Lemma fidiv_spec_f x y : finite x -> (FI2FS y <> 0 :> R) ->
  Rabs (fdiv (FI2FS x) (FI2FS y)) < m -> finite (fidiv x y).
Proof. intros Fx Nzy _; revert Fx Nzy; apply fidiv_spec_f_aux. Qed.

Lemma fidiv_spec_aux x y : finite (fidiv x y) ->
  FI2FS (fidiv x y) = fdiv (FI2FS x) (FI2FS y) :> R.
Proof.
unfold finite; rewrite (FI2FS_X2F_FtoX _) FtoX_real.
unfold fidiv; simpl; rewrite F.div_correct.
set (z := Xdiv _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic.
{ apply f_equal; revert Hr; unfold z.
  case_eq (F.toX x); [now simpl|]; intros rx Hrx.
  case_eq (F.toX y); [now simpl|]; intros ry Hry.
  by rewrite /Xdiv /Xdiv'; case: ifP =>// _ [->]. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Lemma fidiv_spec x y : finite (fidiv x y) -> finite y ->
  FI2FS (fidiv x y) = fdiv (FI2FS x) (FI2FS y) :> R.
Proof. now intros Fxy Fy; apply fidiv_spec_aux. Qed.

Lemma fisqrt_proof (x : F.type) : is_mantissa_bounded (F.sqrt rnd_NE 53%bigZ x).
Proof.
apply/mantissa_boundedP.
unfold mantissa_bounded, x_bounded.
rewrite F.sqrt_correct; set (z := Xsqrt_nan _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fisqrt (x : FI) : FI :=
  {| FI_val := F.sqrt rnd_NE 53%bigZ x; FI_prop := fisqrt_proof x |}.

Lemma fisqrt_spec_f1 x : finite (fisqrt x) -> finite x.
Proof.
unfold finite, fisqrt; simpl; do 2 rewrite FtoX_real.
now rewrite F.sqrt_correct; case (F.toX x); [|intro r].
Qed.

Lemma fisqrt_spec_f x : finite x -> FI2FS x >= 0 -> finite (fisqrt x).
Proof.
unfold finite, fisqrt; simpl.
rewrite !FtoX_real F.sqrt_correct /X_real.
case: F.toX =>[//|r] /=.
rewrite /Xsqrt_nan'; case: (is_negative_spec r) =>//.
by move/Rlt_not_ge.
Qed.

Lemma fisqrt_spec x : finite (fisqrt x) -> FI2FS (fisqrt x) = fsqrt (FI2FS x) :> R.
Proof.
move=> H.
suff: FI2FS (fisqrt x) = fsqrt (FI2FS x) :> R; [by []|].
move: H.
unfold finite; rewrite (FI2FS_X2F_FtoX _) FtoX_real.
unfold fisqrt; simpl; rewrite F.sqrt_correct.
set (z := Xsqrt_nan _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic.
{ apply f_equal; revert Hr; unfold z.
  case_eq (F.toX x); [now simpl|]; intros rx Hrx.
  by rewrite /= /Xsqrt_nan'; case: is_negative_spec =>// _ [->]. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition ficompare (x y : FI) : float_comparison :=
  match F'.cmp x y with
    | Xlt => FLt
    | Xgt => FGt
    | Xeq => FEq
    | Xund =>
      if ~~ F.real x && ~~ F.real y then FEq else FNotComparable
  end.

Lemma ficompare_spec x y : finite x -> finite y ->
  ficompare x y = flatten_cmp_opt (Some (Rcompare (FI2FS x) (FI2FS y))).
Proof.
unfold ficompare; rewrite F'.cmp_correct.
unfold finite; rewrite !FtoX_real !FI2FS_X2F_FtoX.
caseFI x Hx Hx1 Hx2; caseFI y Hy Hy1 Hy2.
rewrite /Xcmp.
rewrite real_FtoX_toR // => H.
rewrite real_FtoX_toR // => H'.
rewrite Hx1 Hy1 /X2F.
case: Rcompare_spec =>//= H0.
- do 2![rewrite round_generic; last exact: generic_format_FLX].
  by rewrite Rcompare_Lt.
- do 2![rewrite round_generic; last exact: generic_format_FLX].
  by rewrite Rcompare_Eq.
- do 2![rewrite round_generic; last exact: generic_format_FLX].
  by rewrite Rcompare_Gt.
Qed.

Lemma ficompare_spec_eq x y : ficompare x y = FEq -> FI2FS x = FI2FS y :> R.
Proof.
move=> H; suff: FI2FS x = FI2FS y :> R; [by []|move: H].
unfold ficompare; rewrite F'.cmp_correct !F.real_correct.
unfold Xcmp.
case Ex: (F.toX x) =>[|rx]; case Ey: (F.toX y) =>[|ry] //=;
  first by rewrite Ex Ey.
by case: Rcompare_spec =>//; rewrite Ex Ey =>->.
Qed.

Lemma ficompare_spec_eq_f x y : ficompare x y = FEq ->
  (finite x <-> finite y).
Proof.
unfold ficompare, finite; rewrite F'.cmp_correct !F.real_correct.
by case Ex: (F.toX x) =>[|rx]; case Ey: (F.toX y) =>[|ry].
Qed.

Definition coqinterval_infnan : Float_infnan_spec :=
  @Build_Float_infnan_spec
    FI
    FI0
    FI1
    F.real
    finite0
    finite1
    fis
    m
    m_ge_2
    FI2FS
    FI2FS_spec
    FI2FS0
    FI2FS1
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
    fiminus
    fiminus_spec
    fiminus_spec_fl
    fiminus_spec_fr
    fiminus_spec_f
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

Definition FI2FIS (x : FI) : FIS coqinterval_infnan := x.

Definition fieps := Build_FI (mantissa_bounded_bpow (-53)%bigZ).

Lemma fieps_spec :
  (eps (float_infnan_spec.fis coqinterval_infnan) <= FI2FS fieps)%Re.
Proof. rewrite /=; compute; lra. Qed.

Definition fieta := Build_FI (mantissa_bounded_bpow (-1075)%bigZ).

Lemma fieta_spec : (eta fis <= FI2FS fieta)%Re.
Proof. rewrite /=; compute; lra. Qed.

Definition fiplus_up (x y : FI) : FI := Build_FI (fiplus_proof rnd_UP x y).

Lemma fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.add_slow_correct /Xround /Xbind; case: (F.toX x).
Qed.

Lemma fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.add_slow_correct /Xround /Xbind; case (F.toX y)=>//; rewrite Xadd_comm.
Qed.

Lemma fiplus_up_spec x y : finite (fiplus_up x y) ->
  (FI2FS x + FI2FS y <= FI2FS (fiplus_up x y))%Re.
Proof.
move=> Fxy.
have Fx := fiplus_up_spec_fl Fxy; have Fy := fiplus_up_spec_fr Fxy.
move: Fxy Fx Fy; unfold finite; rewrite !(FI2FS_X2F_FtoX _) !FtoX_real.
unfold fiplus_up; simpl; rewrite F.add_slow_correct.
caseFI x Hx Hx1 Hx2.
caseFI y Hy Hy1 Hy2.
set (z := Xadd _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite Hx1 Hy1 /=.
rewrite !round_generic.
2: exact/generic_format_round/FLX_exp_valid.
2: exact: generic_format_FLX.
2: exact: generic_format_FLX.
apply: (Rle_trans _ r).
by right; apply Xreal_inj; rewrite -Hr /z Hx1 Hy1.
now apply round_UP_pt, FLX_exp_valid.
Qed.

Definition fimult_up (x y : FI) : FI := Build_FI (fimult_proof rnd_UP x y).

Lemma fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.mul_correct /Xround /Xbind; case: (F.toX x).
Qed.

Lemma fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y.
Proof.
unfold finite; simpl; do 2 rewrite FtoX_real.
now rewrite F.mul_correct /Xround /Xbind; case (F.toX y)=>//; rewrite Xmul_comm.
Qed.

Lemma fimult_up_spec x y : finite (fimult_up x y) ->
  (FI2FS x * FI2FS y <= FI2FS (fimult_up x y))%Re.
Proof.
move=> Fxy.
have Fx := fimult_up_spec_fl Fxy; have Fy := fimult_up_spec_fr Fxy.
move: Fxy Fx Fy; unfold finite; rewrite !(FI2FS_X2F_FtoX _) !FtoX_real.
unfold fimult_up; simpl; rewrite F.mul_correct.
caseFI x Hx Hx1 Hx2.
caseFI y Hy Hy1 Hy2.
set (z := Xmul _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite Hx1 Hy1 /=.
rewrite !round_generic.
2: exact/generic_format_round/FLX_exp_valid.
2: exact: generic_format_FLX.
2: exact: generic_format_FLX.
apply: (Rle_trans _ r).
by right; apply Xreal_inj; rewrite -Hr /z Hx1 Hy1.
now apply round_UP_pt, FLX_exp_valid.
Qed.

Definition fidiv_up (x y : FI) : FI := Build_FI (fidiv_proof rnd_UP x y).

Lemma fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x.
Proof.
move=> Fxy _; move: Fxy; unfold finite, fidiv; simpl; do 2 rewrite FtoX_real.
now rewrite F.div_correct; case (F.toX x); [|intro r].
Qed.

Lemma fidiv_up_spec x y : finite (fidiv_up x y) -> finite (y) ->
  (FI2FS x / FI2FS y <= FI2FS (fidiv_up x y))%Re.
Proof.
move=> Fxy Fy.
have Fx := fidiv_up_spec_fl Fxy Fy.
move: Fxy Fx Fy.
unfold finite; rewrite !(FI2FS_X2F_FtoX _) !FtoX_real.
unfold fidiv_up; simpl; rewrite F.div_correct.
caseFI x Hx Hx1 Hx2.
caseFI y Hy Hy1 Hy2.
set (z := Xdiv _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite Hx1 Hy1 /=.
rewrite !round_generic.
2: exact/generic_format_round/FLX_exp_valid.
2: exact: generic_format_FLX.
2: exact: generic_format_FLX.
apply: (Rle_trans _ r).
{ right; apply Xreal_inj; rewrite -Hr /z Hx1 Hy1.
  rewrite /z Hx1 Hy1 in Hr.
  rewrite /Xdiv /Xdiv' in Hr *.
  by case: is_zero_spec Hr. }
now apply round_UP_pt, FLX_exp_valid.
Qed.

Definition coqinterval_round_up_infnan : Float_round_up_infnan_spec :=
  Build_Float_round_up_infnan_spec
    fieps_spec
    fieta_spec
    fiplus_up_spec
    fiplus_up_spec_fl
    fiplus_up_spec_fr
    fimult_up_spec
    fimult_up_spec_fl
    fimult_up_spec_fr
    fidiv_up_spec
    fidiv_up_spec_fl.

End Coqinterval_infnan.
