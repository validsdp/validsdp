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

Module Bir := BigIntRadix2.

Module F := SpecificFloat Bir.

Require Import Psatz.

Open Scope R_scope.

Section Coqinterval_infnan.

Let prec := 53%Z.

Definition x_bounded (x : ExtendedR) : Set :=
  ( x = Xnan ) + { r | x = Xreal r & FLX_format radix2 53 r }.

Definition mantissa_bounded (x : F.type) := x_bounded (F.toX x).

Record FI := { FI_val :> F.type; FI_prop : mantissa_bounded FI_val }.

Definition FI0_proof : mantissa_bounded F.zero.
Proof.
unfold mantissa_bounded, x_bounded; simpl; right; exists 0; [now simpl|].
apply FLX_format_generic; [now simpl|]; apply generic_format_0.
Qed.

Definition FI0 := Build_FI _ FI0_proof.

Definition FI1_proof :
  mantissa_bounded (Interval_specific_ops.Float 1%bigZ 0%bigZ).
Proof.
unfold mantissa_bounded, x_bounded; simpl; right; exists 1; [now simpl|].
apply FLX_format_generic; [now simpl|].
unfold generic_format, F2R, scaled_mantissa, canonic_exp, FLX_exp; simpl.
replace (ln_beta _ _ : Z) with 1%Z; simpl.
{ change 4503599627370496 with (Z2R 4503599627370496).
  rewrite Rmult_1_l, Ztrunc_Z2R, Rinv_r; [reflexivity|].
  now change 0 with (Z2R 0); apply Z2R_neq. }
apply eq_sym, ln_beta_unique_pos; split; [now right|].
rewrite <- (Rplus_0_r 1); apply Rplus_le_lt_compat; [now right|].
apply Rlt_0_1.
Qed.

Definition FI1 := Build_FI _ FI1_proof.

Definition finite (x : FI) := F.real x = true.

Lemma finite0 : finite FI0.
Proof. now unfold finite, FI0, F.real; simpl. Qed.

Lemma finite1 : finite FI1.
Proof. now unfold finite, FI0, F.real; simpl. Qed.

Definition fis := flx64.flx64 (fun m => negb (Zeven m)).

Definition m := 2.  (* anything larger or equal 2 would do the job *)

Lemma m_ge_2 : 2 <= m.
Proof. apply Rle_refl. Qed.

Definition FI2F (x : FI) : F fis :=
  match FI_prop x with
    | inl _ => F0 fis
    | inr (@exist2 _ _ _ r _ Hr) =>
      {| F_val := r; F_prop := generic_format_FLX radix2 53 r Hr |}
  end.

Lemma FI2F_spec x : (FI2F x <> 0 :> R) -> finite x.
Proof.
unfold FI2F, finite.
case (FI_prop x).
{ now intros _; simpl; intro H; casetype False; apply H. }
intro s; destruct s as (r, Hr, Hr'); simpl; revert Hr.
now unfold F.real, F.toF, FtoX; case (FI_val x).
Qed.

Lemma FI2F0 : FI2F (FI0) = F0 fis :> R.
Proof.
unfold FI2F.
case (FI_prop FI0); [now simpl|].
intro s; destruct s as (r, Hr, Hr'); simpl; revert Hr.
now unfold F.toF, FtoX; simpl; intro H; injection H.
Qed.

Lemma FI2F1 : FI2F (FI1) = F1 fis :> R.
Proof.
unfold FI2F.
case (FI_prop FI1); [now simpl|].
intro s; destruct s as (r, Hr, Hr'); simpl; revert Hr.
now unfold F.toF, FtoX; simpl; intro H; injection H.
Qed.

Lemma toF_fromF_id (x : float radix2) : F.toF (F.fromF x) = x.
Proof.
unfold F.toF, F.fromF.
case x; auto.
intros s m e; case s; auto.
{ unfold Bir.mantissa_sign, Bir.ZtoM; simpl.
  unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
  rewrite Cyclic31.spec_0, BigN.BigN.spec_of_pos; simpl.
  unfold Bir.MtoP; rewrite BigN.BigN.spec_of_pos.
  now rewrite Bir.ZtoE_correct. }
unfold BigIntRadix2.mantissa_sign, BigIntRadix2.ZtoM; simpl.
unfold BigZ.BigZ.eqb; rewrite BigZ.BigZ.spec_compare; simpl.
rewrite Cyclic31.spec_0, BigN.BigN.spec_of_pos; simpl.
unfold BigIntRadix2.MtoP; rewrite BigN.BigN.spec_of_pos.
now rewrite BigIntRadix2.ZtoE_correct.
Qed.

Definition firnd_val (x : R) : F.type :=
  let f := frnd fis x in
  let m := Ztrunc (scaled_mantissa radix2 (FLX_exp 53) f) in
  let e := canonic_exp radix2 (FLX_exp 53) f in
  let f' := match m with
    | Zpos p => Float false p e
    | Z0 => Fzero
    | Zneg p => Float true p e end in
  F.fromF f'.

Lemma firnd_proof x : mantissa_bounded (firnd_val x).
Proof.
unfold mantissa_bounded, x_bounded, firnd_val, F.toX.
rewrite toF_fromF_id; right; exists (frnd fis x).
{ set (f := frnd fis x).
  set (fexp := FLX_exp 53).
  assert (Hfr : Fcore_generic_fmt.round radix2 fexp Ztrunc f = f).
  { rewrite round_generic; [now simpl|apply valid_rnd_ZR|].
    apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N]. }
  set (m := scaled_mantissa _ _ _).
  set (zm := Ztrunc m).
  unfold FtoX; case_eq zm.
  { intro Hzm; rewrite <- Hfr; unfold Fcore_generic_fmt.round, F2R.
    now fold m zm; rewrite Hzm, Rmult_0_l. }
  { intros p Hp; rewrite <- Hfr at 2; unfold Fcore_generic_fmt.round.
    unfold FtoR; case (canonic_exp radix2 fexp f).
    { now fold m zm; rewrite <- Hp; unfold F2R; rewrite Rmult_1_r. }
    { now intro p'; fold m zm; rewrite <- Hp, Z2R_mult; unfold F2R. }
    now intro p'; fold m zm; rewrite <- Hp. }
  intros p Hp; rewrite <- Hfr at 2; unfold Fcore_generic_fmt.round.
  unfold FtoR; case (canonic_exp radix2 fexp f).
  { now fold m zm; rewrite <- Hp; unfold F2R; rewrite Rmult_1_r. }
  { now intro p'; fold m zm; rewrite <- Hp, Z2R_mult; unfold F2R. }
  now intro p'; fold m zm; rewrite <- Hp. }
apply FLX_format_generic; [now simpl|].
apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition firnd (x : R) : FI :=
  {| FI_val := firnd_val x; FI_prop := firnd_proof x |}.

Lemma firnd_spec_aux x : FI2F (firnd x) = frnd fis x :> R.
Proof.
unfold FI2F.
case (FI_prop (firnd x)).
{ unfold firnd, F.toX, F.toF, firnd_val, F.fromF; simpl.
  now case (Ztrunc _); [|intro p|intro p];
  case (Bir.mantissa_sign _). }
intro s; destruct s as (r, Hr, Hr'); simpl.
set (f := Fcore_generic_fmt.round _ _ _ _).
assert (Hfr : Fcore_generic_fmt.round radix2 (FLX_exp 53) Ztrunc f = f).
{ rewrite round_generic; [now simpl|apply valid_rnd_ZR|].
  apply generic_format_round; [now apply FLX_exp_valid|apply valid_rnd_N]. }
cut (Xreal r = Xreal f); [now intro H; injection H|].
rewrite <- Hr.
unfold F.toF, firnd, firnd_val; simpl; fold f.
set (m := scaled_mantissa _ _ _).
set (e := canonic_exp _ _ _).
set (zm := Ztrunc m).
rewrite <- Hfr; unfold Fcore_generic_fmt.round, F2R; simpl; fold m zm e.
unfold F.toX; rewrite toF_fromF_id; unfold FtoX; case_eq zm.
{ now rewrite Rmult_0_l. }
{ intros p Hp; unfold FtoR; case e.
  { now rewrite Rmult_1_r. }
  { now intros p'; rewrite Z2R_mult. }
  now simpl. }
intros p Hp; unfold FtoR; case e.
{ now rewrite Rmult_1_r. }
{ now intro p'; rewrite Z2R_mult. }
now simpl.
Qed.

Lemma firnd_spec x : finite (firnd x) -> FI2F (firnd x) = frnd fis x :> R.
Proof. intros _; apply firnd_spec_aux. Qed.

Lemma firnd_spec_f_aux x : finite (firnd x).
Proof.
now unfold finite, firnd, firnd_val, F.real, F.fromF; simpl; case (Ztrunc _).
Qed.

Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
Proof. intros _; apply firnd_spec_f_aux. Qed.

Lemma fiopp_proof (x : FI) : mantissa_bounded (F.neg x).
Proof.
unfold mantissa_bounded; rewrite F.neg_correct.
assert (H := FI_prop x); revert H; unfold mantissa_bounded, x_bounded.
intro Hx; destruct Hx as [Hx|(r, Hr, Hr')]; [now left; rewrite Hx|right].
exists (- r); [now now rewrite Hr|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_opp, generic_format_FLX.
Qed.

Definition fiopp (x : FI) : FI :=
  {| FI_val := F.neg x; FI_prop := fiopp_proof x |}.

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

Lemma fiopp_spec_f1 x : finite (fiopp x) -> finite x.
Proof.
unfold finite, fiopp; simpl; do 2 rewrite FtoX_real.
now rewrite F.neg_correct; case (F.toX _).
Qed.

Lemma fiopp_spec_f x : finite x -> finite (fiopp x).
Proof.
unfold finite, fiopp; simpl; do 2 rewrite FtoX_real.
now rewrite F.neg_correct; case (F.toX _).
Qed.

Definition X2F (x : ExtendedR) : F fis :=
  match x with
  | Xnan => F0 fis
  | Xreal r => frnd fis r
  end.

Lemma FI2F_X2F_FtoX x : FI2F x = X2F (F.toX x) :> R.
Proof.
unfold FI2F; case (FI_prop x).
{ now intro H; rewrite H. }
intro H; destruct H as (r, Hx, Hr); rewrite Hx; simpl.
now apply sym_eq, round_generic; [apply valid_rnd_N|apply generic_format_FLX].
Qed.

Lemma fiopp_spec_aux x : FI2F (fiopp x) = fopp (FI2F x) :> R.
Proof.
rewrite (FI2F_X2F_FtoX _).
unfold fiopp; simpl; rewrite F.neg_correct.
rewrite (FI2F_X2F_FtoX _); set (f := F.toX _).
case f; simpl; [|intro r].
{ now rewrite Ropp_0. }
apply Fcore_rnd_ne.round_NE_opp.
Qed.

Lemma fiopp_spec x : finite (fiopp x) -> FI2F (fiopp x) = fopp (FI2F x) :> R.
Proof. intros _; apply fiopp_spec_aux. Qed.

Lemma ftoX_ftoF (x : F.type) : F.toX x = FtoX (F.toF x).
Proof. now simpl. Qed.
  
Lemma fiplus_proof (x y : FI) : mantissa_bounded (F.add rnd_NE 53%bigZ x y).
Proof.
unfold mantissa_bounded, x_bounded.
rewrite ftoX_ftoF, F.add_correct, Fadd_correct; set (z := Xadd _ _).
unfold xround; case z; [now left|intro r'; right].
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fiplus (x y : FI) : FI :=
  {| FI_val := F.add rnd_NE 53%bigZ x y; FI_prop := fiplus_proof x y |}.

Lemma fiplus_spec_fl x y : finite (fiplus x y) -> finite x.
Proof.
unfold finite, fiplus; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
now rewrite F.add_correct, Fadd_correct; case (FtoX (F.toF x)); [|intro r].
Qed.

Lemma fiplus_spec_fr x y : finite (fiplus x y) -> finite y.
Proof.
unfold finite, fiplus; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
rewrite F.add_correct, Fadd_correct.
now case (FtoX (F.toF y)); [|intro r]; case (FtoX (F.toF x)).
Qed.

Lemma fiplus_spec_f_aux x y : finite x -> finite y -> finite (fiplus x y).
Proof.
unfold finite, fiplus; simpl; do 3 rewrite FtoX_real, ftoX_ftoF.
rewrite F.add_correct, Fadd_correct.
now case (FtoX (F.toF y)); [|intro r]; case (FtoX (F.toF x)).
Qed.

Lemma fiplus_spec_f x y : finite x -> finite y ->
  Rabs (fplus (FI2F x) (FI2F y)) < m -> finite (fiplus x y).
Proof. now intros Fx Fy _; apply fiplus_spec_f_aux. Qed.

Lemma fiplus_spec x y : finite (fiplus x y) ->
  FI2F (fiplus x y) = fplus (FI2F x) (FI2F y) :> R.
Proof.
unfold finite; rewrite (FI2F_X2F_FtoX _), FtoX_real, ftoX_ftoF.
unfold fiplus; simpl; rewrite F.add_correct, Fadd_correct.
set (z := Xadd _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
{ apply f_equal; revert Hr; unfold z.
  case_eq (FtoX (F.toF x)); [now simpl|]; intros rx Hrx.
  case_eq (FtoX (F.toF y)); [now simpl|]; intros ry Hry.
  do 2 rewrite FI2F_X2F_FtoX, ftoX_ftoF; rewrite Hrx, Hry; simpl.
  rewrite round_generic; [|now apply valid_rnd_N|].
  { rewrite round_generic; [|now apply valid_rnd_N|].
    { now intro H; injection H. }
    case (FI_prop y); [now rewrite ftoX_ftoF, Hry|].
    intros (ry', Hry', Hry''); rewrite ftoX_ftoF, Hry in Hry'; injection Hry'.
    now intro H; rewrite H; apply generic_format_FLX. }
  case (FI_prop x); [now rewrite ftoX_ftoF, Hrx|].
  intros (rx', Hrx', Hrx''); rewrite ftoX_ftoF, Hrx in Hrx'; injection Hrx'.
  now intro H; rewrite H; apply generic_format_FLX. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Lemma fimult_proof (x y : FI) : mantissa_bounded (F.mul rnd_NE 53%bigZ x y).
Proof.
unfold mantissa_bounded, x_bounded.
rewrite ftoX_ftoF, F.mul_correct, Fmul_correct; set (z := Xmul _ _).
unfold xround; case z; [now left|intro r'; right].
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fimult (x y : FI) : FI :=
  {| FI_val := F.mul rnd_NE 53%bigZ x y; FI_prop := fimult_proof x y |}.

Lemma fimult_spec_fl x y : finite (fimult x y) -> finite x.
Proof.
unfold finite, fiplus; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
now rewrite F.mul_correct, Fmul_correct; case (FtoX (F.toF x)); [|intro r].
Qed.

Lemma fimult_spec_fr x y : finite (fimult x y) -> finite y.
Proof.
unfold finite, fiplus; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
rewrite F.mul_correct, Fmul_correct.
now case (FtoX (F.toF y)); [|intro r]; case (FtoX (F.toF x)).
Qed.

Lemma fimult_spec_f_aux x y : finite x -> finite y -> finite (fimult x y).
Proof.
unfold finite, fiplus; simpl; do 3 rewrite FtoX_real, ftoX_ftoF.
rewrite F.mul_correct, Fmul_correct.
now case (FtoX (F.toF y)); [|intro r]; case (FtoX (F.toF x)).
Qed.

Lemma fimult_spec_f x y : finite x -> finite y ->
  Rabs (fmult (FI2F x) (FI2F y)) < m -> finite (fimult x y).
Proof. now intros Fx Fy _; apply fimult_spec_f_aux. Qed.

Lemma fimult_spec x y : finite (fimult x y) ->
  FI2F (fimult x y) = fmult (FI2F x) (FI2F y) :> R.
Proof.
unfold finite; rewrite (FI2F_X2F_FtoX _), FtoX_real, ftoX_ftoF.
unfold fimult; simpl; rewrite F.mul_correct, Fmul_correct.
set (z := Xmul _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
{ apply f_equal; revert Hr; unfold z.
  case_eq (FtoX (F.toF x)); [now simpl|]; intros rx Hrx.
  case_eq (FtoX (F.toF y)); [now simpl|]; intros ry Hry.
  do 2 rewrite FI2F_X2F_FtoX, ftoX_ftoF; rewrite Hrx, Hry; simpl.
  rewrite round_generic; [|now apply valid_rnd_N|].
  { rewrite round_generic; [|now apply valid_rnd_N|].
    { now intro H; injection H. }
    case (FI_prop y); [now rewrite ftoX_ftoF, Hry|].
    intros (ry', Hry', Hry''); rewrite ftoX_ftoF, Hry in Hry'; injection Hry'.
    now intro H; rewrite H; apply generic_format_FLX. }
  case (FI_prop x); [now rewrite ftoX_ftoF, Hrx|].
  intros (rx', Hrx', Hrx''); rewrite ftoX_ftoF, Hrx in Hrx'; injection Hrx'.
  now intro H; rewrite H; apply generic_format_FLX. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Lemma fidiv_proof (x y : FI) : mantissa_bounded (F.div rnd_NE 53%bigZ x y).
Proof.
unfold mantissa_bounded, x_bounded.
rewrite ftoX_ftoF, F.div_correct, Fdiv_correct; set (z := Xdiv _ _).
unfold xround; case z; [now left|intro r'; right].
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fidiv (x y : FI) : FI :=
  {| FI_val := F.div rnd_NE 53%bigZ x y; FI_prop := fidiv_proof x y |}.

Lemma fidiv_spec_fl_aux x y : finite (fidiv x y) -> finite x.
Proof.
unfold finite, fidiv; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
now rewrite F.div_correct, Fdiv_correct; case (FtoX (F.toF x)); [|intro r].
Qed.

Lemma fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x.
Proof. now intros Fxy _; revert Fxy; apply fidiv_spec_fl_aux. Qed.

Lemma fidiv_spec_f_aux x y : finite x -> (FI2F y <> 0 :> R) -> finite (fidiv x y).
Proof.
unfold finite, fidiv; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
rewrite F.div_correct, Fdiv_correct.
case (FtoX (F.toF x)); [now simpl|]; intros r Hr.
unfold FI2F; case (FI_prop y).
{ now intros _ H; casetype False; apply H. }
intros (r', Hr', Hr''); simpl; rewrite <- ftoX_ftoF, Hr'.
assert (H := is_zero_spec r'); revert H; unfold Xdiv'; case (is_zero r').
{ now intros H1 H2; casetype False; apply H2; destruct H1. }
now simpl.
Qed.

Lemma fidiv_spec_f x y : finite x -> (FI2F y <> 0 :> R) ->
  Rabs (fdiv (FI2F x) (FI2F y)) < m -> finite (fidiv x y).
Proof. intros Fx Nzy _; revert Fx Nzy; apply fidiv_spec_f_aux. Qed.

Lemma fidiv_spec_aux x y : finite (fidiv x y) ->
  FI2F (fidiv x y) = fdiv (FI2F x) (FI2F y) :> R.
Proof.
unfold finite; rewrite (FI2F_X2F_FtoX _), FtoX_real, ftoX_ftoF.
unfold fidiv; simpl; rewrite F.div_correct, Fdiv_correct.
set (z := Xdiv _ _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
{ apply f_equal; revert Hr; unfold z.
  case_eq (FtoX (F.toF x)); [now simpl|]; intros rx Hrx.
  case_eq (FtoX (F.toF y)); [now simpl|]; intros ry Hry.
  do 2 rewrite FI2F_X2F_FtoX, ftoX_ftoF; rewrite Hrx, Hry; simpl.
  rewrite round_generic; [|now apply valid_rnd_N|].
  { rewrite round_generic; [|now apply valid_rnd_N|]; unfold Xdiv'.
    { case (is_zero ry); [now simpl|].
      now intro H; injection H. }
    case (FI_prop y); [now rewrite ftoX_ftoF, Hry|].
    intros (ry', Hry', Hry''); rewrite ftoX_ftoF, Hry in Hry'; injection Hry'.
    now intro H; rewrite H; apply generic_format_FLX. }
  case (FI_prop x); [now rewrite ftoX_ftoF, Hrx|].
  intros (rx', Hrx', Hrx''); rewrite ftoX_ftoF, Hrx in Hrx'; injection Hrx'.
  now intro H; rewrite H; apply generic_format_FLX. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Lemma fidiv_spec x y : finite (fidiv x y) -> finite y ->
  FI2F (fidiv x y) = fdiv (FI2F x) (FI2F y) :> R.
Proof. now intros Fxy Fy; apply fidiv_spec_aux. Qed.

Lemma fisqrt_proof (x : FI) : mantissa_bounded (F.sqrt rnd_NE 53%bigZ x).
Proof.
unfold mantissa_bounded, x_bounded.
rewrite ftoX_ftoF, F.sqrt_correct, Fsqrt_correct; set (z := Xsqrt _).
unfold xround; case z; [now left|intro r'; right].
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition fisqrt (x : FI) : FI :=
  {| FI_val := F.sqrt rnd_NE 53%bigZ x; FI_prop := fisqrt_proof x |}.

Lemma fisqrt_spec_f1 x : finite (fisqrt x) -> finite x.
Proof.
unfold finite, fisqrt; simpl; do 2 rewrite FtoX_real, ftoX_ftoF.
now rewrite F.sqrt_correct, Fsqrt_correct; case (FtoX (F.toF x)); [|intro r].
Qed.

Lemma fisqrt_spec_f x : finite x -> FI2F x >= 0 -> finite (fisqrt x).
Proof.
unfold finite, fisqrt; simpl; do 2 rewrite FtoX_real; rewrite FI2F_X2F_FtoX.
rewrite ftoX_ftoF, ftoX_ftoF, F.sqrt_correct, Fsqrt_correct.
assert (H := FI_prop x); revert H; unfold mantissa_bounded, x_bounded.
rewrite ftoX_ftoF; case (FtoX (F.toF x)); [now simpl|intros r Hr]; simpl.
destruct Hr as [Hr|Hr]; [now simpl|]; destruct Hr as (r', Hr', Hr'').
injection Hr'; intros Hr''' _; rewrite Hr''', round_generic.
{ assert (H := is_negative_spec r'); revert H; unfold Xsqrt'.
  case (is_negative r'); [|now simpl]; intro H; destruct H; [|now simpl].
  now intro H'; casetype False; revert H'; apply Rlt_not_ge. }
{ now apply valid_rnd_N. }
now apply generic_format_FLX.
Qed.

Lemma fisqrt_spec x : finite (fisqrt x) ->
  FI2F (fisqrt x) = fsqrt (FI2F x) :> R.
Proof.
unfold finite; rewrite (FI2F_X2F_FtoX _), FtoX_real, ftoX_ftoF.
unfold fisqrt; simpl; rewrite F.sqrt_correct, Fsqrt_correct.
set (z := Xsqrt _); case_eq z; [now simpl|]; intros r Hr _; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
{ apply f_equal; revert Hr; unfold z.
  case_eq (FtoX (F.toF x)); [now simpl|]; intros rx Hrx.
  rewrite FI2F_X2F_FtoX, ftoX_ftoF, Hrx; simpl; unfold Xsqrt'.
  rewrite round_generic; [|now apply valid_rnd_N|].
  { case (is_negative rx); [now simpl|].
    now intro H; injection H. }
  case (FI_prop x); [now rewrite ftoX_ftoF, Hrx|].
  intros (rx', Hrx', Hrx''); rewrite ftoX_ftoF, Hrx in Hrx'; injection Hrx'.
  now intro H; rewrite H; apply generic_format_FLX. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_N].
Qed.

Definition ficompare (x y : FI) : option comparison :=
  match F.cmp x y with
    | Xlt => Some Lt
    | Xgt => Some Gt
    | Xeq => Some Eq
    | Xund => None
  end.

Lemma ficompare_spec x y : finite x -> finite y ->
  ficompare x y = Some (Rcompare (FI2F x) (FI2F y)).
Proof.
unfold ficompare; rewrite F.cmp_correct.
unfold finite; rewrite !FtoX_real, !FI2F_X2F_FtoX.
case (FI_prop x); [now intro H; rewrite H|]; intros [xr Hxr Hxrf] _.
case (FI_prop y); [now intro H; rewrite H|]; intros [yr Hyr Hyrf] _.
rewrite Hxr, Hyr; unfold flx64.frnd; simpl.
do 2 (rewrite round_generic;
        [|now apply valid_rnd_N|now apply generic_format_FLX]).
now case (Rcompare _ _).
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
    ficompare_spec.

End Coqinterval_infnan.
