(** * IEEE754 binary64 format satisfies hypothesis in [Float_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLT(-1074, 53) is a
    model of binary64 with gradual underflow but without NaNs nor
    overflows (which could be easily handled afterward). *)

Require Import Reals.

Require Import float_spec.
Require flx64.

Require Import Flocq.Core.Zaux.
Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Prop.Relative.
Require Import Flocq.Prop.Plus_error.

Require Import Psatz.

Open Scope R_scope.

Section Binary64.

Let prec := 53%Z.
Let emax := 1024%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.

Lemma Pprec : (0 < prec)%Z.
Proof. unfold prec; omega. Qed.

Instance valid_exp : Valid_exp fexp.
Proof. now apply FLT_exp_valid. Qed.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition format x := generic_format radix2 fexp x.

Let F := FS_of format.

Lemma format0 : format 0.
Proof.
unfold format, generic_format, scaled_mantissa, F2R; simpl.
rewrite Rmult_0_l.
change 0 with (IZR 0); rewrite Ztrunc_IZR.
now rewrite Rmult_0_l.
Qed.

Lemma format1 : format 1.
Proof.
unfold format, generic_format, scaled_mantissa, cexp, F2R; simpl.
rewrite Rmult_1_l, (mag_unique radix2 1 1).
{ unfold fexp, FLT_exp.
  rewrite Zmax_left; [|unfold emin, emax, prec; omega].
  rewrite <- IZR_Zpower; [|unfold prec; omega].
  rewrite Ztrunc_IZR, IZR_Zpower; [|unfold prec; omega].
  rewrite <- bpow_plus.
  now replace (_ + _)%Z with Z0 by ring. }
rewrite Rabs_R1; simpl; split; [now right|].
rewrite IZR_Zpower_pos; simpl; lra.
Qed.

Lemma format_opp x : format x -> format (- x).
Proof. apply generic_format_opp. Qed.

Definition eps := bpow radix2 (-53).

Lemma eps_pos : 0 <= eps.
Proof. apply bpow_ge_0. Qed.

Lemma eps_lt_1 : eps < 1.
Proof.
unfold eps, bpow.
apply (Rmult_lt_reg_r (IZR (Z.pow_pos radix2 53)));
  [now fold (bpow radix2 53); apply bpow_gt_0|].
rewrite Rinv_l; [rewrite Rmult_1_l|now apply Rgt_not_eq, Rlt_gt;
                                    fold (bpow radix2 53); apply bpow_gt_0].
change 1 with (IZR 1); apply IZR_lt.
unfold Z.pow_pos; simpl.
omega.
Qed.

Let b_eps := bounded eps.
Let b_epsd1peps := bounded (eps / (1 + eps)).

Definition eta := bpow radix2 (-1075).

Lemma eta_pos : 0 < eta.
Proof. apply bpow_gt_0. Qed.

Let b_eta := bounded eta.

(** The tie-break rule doesn't really matter. *)
Variable choice : Z -> bool.

(** All we need is rounding to nearest. *)
Definition frnd (x : R) : F :=
  Build_FS_of (generic_format_round radix2 fexp (Znearest choice) x).

Lemma frnd_F (x : F) : round radix2 fexp (Znearest choice) x = x :> R.
Proof. apply round_generic; [apply valid_rnd_N|apply FS_prop]. Qed.

Lemma frnd_spec (x : R) :
  exists (d : b_epsd1peps) (e : b_eta),
    round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R
    /\ d * e = 0.
Proof.
assert (Pb := epsd1peps_pos eps_pos).
destruct (Rle_or_lt (bpow radix2 (emin + prec - 1)) (Rabs x)) as [MX|Mx].
{ destruct (flx64.frnd_spec_aux choice x) as (d, Hd).
  exists (cast_bounded (eq_refl _) d), (bounded_0 (Rlt_le _ _ eta_pos)); simpl.
  rewrite Rplus_0_r, Rmult_0_r; split; [|reflexivity].
  now rewrite <- Hd; apply round_FLT_FLX. }
assert (H : Rabs (frnd x - x) <= eta).
{ apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)).
  unfold fexp; rewrite ulp_FLT_small; [|now simpl|].
  { unfold eta; change (-1075)%Z with (-1 + -1074)%Z.
    now rewrite bpow_plus; right. }
  apply (Rlt_le_trans _ _ _ Mx), bpow_le; lia. }
exists (bounded_0 (epsd1peps_pos eps_pos)), (Build_bounded H); simpl.
now rewrite Rplus_0_r, Rmult_1_l, Rmult_0_l; split; [ring|].
Qed.

Lemma round_N_small beta fexp' choice' x ex :
  bpow beta (ex - 1) <= Rabs x < bpow beta ex ->
  (ex < fexp' ex)%Z -> round beta fexp' (Znearest choice') x = 0.
Proof.
intros Hx Hex.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{ now revert Hex; apply round_N_small_pos; revert Hx; rewrite Rabs_pos_eq. }
rewrite <-(Ropp_involutive x), round_N_opp, <-Ropp_0; f_equal.
now revert Hex; apply round_N_small_pos; revert Hx; rewrite Rabs_left.
Qed.

Lemma fplus_spec (x y : F) :
  exists d : b_epsd1peps, frnd (x + y) = (1 + d) * (x + y) :> R.
Proof.
assert (Pb := epsd1peps_pos eps_pos).
destruct (Rle_or_lt (bpow radix2 (emin + prec - 1)) (Rabs (x + y))) as [M|M].
{ destruct (flx64.frnd_spec_aux choice (x + y)) as (d, Hd).
  exists (cast_bounded (eq_refl _) d); simpl.
  now rewrite <- Hd; apply round_FLT_FLX. }
exists (bounded_0 (epsd1peps_pos eps_pos)); simpl; rewrite Rplus_0_r, Rmult_1_l.
apply round_generic; [apply valid_rnd_N|].
apply FLT_format_plus_small; [now simpl|apply FS_prop|apply FS_prop|].
apply Rlt_le, (Rlt_le_trans _ _ _ M), bpow_le; lia.
Qed.

Lemma fplus_spec_l (x y : F) : Rabs (frnd (x + y) - (x + y)) <= Rabs x.
Proof.
apply (Rle_trans _ (Rabs (y - (x + y)))).
{ now apply round_N_pt; [apply FLT_exp_valid|apply FS_prop]. }
rewrite Rabs_minus_sym; right; f_equal; ring.
Qed.

Lemma fplus_spec2 (x y : F) : y <= 0 -> frnd (x + y) <= x.
Proof.
intros Hy.
unfold frnd; simpl.
rewrite <- (round_generic radix2 fexp (Znearest choice) x) at 2;
  [|now apply FS_prop].
now apply round_le; [apply FLT_exp_valid|apply valid_rnd_N|lra].
Qed.

Lemma fmult_spec2 x : 0 <= frnd (x * x).
Proof.
unfold fmult, frnd; simpl.
rewrite <- (round_0 radix2 fexp (Znearest choice)).
apply round_le; [now apply FLT_exp_valid|now apply valid_rnd_N|].
apply misc.sqr_ge_0.
Qed.

Lemma sqrt_bpow_ge e : bpow radix2 (e / 2) <= sqrt (bpow radix2 e).
Proof.
rewrite <- (sqrt_square (bpow _ _)); [|now apply bpow_ge_0].
apply sqrt_le_1_alt; rewrite <- bpow_plus; apply bpow_le.
now replace (_ + _)%Z with (2 * (e / 2))%Z by ring; apply Z_mult_div_ge.
Qed.

Lemma fsqrt_spec (x : F) :
  exists d : bounded (1 - 1 / sqrt (1 + 2 * eps)),
    frnd (sqrt x) = (1 + d) * (sqrt x) :> R.
Proof.
assert (Heps := eps_pos).
assert (Pb := om1ds1p2eps_pos eps_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 Pb); simpl.
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_r; [|apply valid_rnd_N]. }
set (x' := Build_FS_of (generic_format_FLX_FLT _ _ _ _ (FS_prop x))).
destruct (flx64.fsqrt_spec choice x') as (d, Hd).
revert Hd; case d; simpl; intros dv dp Hd.
exists (Build_bounded dp); simpl; rewrite <-Hd; apply round_FLT_FLX.
apply (Rle_trans _ (bpow radix2 (emin / 2)%Z)).
{ now apply bpow_le; unfold emin, emax, prec, Z.div. }
apply (Rle_trans _ _ _ (sqrt_bpow_ge _)).
rewrite Rabs_pos_eq; [|now apply sqrt_pos]; apply sqrt_le_1_alt.
assert (H := FS_prop x); revert H.
apply generic_format_ge_bpow; [|exact Px].
intro e; unfold fexp, FLT_exp; apply Z.le_max_r.
Qed.

Lemma exact_shift x e :
  format x -> (emin + prec - mag radix2 x <= e)%Z -> format (x * bpow radix2 e).
Proof.
intros Fx He.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, Rmult_0_l; apply generic_format_0. }
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _ _ _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float radix2).
apply (generic_format_F2R' _ _ _ f).
{ now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc. }
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold fexp, FLT_exp; rewrite Z.max_l; [|omega]; rewrite <- Z.add_max_distr_r.
set (n := (_ - _ + _)%Z); apply (Z.le_trans _ n); [unfold n; omega|].
apply Z.le_max_l.
Qed.

Lemma ulp_exact_shift_pos x e :
  0 < x ->
  (emin + prec <= mag radix2 x)%Z ->
  (emin + prec - mag radix2 x <= e)%Z ->
  ulp radix2 fexp (x * bpow radix2 e) = ulp radix2 fexp x * bpow radix2 e.
Proof.
intros Px Hmx He.
unfold ulp; rewrite Req_bool_false;
  [|now apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat; [|apply bpow_gt_0]].
rewrite Req_bool_false; [|now apply Rgt_not_eq, Rlt_gt].
rewrite <- bpow_plus; f_equal; unfold cexp, fexp, FLT_exp.
rewrite mag_mult_bpow; [|now apply Rgt_not_eq, Rlt_gt].
rewrite Z.max_l; [rewrite Z.max_l|]; omega.
Qed.

Lemma succ_exact_shift_pos x e :
  0 < x ->
  (emin + prec <= mag radix2 x)%Z ->
  (emin + prec - mag radix2 x <= e)%Z ->
  succ radix2 fexp (x * bpow radix2 e) = succ radix2 fexp x * bpow radix2 e.
Proof.
intros Px Hmx He.
rewrite succ_eq_pos; [|now apply Rmult_le_pos; [left|apply bpow_ge_0]].
rewrite succ_eq_pos; [|now left].
now rewrite Rmult_plus_distr_r; f_equal; apply ulp_exact_shift_pos.
Qed.

Definition binary64 : Float_spec :=
  @Build_Float_spec
    format
    format0
    format1
    format_opp
    eps
    eps_pos
    eps_lt_1
    eta
    eta_pos
    frnd
    frnd_F
    frnd_spec
    fplus_spec
    fplus_spec_l
    fplus_spec2
    fmult_spec2
    fsqrt_spec.

End Binary64.
