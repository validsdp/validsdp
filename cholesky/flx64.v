(** * CoqInterval floats satisfy hypothesis in [Float_infnan_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLX(53) is a model
    of binary64 without underflows, NaNs nor overflows. *)

Require Import Reals.

Require Import float_spec.

Require Import Flocq.Core.Fcore_Zaux.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Core.Fcore_defs.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_FLX.
Require Import Flocq.Core.Fcore_ulp.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Prop.Fprop_plus_error.

Require Import Psatz.

Open Scope R_scope.

Section Flx64.

Let prec := 53%Z.
Let emax := 1024%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLX_exp prec.

Lemma Pprec : (0 < prec)%Z.
Proof. unfold prec; omega. Qed.

Instance valid_exp : Valid_exp fexp.
Proof. now apply FLX_exp_valid. Qed.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition format x := generic_format radix2 fexp x.

Let F := Ff format.

Lemma format0 : format 0.
Proof.
unfold format, generic_format, scaled_mantissa, F2R; simpl.
rewrite Rmult_0_l.
change 0 with (Z2R 0); rewrite Ztrunc_Z2R.
now rewrite Rmult_0_l.
Qed.

Lemma format1 : format 1.
Proof.
unfold format, generic_format, scaled_mantissa, canonic_exp, F2R; simpl.
rewrite Rmult_1_l, (ln_beta_unique radix2 1 1).
{ unfold fexp, FLX_exp.
  rewrite <- Z2R_Zpower; [|unfold prec; omega].
  rewrite Ztrunc_Z2R, Z2R_Zpower; [|unfold prec; omega].
  rewrite <- bpow_plus.
  now replace (_ + _)%Z with Z0 by ring. }
rewrite Rabs_R1; simpl; split; lra.
Qed.

Lemma format_opp x : format x -> format (- x).
Proof. apply generic_format_opp. Qed.
  
Definition eps := bpow radix2 (-53).

Lemma eps_pos : 0 <= eps.
Proof. apply bpow_ge_0. Qed.

Lemma eps_lt_1 : eps < 1.
Proof.
unfold eps, bpow.
apply (Rmult_lt_reg_r (Z2R (Z.pow_pos radix2 53)));
  [now fold (bpow radix2 53); apply bpow_gt_0|].
rewrite Rinv_l; [rewrite Rmult_1_l|now apply Rgt_not_eq, Rlt_gt;
                                    fold (bpow radix2 53); apply bpow_gt_0].
change 1 with (Z2R 1); apply Z2R_lt.
unfold Z.pow_pos; simpl.
omega.
Qed.

Let b_eps := bounded eps.

Definition eta := bpow radix2 (-1075).

Lemma eta_pos : 0 < eta.
Proof. apply bpow_gt_0. Qed.

Let b_eta := bounded eta.

(** The tie-break rule doesn't really matter. *)
Variable choice : Z -> bool.

(** All we need is rounding to nearest. *)
Definition frnd (x : R) : F :=
  Build_Ff (generic_format_round radix2 fexp (Znearest choice) x).

Lemma frnd_spec (x : R) :
  exists (d : b_eps) (e : b_eta),
  round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R.
Proof.
destruct (relative_error_N_FLX_ex radix2 prec Pprec choice x) as (d, (Hd, Hr)).
assert (Hd' : Rabs d <= eps).
{ apply (Rle_trans _ _ _ Hd).
  apply (Rmult_le_reg_l 2); [lra|].
  rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
  change 2 with (bpow radix2 1).
  unfold eps; rewrite <- bpow_plus.
  now apply bpow_le. }
exists {| bounded_val := d; bounded_prop := Hd' |}.
exists (bounded_0 (Rlt_le _ _ eta_pos)).
now rewrite Rmult_comm, Rplus_0_r.
Qed.

Lemma fplus_spec (x y : F) :
  exists d : b_eps, frnd (x + y) = (1 + d) * (x + y) :> R.
Proof.
set (xy := x + y).
set (fxy := frnd xy).
destruct (relative_error_N_FLX_ex radix2 prec Pprec choice xy)
    as (d, (Hd1, Hd2)).
assert (Hd3 : Rabs d <= eps).
{ apply (Rle_trans _ _ _ Hd1).
  apply (Rmult_le_reg_l 2); [lra|].
  rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
  change 2 with (bpow radix2 1).
  unfold eps; rewrite <- bpow_plus.
  now apply bpow_le. }
exists {| bounded_val := d; bounded_prop := Hd3 |}.
now rewrite Rmult_comm.
Qed.

Lemma fplus_spec2 (x y : F) : y <= 0 -> frnd (x + y) <= x.
Proof.
intros Hy.
unfold frnd; simpl.
rewrite <- (round_generic radix2 fexp (Znearest choice) x) at 2;
  [|now apply F_prop].
now apply round_le; [apply FLX_exp_valid|apply valid_rnd_N|lra].
Qed.

Lemma fmult_spec2 x : 0 <= frnd (x * x).
Proof.
unfold fmult, frnd; simpl.
rewrite <- (round_0 radix2 fexp (Znearest choice)).
apply round_le; [now apply FLX_exp_valid|now apply valid_rnd_N|].
apply misc.sqr_ge_0.
Qed.

(** Sufficient condition : emin <= 2 * (1 - prec). *)
Lemma fsqrt_spec (x : F) :
  exists d : b_eps, frnd (sqrt x) = (1 + d) * (sqrt x) :> R.
Proof.
destruct (Rlt_or_le x 0) as [Nx|Px].
{ exists (bounded_0 eps_pos).
  simpl; rewrite (sqrt_neg x (Rlt_le x 0 Nx)), Rmult_0_r.
  now rewrite round_0; [|apply valid_rnd_N]. }
destruct (relative_error_N_FLX_ex radix2 prec Pprec choice
                                    (sqrt x)) as (d, (Hd1, Hd2)).
assert (Hd3 : Rabs d <= eps).
{ apply (Rle_trans _ _ _ Hd1).
  apply (Rmult_le_reg_l 2); [lra|].
  rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
  change 2 with (bpow radix2 1).
  unfold eps; rewrite <- bpow_plus.
  now apply bpow_le. }
exists {| bounded_val := d; bounded_prop := Hd3 |}.
now rewrite Rmult_comm.
Qed.

Definition flx64 : Float_spec :=
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
    frnd_spec
    fplus_spec
    fplus_spec2
    fmult_spec2
    fsqrt_spec.

End Flx64.
