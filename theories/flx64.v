(** * FLX 53 satisfy hypothesis in [Float_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLX(53) is a model
    of binary64 without underflows, NaNs nor overflows. *)

Require Import Reals.

Require Import float_spec.

Require Import Flocq.Core.Zaux.
Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLX.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Prop.Relative.
Require Import Flocq.Prop.Plus_error.

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

Definition format x := generic_format radix2 fexp x.

Let F := FS_of format.

Lemma format0 : format 0.
Proof. apply generic_format_0. Qed.

Lemma format1 : format 1.
Proof.
unfold format, generic_format, scaled_mantissa, cexp, F2R; simpl.
rewrite Rmult_1_l, (mag_unique radix2 1 1).
{ unfold fexp, FLX_exp.
  rewrite <- IZR_Zpower; [|unfold prec; omega].
  rewrite Ztrunc_IZR, IZR_Zpower; [|unfold prec; omega].
  rewrite <- bpow_plus.
  now replace (_ + _)%Z with Z0 by ring. }
rewrite Rabs_R1; simpl; split; [now right|].
unfold Z.pow_pos; simpl; lra.
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
  exists (d : b_eps) (e : b_eta),
    round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R
    /\ d * e = 0.
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
now rewrite Rmult_comm, Rplus_0_r, Rmult_0_r.
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

Lemma fplus_spec_l (x y : F) : Rabs (frnd (x + y) - (x + y)) <= Rabs x.
Proof.
apply (Rle_trans _ (Rabs (y - (x + y)))).
{ now apply round_N_pt; [apply FLX_exp_valid|apply FS_prop]. }
rewrite Rabs_minus_sym; right; f_equal; ring.
Qed.

Lemma fplus_spec2 (x y : F) : y <= 0 -> frnd (x + y) <= x.
Proof.
intros Hy.
unfold frnd; simpl.
rewrite <- (round_generic radix2 fexp (Znearest choice) x) at 2;
  [|now apply FS_prop].
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

Lemma fsqrt_spec_b (x : F) :
  exists d : bounded (sqrt (1 + 2 * eps) - 1),
    sqrt x = (1 + d) * frnd (sqrt x) :> R.
Proof.
Admitted.

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
    frnd_F
    frnd_spec
    fplus_spec
    fplus_spec_l
    fplus_spec2
    fmult_spec2
    fsqrt_spec
    fsqrt_spec_b.

End Flx64.
