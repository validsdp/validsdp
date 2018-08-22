(** * IEEE754 binary64 format satisfies hypothesis in [Float_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLT(-1074, 53) is a
    model of binary64 with gradual underflow but without NaNs nor
    overflows (which could be easily handled afterward). *)

Require Import Reals.

Require Import float_spec.

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
destruct (error_N_FLT radix2 emin prec Pprec choice x)
  as (d,(e,(Hd,(He,(Hde0,Hr))))).
assert (Hd' : Rabs d <= eps).
{ apply (Rle_trans _ _ _ Hd).
  apply (Rmult_le_reg_l 2); [lra|].
  rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
  change 2 with (bpow radix2 1).
  unfold eps; rewrite <- bpow_plus.
  now apply bpow_le. }
assert (He' : Rabs e <= eta).
{ apply (Rle_trans _ _ _ He).
  apply (Rmult_le_reg_l 2); [lra|].
  rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
  change 2 with (bpow radix2 1).
  unfold eta; rewrite <- bpow_plus.
  now apply bpow_le. }
exists {| bounded_val := d; bounded_prop := Hd' |}.
exists {| bounded_val := e; bounded_prop := He' |}.
now rewrite Rmult_comm.
Qed.

Lemma fplus_spec (x y : F) :
  exists d : b_eps, frnd (x + y) = (1 + d) * (x + y) :> R.
Proof.
set (xy := x + y).
set (fxy := frnd xy).
destruct (Rle_or_lt (bpow radix2 (emin + prec - 1)) (Rabs xy)) as [Hxy|Hxy].
{ destruct (@relative_error_N_FLT_ex radix2 emin prec Pprec choice xy Hxy)
    as (d, (Hd1, Hd2)).
  assert (Hd3 : Rabs d <= eps).
  { apply (Rle_trans _ _ _ Hd1).
    apply (Rmult_le_reg_l 2); [lra|].
    rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
    change 2 with (bpow radix2 1).
    unfold eps; rewrite <- bpow_plus.
    now apply bpow_le. }
  exists {| bounded_val := d; bounded_prop := Hd3 |}.
  now rewrite Rmult_comm. }
exists (bounded_0 eps_pos); rewrite Rplus_0_r, Rmult_1_l.
assert (Hxy' : Rabs (fxy - xy) <= / 2 * ulp radix2 fexp xy).
unfold fxy; unfold frnd ; simpl.
{ now apply error_le_half_ulp, FLT_exp_valid. }
assert (Hxy'' : format (fxy - xy)).
{ now apply plus_error;
  [apply FLT_exp_valid|apply FLT_exp_monotone|apply FS_prop|apply FS_prop]. }
destruct (Req_dec xy 0) as [Zxy|Nzxy].
{ now unfold fxy, fplus, frnd; simpl; fold xy; rewrite Zxy, round_0;
  [|apply valid_rnd_N]. }
apply Rminus_diag_uniq.
destruct (Req_dec (fxy - xy) 0) as [Zxy|Nzxy']; [assumption|].
set (exy := mag radix2 (fxy - xy)).
assert (Hexy : (exy <= fexp exy)%Z).
{ apply (Zle_trans _ emin); [|now apply Z.le_max_r].
  apply (Zle_trans _ (cexp radix2 fexp xy)).
  { apply (mag_le_bpow _ _ _ Nzxy'), (Rle_lt_trans _ _ _ Hxy').
    apply (Rmult_lt_reg_l 2); [lra|rewrite <- Rmult_assoc, Rinv_r; [|lra]].
    rewrite ulp_neq_0; [|easy].
    change 2%R with (Rplus 1%R 1%R).
    rewrite Rmult_plus_distr_r, Rmult_1_l.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_lt_compat_l, bpow_gt_0. }
  unfold cexp, fexp, FLT_exp.
  rewrite Zmax_right; [now apply Zle_refl|].
  apply (Zplus_le_reg_r _ _ prec); ring_simplify.
  apply (mag_le_bpow _ _ _ Nzxy).
  apply (Rlt_le_trans _ _ _ Hxy), bpow_le; omega. }
destruct (Rtotal_order 0 (fxy - xy)) as [Pxy|[Zxy|Nxy]]; [|now apply eq_sym|].
{ rewrite <- (round_generic radix2 fexp Zfloor (fxy - xy) Hxy'').
  apply round_DN_small_pos with exy; [|assumption].
  destruct exy as (exy', Hexy'); simpl.
  rewrite <- (Rabs_pos_eq (round _ _ _ _ - xy)); [|now apply Rlt_le].
  now apply Hexy', Rgt_not_eq, Rlt_gt. }
apply Rminus_diag_eq, Rminus_diag_uniq_sym.
rewrite <- (round_generic radix2 fexp Zfloor (xy - fxy));
[|now replace (xy - fxy) with (- (fxy - xy)) by ring; apply generic_format_opp].
apply round_DN_small_pos with exy; [|assumption].
destruct exy as (exy', Hexy'); simpl.
rewrite <- (Rabs_right (xy - round _ _ _ _));
  [|now unfold fxy, fplus, frnd in Nxy; simpl in Nxy; lra].
rewrite Rabs_minus_sym; apply Hexy'; lra.
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

(** Sufficient condition : emin <= 2 * (1 - prec). *)
Lemma fsqrt_spec (x : F) :
  exists d : b_eps, frnd (sqrt x) = (1 + d) * (sqrt x) :> R.
Proof.
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 eps_pos).
  simpl; rewrite (sqrt_neg x Nx), Rmult_0_r.
  now rewrite round_0; [|apply valid_rnd_N]. }
destruct (Rle_or_lt (bpow radix2 (emin + prec - 1)) (Rabs (sqrt x)))
  as [Hsx|Hsx].
{ destruct (@relative_error_N_FLT_ex radix2 emin prec Pprec choice
                                    (sqrt x) Hsx) as (d, (Hd1, Hd2)).
  assert (Hd3 : Rabs d <= eps).
  { apply (Rle_trans _ _ _ Hd1).
    apply (Rmult_le_reg_l 2); [lra|].
    rewrite <- Rmult_assoc, Rinv_r; [rewrite Rmult_1_l|lra].
    change 2 with (bpow radix2 1).
    unfold eps; rewrite <- bpow_plus.
    now apply bpow_le. }
  exists {| bounded_val := d; bounded_prop := Hd3 |}.
  now rewrite Rmult_comm. }
exists (bounded_0 eps_pos).
assert (Nzx : x <> 0 :> R).
{ intro H; revert Px; rewrite H; apply Rlt_irrefl. }
casetype False; apply Nzx.
rewrite <- (round_generic radix2 fexp Zfloor x (FS_prop x)).
set (ex := mag radix2 x).
apply round_DN_small_pos with ex.
{ destruct ex as (ex', Hex'); simpl.
  now rewrite <- (Rabs_pos_eq x); [apply Hex'|apply Rlt_le]. }
assert (Hx : Rabs x < bpow radix2 (2 * (emin + prec - 1))).
{ rewrite <- (sqrt_def x (Rlt_le _ _ Px)), Rabs_mult.
  change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l, Zmult_1_l, bpow_plus.
  now apply Rmult_lt_compat; [apply Rabs_pos|apply Rabs_pos| |]. }
apply (Zle_trans _ emin); [|now apply Z.le_max_r].
apply (Zle_trans _ (cexp radix2 fexp x)).
{ apply (mag_le_bpow _ _ _ Nzx), (Rlt_le_trans _ _ _ Hx).
  apply bpow_le; apply (Zle_trans _ emin); [|now apply Z.le_max_r].
  unfold emin, prec, emax; omega. }
unfold cexp, fexp, FLT_exp.
rewrite Zmax_right; [now apply Zle_refl|].
apply (Zplus_le_reg_r _ _ prec); ring_simplify.
apply (mag_le_bpow _ _ _ Nzx).
apply (Rlt_le_trans _ _ _ Hx), bpow_le; unfold emin, prec, emax; omega.
Qed.

Lemma sqrt_bpow_ge e : bpow radix2 (e / 2) <= sqrt (bpow radix2 e).
Proof.
rewrite <- (sqrt_square (bpow _ _)); [|now apply bpow_ge_0].
apply sqrt_le_1_alt; rewrite <- bpow_plus; apply bpow_le.
now replace (_ + _)%Z with (2 * (e / 2))%Z by ring; apply Z_mult_div_ge.
Qed.

Require flx64.

(** Sufficient condition : emin <= 1 - prec. *)
Lemma fsqrt_spec_b (x : F) :
  exists d : bounded (sqrt (1 + 2 * eps) - 1),
    sqrt x = (1 + d) * frnd (sqrt x) :> R.
Proof.
assert (Pb : 0 <= sqrt (1 + 2 * eps) - 1).
{ apply (Rplus_le_reg_l 1); ring_simplify; rewrite <- sqrt_1 at 1.
  apply sqrt_le_1_alt; assert (H := eps_pos); lra. }
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 Pb); simpl.
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_r; [|apply valid_rnd_N]. }
set (x' := Build_FS_of (generic_format_FLX_FLT _ _ _ _ (FS_prop x))).
destruct (flx64.fsqrt_spec_b choice x') as (d, Hd).
exists d; revert Hd; simpl; intro Hd; rewrite Hd at 1; f_equal.
apply eq_sym, round_FLT_FLX.
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
    fsqrt_spec
    fsqrt_spec_b.

End Binary64.
