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

Lemma frnd_spec_aux (x : R) :
  exists (d : b_epsd1peps),
    round radix2 fexp (Znearest choice) x = (1 + d) * x :> R.
Proof.
assert (Peps := eps_pos).
destruct (Req_dec x 0) as [Zx|Nzx].
{ exists (bounded_0 (epsd1peps_pos eps_pos)).
  simpl; rewrite Rplus_0_r, Rmult_1_l, Zx.
  now rewrite round_0; [split|apply valid_rnd_N]. }
set (ufpx := bpow radix2 (mag radix2 x - 1)%Z).  
assert (Pufpx : 0 <= ufpx); [now apply bpow_ge_0|].
assert (H_2_1 : Rabs (frnd x - x) <= eps * ufpx).
{ apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)); right.
  unfold ulp, cexp, fexp, FLX_exp, eps, ufpx; rewrite (Req_bool_false _ _ Nzx).
  rewrite <-bpow_plus; unfold Zminus; rewrite Zplus_assoc, (bpow_plus _ _ (-1)).
  rewrite Rmult_comm; f_equal; f_equal; unfold prec; ring. }
assert (H_2_3 : ufpx + Rabs (frnd x - x) <= Rabs x).
{ apply (Rplus_le_reg_r (- ufpx)); ring_simplify.
  destruct (Rle_or_lt 0 x) as [Sx|Sx].
  { apply (Rle_trans _ (Rabs (ufpx - x))).
    { apply round_N_pt; [now apply FLX_exp_valid|].
      apply generic_format_bpow; unfold fexp, FLX_exp, prec; lia. }
    rewrite Rabs_minus_sym, Rabs_pos_eq.
    { now rewrite Rabs_pos_eq; [right; ring|]. }
    apply (Rplus_le_reg_r ufpx); ring_simplify.
    now rewrite <-(Rabs_pos_eq _ Sx); apply bpow_mag_le. }
  apply (Rle_trans _ (Rabs (- ufpx - x))).
  { apply round_N_pt; [now apply FLX_exp_valid|].
    apply generic_format_opp, generic_format_bpow.
    unfold fexp, FLX_exp, prec; lia. }
  rewrite Rabs_pos_eq; [now rewrite Rabs_left; [right|]|].
  apply (Rplus_le_reg_r x); ring_simplify.
  rewrite <-(Ropp_involutive x); apply Ropp_le_contravar; unfold ufpx.
  rewrite <-mag_opp, <-Rabs_pos_eq; [apply bpow_mag_le|]; lra. }
assert (H : Rabs ((frnd x - x) / x) <= eps / (1 + eps)).
{ assert (H : 0 < ufpx + Rabs (frnd x - x)).
  { apply Rplus_lt_le_0_compat; [apply bpow_gt_0|apply Rabs_pos]. }
  apply (Rle_trans _ (Rabs (frnd x - x) / (ufpx + Rabs (frnd x - x)))).
  { unfold Rdiv; rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos|].
    now rewrite (Rabs_Rinv _ Nzx); apply Rinv_le. }
  apply (Rmult_le_reg_r ((ufpx + Rabs (frnd x - x)) * (1 + eps))).
  { apply Rmult_lt_0_compat; lra. }
  field_simplify; [unfold Rdiv; rewrite Rinv_1, !Rmult_1_r| |]; lra. }
now exists (Build_bounded H); simpl; field.
Qed.

Lemma frnd_spec (x : R) :
  exists (d : b_epsd1peps) (e : b_eta),
    round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R
    /\ d * e = 0.
Proof.
destruct (frnd_spec_aux x) as (d, Hd).
exists d, (bounded_0 (Rlt_le _ _ (eta_pos))); simpl.
now rewrite Rplus_0_r, Rmult_0_r; split.
Qed.

Lemma fplus_spec (x y : F) :
  exists d : b_epsd1peps, frnd (x + y) = (1 + d) * (x + y) :> R.
Proof. now destruct (frnd_spec_aux (x + y)) as (d, Hd); exists d. Qed.

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

Lemma exact_shift x e : format x -> format (x * bpow radix2 e).
Proof.
intro Fx.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, Rmult_0_l; apply generic_format_0. }
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _ _ _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float radix2).
apply (generic_format_F2R' _ _ _ f).
{ now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc. }
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold fexp, FLX_exp; omega.
Qed.

(** Sufficient condition : emin <= 1 - prec. *)
Lemma decomp (x : F) (Px : 0 < x) :
  exists (mu : F) (e : Z), x = mu * bpow radix2 (2 * e) :> R
                           /\ 1 <= mu /\ mu < bpow radix2 2.
Proof.
set (e := ((mag radix2 x - 1) / 2)%Z).
set (mu := x * bpow radix2 (-2 * e)%Z).
assert (Hbe : bpow radix2 (-2 * e) * bpow radix2 (2 * e) = 1).
{ now rewrite <- bpow_plus; case e; simpl; [reflexivity| |]; intro p;
    rewrite Z.pos_sub_diag. }
assert (Fmu : format mu); [now apply exact_shift, FS_prop|].
exists (Build_FS_of Fmu), e; split; [|split].
{ set (e2 := (2 * e)%Z); simpl; unfold mu; rewrite Rmult_assoc.
  now unfold e2; rewrite Hbe, Rmult_1_r. }
{ apply (Rmult_le_reg_r (bpow radix2 (2 * e))).
  { apply bpow_gt_0. }
  rewrite Rmult_1_l; set (e2 := (2 * e)%Z); simpl; unfold mu.
  unfold e2; rewrite Rmult_assoc, Hbe, Rmult_1_r.
  apply (Rle_trans _ (bpow radix2 (mag radix2 x - 1))).
  { now apply bpow_le; unfold e; apply Z_mult_div_ge. }
  set (l := mag _ _); rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)).
  unfold l; apply bpow_mag_le.
  intro Hx; revert Px; rewrite Hx; apply Rlt_irrefl. }
simpl; unfold mu; change (IZR _) with (bpow radix2 2).
apply (Rmult_lt_reg_r (bpow radix2 (2 * e))); [now apply bpow_gt_0|].
rewrite Rmult_assoc, Hbe, Rmult_1_r.
apply (Rlt_le_trans _ (bpow radix2 (mag radix2 x))).
{ rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)) at 1; apply bpow_mag_gt. }
rewrite <- bpow_plus; apply bpow_le; unfold e; set (mxm1 := (_ - 1)%Z).
replace (_ * _)%Z with (2 * (mxm1 / 2) + mxm1 mod 2 - mxm1 mod 2)%Z by ring.
rewrite <- Z.div_mod; [|now simpl].
apply (Zplus_le_reg_r _ _ (mxm1 mod 2 - mag radix2 x)%Z).
now unfold mxm1; ring_simplify; apply Zlt_succ_le; simpl; apply Z_mod_lt.
Qed.

Lemma mag_1 : mag radix2 1 = 1%Z :> Z.
Proof. apply mag_unique_pos; rewrite bpow_1; simpl; lra. Qed.

Lemma succ_FLX_1 : succ radix2 fexp 1 = 1 + bpow radix2 (1 - prec).
Proof.
unfold succ, ulp, cexp, fexp, FLX_exp; rewrite Rle_bool_true; [|lra].
rewrite Req_bool_false; [|lra]; rewrite mag_1.
now unfold Z.sub, eps, prec; rewrite bpow_plus, bpow_1.
Qed.

Lemma ulp_FLX_1 : ulp radix2 fexp 1 = bpow radix2 (1 - prec).
Proof.
unfold ulp, fexp, FLX_exp, cexp; rewrite Req_bool_false; [|lra].
now rewrite mag_1.
Qed.

Lemma fsqrt_spec_aux (x : F) :
  1 <= x ->
  (x = 1 :> R \/ x = 1 + 2 * eps :> R \/ 1 + 4 * eps <= x).
Proof.
intro HxGe1.
destruct (Rle_or_lt x 1) as [HxLe1|HxGt1]; [now left; apply Rle_antisym|right].
assert (H2eps : 2 * eps = bpow radix2 (1 - prec)).
{ now unfold Z.sub, eps; rewrite bpow_plus. }
assert (HmuGe1p2eps : 1 + 2 * eps <= x).
{ rewrite H2eps, <- succ_FLX_1.
  now apply succ_le_lt; [apply FLX_exp_valid|apply format1|apply FS_prop|]. }
destruct (Rle_or_lt x (1 + 2 * eps)) as [HxLe1p2eps|HxGt1p2eps];
  [now left; apply Rle_antisym|right].
assert (Hulp1p2eps : ulp radix2 fexp (1 + 2 * eps) = 2 * eps).
{ destruct (ulp_succ_pos _ _ _ format1 Rlt_0_1) as [Hsucc|Hsucc].
  { now rewrite H2eps, <- succ_FLX_1, <- ulp_FLX_1. }
  exfalso; revert Hsucc; apply Rlt_not_eq.
  rewrite succ_FLX_1, mag_1, bpow_1, <- H2eps; simpl; apply Rplus_lt_compat_l.
  change 2 with (IZR radix2); unfold eps; rewrite <- bpow_1, <- bpow_plus.
  now apply (Rlt_le_trans _ (bpow radix2 0)); [apply bpow_lt|right]. }
assert (Hsucc1p2eps : succ radix2 fexp (1 + 2 * eps) = 1 + 4 * eps).
{ unfold succ; rewrite Rle_bool_true; [rewrite Hulp1p2eps; ring|].
  apply Rplus_le_le_0_compat; [|assert (H := eps_pos)]; lra. }
rewrite <- Hsucc1p2eps.
apply succ_le_lt; [now apply FLX_exp_valid| |now apply FS_prop|now simpl].
rewrite H2eps, <- succ_FLX_1.
now apply generic_format_succ; [apply FLX_exp_valid|apply format1].
Qed.

Lemma sqrt_bpow e : sqrt (bpow radix2 (2 * e)) = bpow radix2 e.
Proof.
change 2%Z with (1 + 1)%Z; rewrite Z.mul_add_distr_r, Z.mul_1_l, bpow_plus.
apply sqrt_square, bpow_ge_0.
Qed.

Lemma ulp_exact_shift_pos x e :
  0 < x ->
  ulp radix2 fexp (x * bpow radix2 e) = ulp radix2 fexp x * bpow radix2 e.
Proof.
intro Px.
unfold ulp; rewrite Req_bool_false;
  [|now apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat; [|apply bpow_gt_0]].
rewrite Req_bool_false; [|now apply Rgt_not_eq, Rlt_gt].
rewrite <- bpow_plus; f_equal; unfold cexp, fexp, FLX_exp.
rewrite mag_mult_bpow; [|now apply Rgt_not_eq, Rlt_gt]; omega.
Qed.

Lemma succ_exact_shift_pos x e :
  0 < x ->
  succ radix2 fexp (x * bpow radix2 e) = succ radix2 fexp x * bpow radix2 e.
Proof.
intro Px.
rewrite succ_eq_pos; [|now apply Rmult_le_pos; [left|apply bpow_ge_0]].
rewrite succ_eq_pos; [|now left].
now rewrite Rmult_plus_distr_r; f_equal; apply ulp_exact_shift_pos.
Qed.

Lemma Rsqr_le_abs_0_alt x y : x² <= y² -> x <= Rabs y.
Proof.
intro H.
apply (Rle_trans _ (Rabs x)); [apply Rle_abs|apply (Rsqr_le_abs_0 _ _ H)].
Qed.

(** Requires eps <= 1/2 *)
Lemma fsqrt_spec_aux' :
  eps / sqrt (1 + 4 * eps) <= 1 - 1 / sqrt (1 + 2 * eps).
Proof.
assert (Peps := eps_pos).
unfold Rdiv; apply (Rplus_le_reg_r (/ sqrt (1 + 2 * eps))); ring_simplify.
apply (Rmult_le_reg_r (sqrt (1 + 4 * eps) * sqrt (1 + 2 * eps))).
{ apply Rmult_lt_0_compat; apply sqrt_lt_R0; lra. }
field_simplify; [|split; apply Rgt_not_eq, Rlt_gt, sqrt_lt_R0; lra].
unfold Rdiv; rewrite Rinv_1, !Rmult_1_r.
apply Rsqr_incr_0_var; [|now apply Rmult_le_pos; apply sqrt_pos].
rewrite <-sqrt_mult; [|lra|lra].
rewrite Rsqr_sqrt; [|apply Rmult_le_pos; lra].
unfold Rsqr; ring_simplify; unfold pow; rewrite !Rmult_1_r.
rewrite !sqrt_def; [|lra|lra].
apply (Rplus_le_reg_r (-eps * eps - 1 -4 * eps - 2 * eps ^ 3)); ring_simplify.
apply Rsqr_incr_0_var.
{ unfold Rsqr; ring_simplify.
  unfold pow; rewrite !Rmult_1_r, !sqrt_def; [|lra|lra].
  apply (Rplus_le_reg_r (-32 * eps ^ 4 - 24 * eps ^ 3 - 4 * eps ^ 2)).    
  ring_simplify.
  replace (_ + _) with (((4 * eps ^ 2 - 28 * eps + 9) * eps + 4) * eps ^ 3)
    by ring.
  apply Rmult_le_pos; [|now apply pow_le, eps_pos].
  assert (Heps_le_half : eps <= 1 / 2).
  { unfold eps, bpow, Rdiv; rewrite Rmult_1_l; apply Rinv_le; [lra|].
    now apply IZR_le. }
  apply (Rle_trans _ (-8 * eps + 4)); [lra|].
  apply Rplus_le_compat_r, Rmult_le_compat_r; [apply eps_pos|].
  now assert (H : 0 <= eps ^ 2); [apply pow2_ge_0|lra]. }
assert (H : eps ^ 3 <= eps ^ 2).
{ unfold pow; rewrite <-!Rmult_assoc, Rmult_1_r.
  apply Rmult_le_compat_l; [apply misc.sqr_ge_0|apply Rlt_le, eps_lt_1]. }
now assert (H' : 0 <= eps ^ 2); [apply pow2_ge_0|lra].
Qed.

Lemma fsqrt_spec (x : F) :
  exists d : bounded (1 - 1 / sqrt (1 + 2 * eps)),
    frnd (sqrt x) = (1 + d) * (sqrt x) :> R.
Proof.
assert (Peps := eps_pos).
assert (Peps' : 0 < eps); [now unfold eps; apply bpow_gt_0|].
assert (Pb := om1ds1p2eps_pos eps_pos).
assert (Pb' := s1p2epsm1_pos eps_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 Pb); simpl.
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_r; [|apply valid_rnd_N]. }
destruct (decomp x Px) as (mu, (e, (Hmu, (HmuGe1, HmuLtsqradix)))).
pose (t := sqrt x).
assert (Ht : t = sqrt mu * bpow radix2 e).
{ unfold t; rewrite Hmu, sqrt_mult_alt; [|now apply (Rle_trans _ _ _ Rle_0_1)].
  now rewrite sqrt_bpow. }
destruct (fsqrt_spec_aux _ HmuGe1) as [Hmu'|[Hmu'|Hmu']].
{ exists (bounded_0 Pb); simpl; rewrite Rplus_0_r, Rmult_1_l.
  fold t; rewrite Ht, Hmu', sqrt_1, Rmult_1_l.
  apply round_generic; [now apply valid_rnd_N|].
  apply generic_format_bpow'; [now apply FLX_exp_valid|].
  unfold fexp, FLX_exp, prec; omega. }
{ assert (Hsqrtmu : 1 <= sqrt mu < 1 + eps); [rewrite Hmu'; split|].
  { rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt; lra. }
  { rewrite <- sqrt_square; [|lra]; apply sqrt_lt_1_alt; split; [lra|].
    ring_simplify; assert (0 < eps ^ 2); [apply Rcomplements.pow2_gt_0|]; lra. }
  assert (Fbpowe : generic_format radix2 fexp (bpow radix2 e)).
  { apply generic_format_bpow; unfold fexp, FLX_exp, prec; omega. }
  assert (Hrt : frnd t = bpow radix2 e :> R).
  { rewrite Ht; unfold frnd; simpl; apply Rle_antisym.
    { apply round_N_le_midp; [now apply FLX_exp_valid|exact Fbpowe|].
      apply (Rlt_le_trans _ ((1 + eps) * bpow radix2 e)).
      { now apply Rmult_lt_compat_r; [apply bpow_gt_0|]. }
      unfold succ; rewrite Rle_bool_true; [|now apply bpow_ge_0].
      rewrite ulp_bpow; unfold fexp, FLX_exp.
      unfold Z.sub; do 2 rewrite bpow_plus.
      unfold prec, eps; right; rewrite bpow_1; simpl; field.
      rewrite IZR_Zpower_pos; apply powerRZ_NOR; lra. }
    apply round_ge_generic;
      [now apply FLX_exp_valid|now apply valid_rnd_N|exact Fbpowe|].
    rewrite <- (Rmult_1_l (bpow _ _)) at 1.
    now apply Rmult_le_compat_r; [apply bpow_ge_0|]. }
  exists (bounded_opp (Build_bounded (or_intror (Rabs_pos_eq _ Pb)))); simpl.
  revert Hrt; unfold frnd, t; simpl; intro Hrt; rewrite Hrt.
  fold t; rewrite Ht, Hmu'; field; lra. }
assert (Hsqrtmu : 1 + eps < sqrt mu).
{ apply (Rlt_le_trans _ (sqrt (1 + 4 * eps))); [|now apply sqrt_le_1_alt].
  assert (P1peps : 0 <= 1 + eps)
    by now apply Rplus_le_le_0_compat; [lra|apply eps_pos].
  rewrite <- (sqrt_square (1 + eps)); [|lra].
  apply sqrt_lt_1_alt; split; [now apply Rmult_le_pos|].
  apply (Rplus_lt_reg_r (-1 - 2 * eps)); ring_simplify; simpl.
  rewrite Rmult_1_r; apply Rmult_lt_compat_r.
  { now unfold eps; apply bpow_gt_0. }
  now apply (Rlt_le_trans _ 1); [exact eps_lt_1|lra]. }
assert (Hulpt : ulp radix2 fexp t = 2 * eps * bpow radix2 e).
{ unfold ulp; rewrite Req_bool_false; [|apply Rgt_not_eq, Rlt_gt].
  { change 2 with (IZR radix2); rewrite <- bpow_1; unfold eps.
    do 2 rewrite <- bpow_plus; f_equal; unfold cexp, fexp, FLX_exp.
    assert (Hmagt : (mag radix2 t = 1 + e :> Z)%Z).
    { apply mag_unique.
      unfold t; rewrite (Rabs_pos_eq _ (Rlt_le _ _ (sqrt_lt_R0 _ Px))).
      fold t; split.
      { rewrite Ht; replace (_ - _)%Z with e by ring.
        rewrite <- (Rmult_1_l (bpow _ _)) at 1; apply Rmult_le_compat_r.
        { apply bpow_ge_0. }
        now rewrite <- sqrt_1; apply sqrt_le_1_alt. }
      rewrite bpow_plus, bpow_1, Ht; simpl.
      apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
      rewrite <- sqrt_square; [|lra]; apply sqrt_lt_1_alt; split; [lra|].
      now apply (Rlt_le_trans _ _ _ HmuLtsqradix); right. }
    rewrite Hmagt; unfold prec; omega. }
  rewrite Ht; apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
  now apply (Rlt_le_trans _ 1); [lra|rewrite <- sqrt_1; apply sqrt_le_1_alt]. }
assert (Pt : 0 < t).
{ rewrite Ht; apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (H : Rabs ((frnd (sqrt x) - sqrt x) / sqrt x)
            <= 1 - 1 / sqrt (1 + 2 * eps)).
{ unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ _));
    [|now left; apply Rinv_0_lt_compat].
  apply (Rle_trans _ ((eps * bpow radix2 e) / t)).
  { unfold Rdiv; apply Rmult_le_compat_r; [now left; apply Rinv_0_lt_compat|].
    apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)).
    fold t; rewrite Hulpt; right; field. }
  apply (Rle_trans _ (eps / sqrt (1 + 4 * eps))).
  { apply (Rle_trans _ (eps * bpow radix2 e
                                   / (sqrt (1 + 4 * eps) * bpow radix2 e))).
    { unfold Rdiv; apply Rmult_le_compat_l;
        [now apply Rmult_le_pos; [apply eps_pos|apply bpow_ge_0]|].
      apply Rinv_le.
      { apply Rmult_lt_0_compat; [apply sqrt_lt_R0; lra|apply bpow_gt_0]. }
      now rewrite Ht; apply Rmult_le_compat_r;
        [apply bpow_ge_0|apply sqrt_le_1_alt]. }
    right; field; split; apply Rgt_not_eq, Rlt_gt;
      [apply sqrt_lt_R0; lra|apply bpow_gt_0]. }
  apply fsqrt_spec_aux'. }
now exists (Build_bounded H); simpl; field; apply Rgt_not_eq, Rlt_gt.
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
    frnd_F
    frnd_spec
    fplus_spec
    fplus_spec_l
    fplus_spec2
    fmult_spec2
    fsqrt_spec.

End Flx64.
