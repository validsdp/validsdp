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

Lemma frnd_spec (x : R) :
  exists (d : b_eps) (e : b_eta),
  round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R.
Proof.
destruct (error_N_FLT radix2 emin prec Pprec choice x)
  as (d,(e,(Hd,(He,(_,Hr))))).
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
{ destruct (relative_error_N_FLT_ex radix2 emin prec Pprec choice xy Hxy)
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
{ destruct (relative_error_N_FLT_ex radix2 emin prec Pprec choice
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

(** Sufficient condition : emin <= 1 - prec. *)
Lemma decomp (x : F) (Px : 0 < x) :
  exists (mu : F) (e : Z), x = mu * bpow radix2 (2 * e) :> R
                           /\ (emin / 2 <= e)%Z
                           /\ 1 <= mu /\ mu < bpow radix2 2.
Proof.
set (e := ((mag radix2 x - 1) / 2)%Z).
set (mu := x * bpow radix2 (-2 * e)%Z).
assert (Hbe : bpow radix2 (-2 * e) * bpow radix2 (2 * e) = 1).
{ now rewrite <- bpow_plus; case e; simpl; [reflexivity| |]; intro p;
    rewrite Z.pos_sub_diag. }
assert (Fmu : format mu).
{ apply exact_shift; [now apply FS_prop|]; unfold e.
  change (-2)%Z with (Z.opp 2); rewrite <- Zopp_mult_distr_l.
  set (lxm1 := (_ - 1)%Z).
  replace (_ * _)%Z with (2 * (lxm1 / 2) + lxm1 mod 2 - lxm1 mod 2)%Z by ring.
  rewrite <- Z.div_mod; [|now simpl]; apply (Z.le_trans _ (- lxm1)).
  { unfold lxm1, emin, prec, emax; omega. }
  now apply (Zplus_le_reg_l _ _ lxm1); ring_simplify; apply Z_mod_lt. }
exists (Build_FS_of Fmu), e; split; [|split; [|split]].
{ set (e2 := (2 * e)%Z); simpl; unfold mu; rewrite Rmult_assoc.
  now unfold e2; rewrite Hbe, Rmult_1_r. }
{ unfold e; apply Z.div_le_mono; [omega|].
  apply (Zplus_le_reg_r _ _ 1), Zgt_le_succ, Z.lt_gt; ring_simplify.
  apply (Z.le_lt_trans _ (cexp radix2 fexp x)).
  { unfold cexp, fexp, FLT_exp; apply Z.le_max_r. }
  apply mag_generic_gt; [now apply FLT_exp_valid| |now apply FS_prop].
  now apply Rlt_dichotomy_converse; right; apply Rlt_gt. }
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

Lemma sqrt_bpow e : sqrt (bpow radix2 (2 * e)) = bpow radix2 e.
Proof.
change 2%Z with (1 + 1)%Z; rewrite Z.mul_add_distr_r, Z.mul_1_l, bpow_plus.
apply sqrt_square, bpow_ge_0.
Qed.

Lemma mag_1 : mag radix2 1 = 1%Z :> Z.
Proof.
apply mag_unique_pos; rewrite bpow_1; simpl; lra.
Qed.

Lemma Rsqr_le_abs_0_alt x y : x² <= y² -> x <= Rabs y.
Proof.
intro H.
apply (Rle_trans _ (Rabs x)); [apply Rle_abs|apply (Rsqr_le_abs_0 _ _ H)].
Qed.

(** Sufficient condition : emin <= 1 - prec. *)
Lemma fsqrt_spec2 (x : F) :
  exists d : bounded (sqrt (1 + 2 * eps) - 1),
    sqrt x = (1 + d) * frnd (sqrt x) :> R.
Proof.
assert (Pb : 0 <= sqrt (1 + 2 * eps) - 1).
{ apply (Rplus_le_reg_l 1); ring_simplify; apply (Rle_trans _ (sqrt 1)).
  { rewrite <-(sqrt_square 1) at 1; [apply sqrt_le_1_alt|]; lra. }
  apply sqrt_le_1_alt; assert (H := eps_pos); lra. }
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 Pb); simpl.
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_r; [|apply valid_rnd_N]. }
destruct (decomp x Px) as (mu, (e, (Hmu, (He, (HmuGe1, HmuLtsqradix))))).
assert (He' : (-537 <= e)%Z); [now revert He; unfold emin, emax, prec, Z.div|].
pose (t := sqrt x).
assert (Ht : t = sqrt mu * bpow radix2 e).
{ unfold t; rewrite Hmu, sqrt_mult_alt; [|now apply (Rle_trans _ _ _ Rle_0_1)].
  now rewrite sqrt_bpow. }
destruct (Rle_or_lt mu 1) as [HmuLe1|HmuGt1].
{ exists (bounded_0 Pb); simpl; rewrite Rplus_0_r, Rmult_1_l.
  fold t; rewrite Ht, (Rle_antisym _ _ HmuLe1 HmuGe1), sqrt_1, Rmult_1_l.
  symmetry; apply round_generic; [now apply valid_rnd_N|].
  apply generic_format_bpow'; [now apply FLT_exp_valid|].
  unfold fexp, FLT_exp; rewrite Z.max_l; [unfold prec; omega|].
  apply (Zplus_le_reg_r _ _ prec); unfold emin, emax, prec; omega. }
assert (Hulp1 : ulp radix2 fexp 1 = 2 * eps).
{ unfold ulp, fexp, FLT_exp, cexp; rewrite Req_bool_false; [|lra].
  rewrite mag_1, Z.max_l; [|unfold emin, prec, emax; omega].
  unfold Z.sub; rewrite bpow_plus, bpow_1; unfold eps, prec; simpl; lra. }
assert (Hsucc1 : succ radix2 fexp 1 = 1 + 2 * eps).
{ unfold succ, ulp, cexp, fexp, FLT_exp; rewrite Rle_bool_true; [|lra].
  rewrite Req_bool_false; [|lra]; rewrite mag_1, Z.max_l.
  { now unfold Z.sub, eps, prec; rewrite bpow_plus, bpow_1. }
  now unfold emin, emax, prec, Z.div. }
assert (HmuGe1p2eps : 1 + 2 * eps <= mu).
{ rewrite <- Hsucc1.
  now apply succ_le_lt; [apply FLT_exp_valid|apply format1|apply FS_prop|]. }
destruct (Rle_or_lt mu (1 + 2 * eps)) as [HmuLe1p2eps|HmuGt1p2eps].
{ assert (Hmu' := Rle_antisym _ _ HmuLe1p2eps HmuGe1p2eps).
  assert (Hsqrtmu : 1 <= sqrt mu < 1 + eps); [rewrite Hmu'; split|].
  { rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt; lra. }
  { rewrite <- sqrt_square; [|lra]; apply sqrt_lt_1_alt; split; [lra|].
    ring_simplify; assert (0 < eps ^ 2); [apply Rcomplements.pow2_gt_0|]; lra. }
  assert (Fbpowe : generic_format radix2 fexp (bpow radix2 e)).
  { apply FLT_format_bpow; [now simpl|]; unfold emin, emax, prec; omega. }
  assert (Hrt : frnd t = bpow radix2 e :> R).
  { rewrite Ht; unfold frnd; simpl; apply Rle_antisym.
    { apply round_N_le_midp; [now apply FLT_exp_valid|exact Fbpowe|].
      apply (Rlt_le_trans _ ((1 + eps) * bpow radix2 e)).
      { now apply Rmult_lt_compat_r; [apply bpow_gt_0|]. }
      unfold succ; rewrite Rle_bool_true; [|now apply bpow_ge_0].
      rewrite ulp_bpow; unfold fexp, FLT_exp; rewrite Z.max_l.
      { unfold Z.sub; do 2 rewrite bpow_plus.
        unfold prec, eps; right; rewrite bpow_1; simpl; field.
        rewrite IZR_Zpower_pos; apply powerRZ_NOR; lra. }
      unfold emin, emax, prec; omega. }
    apply round_ge_generic;
      [now apply FLT_exp_valid|now apply valid_rnd_N|exact Fbpowe|].
    rewrite <- (Rmult_1_l (bpow _ _)) at 1.
    now apply Rmult_le_compat_r; [apply bpow_ge_0|]. }
  exists (Build_bounded (or_intror (Rabs_pos_eq _ Pb))); simpl.
  revert Hrt; unfold frnd, t; simpl; intro Hrt; rewrite Hrt.
  fold t; rewrite Ht, Hmu'; ring. }
assert (Hulp1p2eps : ulp radix2 fexp (1 + 2 * eps) = 2 * eps).
{ destruct (ulp_succ_pos _ _ _ format1 Rlt_0_1) as [Hsucc|Hsucc].
  { now rewrite <- Hsucc1, <- Hulp1. }
  casetype False; revert Hsucc; apply Rlt_not_eq.
  rewrite Hsucc1, mag_1, bpow_1; simpl; apply Rplus_lt_compat_l.
  change 2 with (IZR radix2); unfold eps; rewrite <- bpow_1, <- bpow_plus.
  now apply (Rlt_le_trans _ (bpow radix2 0)); [apply bpow_lt|right]. }
assert (Hsucc1p2eps : succ radix2 fexp (1 + 2 * eps) = 1 + 4 * eps).
{ unfold succ; rewrite Rle_bool_true; [rewrite Hulp1p2eps; ring|].
  apply Rplus_le_le_0_compat; [lra|rewrite <- Hulp1; apply ulp_ge_0]. }
assert (HmuGe1p4eps : 1 + 4 * eps <= mu).
{ rewrite <- Hsucc1p2eps.
  apply succ_le_lt; [now apply FLT_exp_valid| |now apply FS_prop|now simpl].
  rewrite <- Hsucc1.
  now apply generic_format_succ; [apply FLT_exp_valid|apply format1]. }
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
    do 2 rewrite <- bpow_plus; f_equal; unfold cexp, fexp, FLT_exp.
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
    rewrite Hmagt; rewrite Z.max_l; [unfold prec; ring|].
    unfold emin, emax, prec; omega. }
  rewrite Ht; apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
  now apply (Rlt_le_trans _ 1); [lra|rewrite <- sqrt_1; apply sqrt_le_1_alt]. }
assert (Hrt : (1 + 2 * eps) * bpow radix2 e <= frnd t).
{ apply round_N_ge_midp; [now apply FLT_exp_valid| |].
  { rewrite <- Hsucc1; apply exact_shift.
    { now apply generic_format_succ; [apply FLT_exp_valid|apply format1]. }
    assert (H : (1 <= mag radix2 (succ radix2 fexp 1))%Z).
    { apply (Z.le_trans _ (mag radix2 1)); [now rewrite mag_1|].
      apply mag_le; [lra|apply succ_ge_id]. }
    unfold emin, emax, prec; omega. }
  set (p := pred _ _ _).
  assert (Hp : p = bpow radix2 e).
  { rewrite <- (pred_succ radix2 _ (bpow radix2 e)).
    { unfold p; f_equal; rewrite <- Hsucc1.
      rewrite <- succ_exact_shift_pos; [now rewrite Rmult_1_l|lra| |].
      { now rewrite mag_1; unfold emin, emax, prec. }
      rewrite mag_1; unfold emin, emax, prec; omega. }
    apply generic_format_bpow; unfold fexp, FLT_exp; rewrite Z.max_l;
      unfold emin, emax, prec; omega. }
  now rewrite Hp, Ht; apply (Rle_lt_trans _ ((1 + eps) * bpow radix2 e));
    [right; field|apply Rmult_lt_compat_r; [apply bpow_gt_0|]]. }
assert (Peps := eps_pos).
assert (Prt : 0 < frnd t).
{ revert Hrt; apply Rlt_le_trans.
  now apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (H : Rabs ((sqrt x - frnd (sqrt x)) / frnd (sqrt x))
            <= sqrt (1 + 2 * eps) - 1).
{ unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ _));
    [|now left; apply Rinv_0_lt_compat].
  apply (Rle_trans _ ((eps * bpow radix2 e) / frnd t)).
  { unfold Rdiv; apply Rmult_le_compat_r; [now left; apply Rinv_0_lt_compat|].
    rewrite Rabs_minus_sym; apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)).
    fold t; rewrite Hulpt; right; field. }
  apply (Rle_trans _ (eps / (1 + 2 * eps))).
  { apply (Rle_trans _ (eps * bpow radix2 e / ((1 + 2 * eps) * bpow radix2 e))).
    { unfold Rdiv; apply Rmult_le_compat_l;
        [now apply Rmult_le_pos; [apply eps_pos|apply bpow_ge_0]|].
      now apply Rinv_le; [|exact Hrt];
        apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
    right; field; split; apply Rgt_not_eq, Rlt_gt; [|apply bpow_gt_0]; lra. }
  apply (Rplus_le_reg_r 1); ring_simplify.
  rewrite <- (Rabs_pos_eq _ (sqrt_ge_0 _)); apply Rsqr_le_abs_0_alt.
  rewrite Rsqr_sqrt; [|lra].
  replace (_ + 1) with ((1 + 3 * eps) / (1 + 2 * eps)); [|field; lra].
  rewrite Rsqr_div; [|lra].
  apply (Rmult_le_reg_r ((1 + 2 * eps)²)); [apply Rlt_0_sqr; lra|].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l;
    [rewrite Rmult_1_r|apply Rgt_not_eq, Rlt_gt, Rlt_0_sqr; lra].
  apply (Rplus_le_reg_r (-1 - 6 * eps - 9 * eps^2)); unfold Rsqr; ring_simplify.
  assert (H3 : 0 <= eps^3) by now apply pow_le.
  assert (H2 : 0 <= eps^2) by now apply pow_le.
  lra. }
now exists (Build_bounded H); simpl; field; apply Rgt_not_eq, Rlt_gt.
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
    frnd_spec
    fplus_spec
    fplus_spec2
    fmult_spec2
    fsqrt_spec.

End Binary64.
