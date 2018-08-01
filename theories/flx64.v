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

Lemma frnd_spec_b_aux (x : R) :
  exists (d : b_eps), x = (1 + d) * round radix2 fexp (Znearest choice) x :> R.
Proof.
set (r := round _ _ _ _).
destruct (Req_dec r 0) as [Zr|Nzr].
{ exists (bounded_0 eps_pos).
  rewrite Zr; simpl; rewrite !Rmult_0_r.
  revert Zr; apply eq_0_round_0_FLX; [apply Pprec|apply valid_rnd_N]. }
set (d := (x - r) / r).
assert (Hd : Rabs d <= eps).
{ unfold d, Rdiv; rewrite Rabs_mult, (Rabs_Rinv _ Nzr).
  apply (Rmult_le_reg_r (Rabs r)); [now apply Rabs_pos_lt|].
  rewrite Rmult_assoc, Rinv_l; [rewrite Rmult_1_r|now apply Rabs_no_R0].
  unfold r; rewrite Rabs_minus_sym.
  apply (Rle_trans _ _ _
                   (relative_error_N_FLX_round radix2 prec Pprec choice x)).
  apply Rmult_le_compat_r; [now apply Rabs_pos|right].
  unfold eps, prec; rewrite bpow_plus, (Rmult_comm (bpow _ _)), <-Rmult_assoc.
  rewrite bpow_1; simpl; lra. }
exists (Build_bounded Hd).
now simpl; unfold d; field.
Qed.

Lemma frnd_spec_b (x : R) :
  exists (d : b_eps) (e : b_eta),
    x = (1 + d) * round radix2 fexp (Znearest choice) x + e :> R
    /\ d * e = 0.
Proof.
assert (Hd := frnd_spec_b_aux x).
destruct Hd as (d, Hd).
exists d.
exists (bounded_0 (Rlt_le _ _ (eta_pos))).
now simpl; rewrite Rplus_0_r, Rmult_0_r; split; [|reflexivity].
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

Lemma fplus_spec_b (x y : F) :
  exists d : b_eps, x + y = (1 + d) * frnd (x + y) :> R.
Proof.
assert (Hd := frnd_spec_b_aux (x + y)).
destruct Hd as (d, Hd).
now exists d.
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

Lemma ulp_FLX_1 : ulp radix2 fexp 1 = bpow radix2 (1 - prec).
Proof.
unfold ulp, fexp, FLX_exp, cexp; rewrite Req_bool_false; [|lra].
now rewrite mag_1.
Qed.

Lemma succ_FLX_1 : succ radix2 fexp 1 = 1 + bpow radix2 (1 - prec).
Proof.
unfold succ, ulp, cexp, fexp, FLX_exp; rewrite Rle_bool_true; [|lra].
rewrite Req_bool_false; [|lra]; rewrite mag_1.
now unfold Z.sub, eps, prec; rewrite bpow_plus, bpow_1.
Qed.

Lemma fsqrt_spec_b_aux (x : F) :
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

(** Sufficient condition : emin <= 1 - prec. *)
Lemma fsqrt_spec_b (x : F) :
  exists d : bounded (sqrt (1 + 2 * eps) - 1),
    sqrt x = (1 + d) * frnd (sqrt x) :> R.
Proof.
assert (Peps := eps_pos).
assert (Peps' : 0 < eps); [now unfold eps; apply bpow_gt_0|].
assert (Pb : 0 <= sqrt (1 + 2 * eps) - 1).
{ apply (Rplus_le_reg_l 1); ring_simplify; rewrite <- sqrt_1 at 1.
  apply sqrt_le_1_alt; lra. }
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists (bounded_0 Pb); simpl.
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_r; [|apply valid_rnd_N]. }
destruct (decomp x Px) as (mu, (e, (Hmu, (HmuGe1, HmuLtsqradix)))).
pose (t := sqrt x).
assert (Ht : t = sqrt mu * bpow radix2 e).
{ unfold t; rewrite Hmu, sqrt_mult_alt; [|now apply (Rle_trans _ _ _ Rle_0_1)].
  now rewrite sqrt_bpow. }
destruct (fsqrt_spec_b_aux _ HmuGe1) as [Hmu'|[Hmu'|Hmu']].
{ exists (bounded_0 Pb); simpl; rewrite Rplus_0_r, Rmult_1_l.
  fold t; rewrite Ht, Hmu', sqrt_1, Rmult_1_l.
  symmetry; apply round_generic; [now apply valid_rnd_N|].
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
  exists (Build_bounded (or_intror (Rabs_pos_eq _ Pb))); simpl.
  revert Hrt; unfold frnd, t; simpl; intro Hrt; rewrite Hrt.
  fold t; rewrite Ht, Hmu'; ring. }
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
assert (H2eps : 2 * eps = bpow radix2 (1 - prec)).
{ now unfold Z.sub, eps; rewrite bpow_plus. }
assert (Hrt : (1 + 2 * eps) * bpow radix2 e <= frnd t).
{ apply round_N_ge_midp; [now apply FLX_exp_valid| |].
  { rewrite H2eps, <- succ_FLX_1; apply exact_shift.
    now apply generic_format_succ; [apply FLX_exp_valid|apply format1]. }
  set (p := pred _ _ _).
  assert (Hp : p = bpow radix2 e).
  { rewrite <- (pred_succ radix2 _ (bpow radix2 e)).
    { unfold p; f_equal; rewrite H2eps, <- succ_FLX_1.
      rewrite <- succ_exact_shift_pos; [now rewrite Rmult_1_l|lra]. }
    apply generic_format_bpow; unfold fexp, FLX_exp; unfold prec; omega. }
  now rewrite Hp, Ht; apply (Rle_lt_trans _ ((1 + eps) * bpow radix2 e));
    [right; field|apply Rmult_lt_compat_r; [apply bpow_gt_0|]]. }
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
  replace (_ + 1) with ((1 + 3 * eps) / (1 + 2 * eps)); [|field; lra].
  rewrite Rsqr_sqrt; [|lra]; rewrite Rsqr_div; [|lra].
  apply (Rmult_le_reg_r ((1 + 2 * eps)²)); [apply Rlt_0_sqr; lra|].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l;
    [rewrite Rmult_1_r|apply Rgt_not_eq, Rlt_gt, Rlt_0_sqr; lra].
  apply (Rplus_le_reg_r (-1 - 6 * eps - 9 * eps^2)); unfold Rsqr; ring_simplify.
  now assert (H : 0 <= eps^2 /\ 0 <= eps^3); [split; apply pow_le|lra]. }
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
    frnd_spec_b
    fplus_spec
    fplus_spec_b
    fplus_spec_l
    fplus_spec2
    fmult_spec2
    fsqrt_spec
    fsqrt_spec_b.

End Flx64.
