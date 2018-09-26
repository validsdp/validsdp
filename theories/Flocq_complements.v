Require Import ZArith.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.Digits.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Core.Round_NE.
Require Import Flocq.IEEE754.Binary.

Require Import Psatz.

Section Bsucc_pred.

Arguments exist {A} {P}.

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Hypothesis Hmax : (prec < emax)%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT.FLT_exp emin prec.
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Arguments B754_finite {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_zero {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Notation bounded := (bounded prec emax).
Notation valid_binary := (valid_binary prec emax).
Notation B2R := (B2R prec emax).
Arguments B2FF {prec} {emax}.
Arguments FF2B {prec} {emax}.
Arguments is_finite {prec} {emax}.
Arguments is_finite_strict {prec} {emax}.
Arguments is_nan {prec} {emax}.
Notation Bsign := (Bsign prec emax).
Arguments Bopp {prec} {emax}.
Arguments binary_round {prec} {emax}.
Notation binary_round_correct := (binary_round_correct prec emax prec_gt_0_ Hmax).
Notation binary_overflow := (binary_overflow prec emax).

Definition Bnormfr_mantissa (x : binary_float prec emax) :=
  match x with
  | B754_finite _ mx ex _ =>
    if Z.eqb ex (-prec)%Z then Npos mx else 0%N
  | _ => 0%N
  end.

Definition Bldexp mode f e :=
  match f with
  | B754_finite sx mx ex _ =>
    FF2B _ (proj1 (binary_round_correct mode sx mx (ex+e)))
  | _ => f
  end.

(* TODO: move *)
Lemma mag_cond_Zopp :
  forall r s z, mag r (IZR (cond_Zopp s z)) = mag r (IZR z) :> Z.
Proof. now intros r s z; case s; simpl; [rewrite opp_IZR, mag_opp|]. Qed.

Theorem Bldexp_correct :
  forall m (f : binary_float prec emax) e,
  if Rlt_bool
       (Rabs (round radix2 fexp (round_mode m) (B2R f * bpow radix2 e)))
       (bpow radix2 emax) then
    (B2R (Bldexp m f e)
     = round radix2 fexp (round_mode m) (B2R f * bpow radix2 e))%R /\
    is_finite (Bldexp m f e) = is_finite f /\
    Bsign (Bldexp m f e) = Bsign f
  else
    B2FF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof.
intros m f e.
case f.
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intros s mf ef Hmef.
  case (Rlt_bool_spec _ _); intro Hover.
  + unfold Bldexp; rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
    simpl; unfold F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_true in Hr.
    * now destruct Hr as (Hr, (Hfr, Hsr)); rewrite Hr, Hfr, Hsr.
    * now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
  + unfold Bldexp; rewrite B2FF_FF2B; simpl.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_false in Hr; [exact Hr|].
    now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
Qed.

(** This hypothesis is needed to implement Bfrexp
    (otherwise, we have emin > - prec
     and Bfrexp cannot fit the mantissa in interval [0.5, 1)) *)
Hypothesis Hemax : (3 <= emax)%Z.

Definition Ffrexp_core_binary s m e :=
  if (Z.to_pos prec <=? digits2_pos m)%positive then
    (F754_finite s m (-prec), (e + prec)%Z)
  else
    let d := (prec - Z.pos (digits2_pos m))%Z in
    (F754_finite s (shift_pos (Z.to_pos d) m) (-prec), (e + prec - d)%Z).

Lemma Bfrexp_correct_aux :
  forall sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
  let z := fst (Ffrexp_core_binary sx mx ex) in
  let e := snd (Ffrexp_core_binary sx mx ex) in
  valid_binary z = true /\
  (/2 <= Rabs (FF2R radix2 z) < 1)%R /\
  (x = FF2R radix2 z * bpow radix2 e)%R.
Proof.
intros sx mx ex Bx.
set (x := F2R _).
set (z := fst _).
set (e := snd _); simpl.
assert (Dmx_le_prec : (Z.pos (digits2_pos mx) <= prec)%Z).
{ revert Bx; unfold bounded; rewrite Bool.andb_true_iff.
  unfold canonical_mantissa; rewrite <-Zeq_is_eq_bool; unfold FLT_exp.
  case (Z.max_spec (Z.pos (digits2_pos mx) + ex - prec) emin); lia. }
assert (Dmx_le_prec' : (digits2_pos mx <= Z.to_pos prec)%positive).
{ change (_ <= _)%positive
    with (Z.pos (digits2_pos mx) <= Z.pos (Z.to_pos prec))%Z.
  now rewrite Z2Pos.id; [|now apply prec_gt_0_]. }
unfold z, e, Ffrexp_core_binary.
case (Pos.leb_spec _ _); simpl; intro Dmx.
- unfold bounded, F2R; simpl.
  assert (Dmx' : digits2_pos mx = Z.to_pos prec).
  { now apply Pos.le_antisym. }
  assert (Dmx'' : Z.pos (digits2_pos mx) = prec).
  { now rewrite Dmx', Z2Pos.id; [|apply prec_gt_0_]. }
  split; [|split].
  + apply andb_true_intro.
    split; [|apply Zle_bool_true; lia].
    apply Zeq_bool_true; unfold FLT_exp.
    rewrite Dmx', Z2Pos.id; [|now apply prec_gt_0_].
    rewrite Z.max_l; [ring|lia].
  + rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
    rewrite <-abs_IZR, abs_cond_Zopp; simpl; split.
    * apply (Rmult_le_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_r.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <-Dmx'', Z.add_comm, Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      apply bpow_mag_le; apply IZR_neq; lia.
    * apply (Rmult_lt_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-Dmx'', Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      apply bpow_mag_gt; apply IZR_neq; lia.
  + unfold x, F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    now replace (_ + _)%Z with ex by ring.
- unfold bounded, F2R; simpl.
  assert (Dmx' : (Z.pos (digits2_pos mx) < prec)%Z).
  { now rewrite <-(Z2Pos.id prec); [|now apply prec_gt_0_]. }
  split; [|split].
  + unfold bounded; apply andb_true_intro.
    split; [|apply Zle_bool_true; lia].
    apply Zeq_bool_true; unfold FLT_exp.
    rewrite Zpos_digits2_pos, shift_pos_correct, Z.pow_pos_fold.
    rewrite Z2Pos.id; [|lia].
    rewrite Z.mul_comm; change 2%Z with (radix2 : Z).
    rewrite Zdigits_mult_Zpower; [|lia|lia].
    rewrite Zpos_digits2_pos; replace (_ - _)%Z with (- prec)%Z by ring.
    now rewrite Z.max_l; [|lia].
  + rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
    rewrite <-abs_IZR, abs_cond_Zopp; simpl.
    rewrite shift_pos_correct, mult_IZR.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos ((prec - Z.pos (digits2_pos mx)))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    set (d := Z.pos (digits2_pos mx)).
    replace (_ + _)%Z with (- d)%Z by ring; split.
    * apply (Rmult_le_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_le; apply IZR_neq; lia.
    * apply (Rmult_lt_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_gt; apply IZR_neq; lia.
  + rewrite Rmult_assoc, <-bpow_plus, shift_pos_correct.
    rewrite IZR_cond_Zopp, mult_IZR, cond_Ropp_mult_r, <-IZR_cond_Zopp.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos (prec - Z.pos (digits2_pos mx))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    now replace (_ + _)%Z with ex by ring; rewrite Rmult_comm.
Qed.

Definition Bfrexp f :=
  match f with
  | B754_finite s m e H =>
    let e' := snd (Ffrexp_core_binary s m e) in
    (FF2B _ (proj1 (Bfrexp_correct_aux s m e H)), e')
  | _ => (f, (-2*emax-prec)%Z)
  end.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let x := B2R f in
  let z := fst (Bfrexp f) in
  let e := snd (Bfrexp f) in
  (/2 <= Rabs (B2R z) < 1)%R /\
  (x = B2R z * bpow radix2 e)%R /\
  e = mag radix2 x.
Proof.
intro f; case f; intro s; try discriminate; intros m e Hf _.
generalize (Bfrexp_correct_aux s m e Hf).
intros (_, (Hb, Heq)); simpl; rewrite B2R_FF2B.
split; [now simpl|]; split; [now simpl|].
rewrite Heq, mag_mult_bpow.
- apply (Z.add_reg_l (- (snd (Ffrexp_core_binary s m e)))).
  now ring_simplify; symmetry; apply mag_unique.
- intro H; destruct Hb as (Hb, _); revert Hb; rewrite H, Rabs_R0; lra.
Qed.

Definition Bone := FF2B _ (proj1 (binary_round_correct mode_NE false 1 0)).

(* TODO: mettre ça ailleurs *)
Lemma mag_1 : mag radix2 1 = 1%Z :> Z.
Proof.
apply mag_unique_pos; rewrite bpow_1; simpl; lra.
Qed.

(* TODO: et ça aussi *)
Lemma negligible_exp_FLT :
  exists n, negligible_exp (FLT_exp emin prec) = Some n /\ (n <= emin)%Z.
Proof.
case (negligible_exp_spec (FLT_exp emin prec)).
{ intro H; exfalso; specialize (H emin); revert H.
  apply Zle_not_lt, Z.le_max_r. }
intros n Hn; exists n; split; [now simpl|].
destruct (Z.max_spec (n - prec) emin) as [(Hm, Hm')|(Hm, Hm')].
{ now revert Hn; unfold FLT_exp; rewrite Hm'. }
revert Hn prec_gt_0_; unfold FLT_exp, Prec_gt_0; rewrite Hm'; lia.
Qed.

Theorem Bone_correct : B2R Bone = 1%R.
Proof.
unfold Bone; simpl.
set (Hr := binary_round_correct _ _ _ _).
unfold Hr; rewrite B2R_FF2B.
destruct Hr as (Vz, Hr).
revert Hr.
fold emin; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
- unfold F2R; simpl; rewrite Rmult_1_r.
  rewrite Rlt_bool_true.
  + now intros (Hr, Hr'); rewrite Hr.
  + rewrite Rabs_pos_eq; [|lra].
    change 1%R with (bpow radix2 0); apply bpow_lt.
    unfold Prec_gt_0 in prec_gt_0_; lia.
- apply generic_format_F2R; intros _.
  unfold cexp, FLT_exp, F2R; simpl; rewrite Rmult_1_r, mag_1.
  unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Lemma is_finite_Bone : is_finite Bone = true.
Proof.
generalize Bone_correct; case Bone; simpl;
 try (intros; reflexivity); intros; exfalso; lra.
Qed.

Lemma Bsign_Bone : Bsign Bone = false.
Proof.
generalize Bone_correct; case Bone; simpl;
  try (intros; exfalso; lra); intros s' m e _.
case s'; [|now intro]; unfold F2R; simpl.
intro H; exfalso; revert H; apply Rlt_not_eq, (Rle_lt_trans _ 0); [|lra].
rewrite <-Ropp_0, <-(Ropp_involutive (_ * _)); apply Ropp_le_contravar.
rewrite Ropp_mult_distr_l; apply Rmult_le_pos; [|now apply bpow_ge_0].
unfold IZR; rewrite <-INR_IPR; generalize (INR_pos m); lra.
Qed.

Definition Bulp x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x))).

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof.
intro x; case x.
- intros s _; unfold Bulp.
  replace (fexp _) with emin.
  + generalize (Bldexp_correct mode_NE Bone emin).
    rewrite Bone_correct, Rmult_1_l, round_generic;
      [|now apply valid_rnd_N|apply generic_format_bpow; unfold fexp, FLT_exp;
        rewrite Z.max_r; unfold Prec_gt_0 in prec_gt_0_; lia].
    rewrite Rlt_bool_true.
    * intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
      split; [|now split; [apply is_finite_Bone|apply Bsign_Bone]].
      simpl; unfold ulp; rewrite Req_bool_true; [|reflexivity].
      destruct negligible_exp_FLT as (n, (Hn, Hn')).
      change fexp with (FLT_exp emin prec); rewrite Hn.
      now unfold FLT_exp; rewrite Z.max_r;
        [|unfold Prec_gt_0 in prec_gt_0_; lia].
    * rewrite Rabs_pos_eq; [|now apply bpow_ge_0]; apply bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + simpl; change (fexp _) with (fexp (-2 * emax - prec)).
    unfold fexp, FLT_exp; rewrite Z.max_r; [reflexivity|].
    unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- intro; discriminate.
- intros s pl Hpl; discriminate.
- intros s m e Hme _; unfold Bulp, ulp, cexp.
  set (f := B754_finite _ _ _ _).
  rewrite Req_bool_false.
  + destruct (Bfrexp_correct f (eq_refl _)) as (Hfr1, (Hfr2, Hfr3)).
    rewrite Hfr3.
    set (e' := fexp _).
    generalize (Bldexp_correct mode_NE Bone e').
    rewrite Bone_correct, Rmult_1_l, round_generic; [|now apply valid_rnd_N|].
    { rewrite Rlt_bool_true.
      - intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
        now split; [|split; [apply is_finite_Bone|apply Bsign_Bone]].
      - rewrite Rabs_pos_eq; [|now apply bpow_ge_0].
        unfold e', fexp, FLT_exp.
        case (Z.max_spec (mag radix2 (B2R f) - prec) emin)
          as [(_, Hm)|(_, Hm)]; rewrite Hm; apply bpow_lt;
          [now unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia|].
        apply (Zplus_lt_reg_r _ _ prec); ring_simplify.
        assert (mag radix2 (B2R f) <= emax)%Z;
          [|now unfold Prec_gt_0 in prec_gt_0_; lia].
        apply mag_le_bpow; [|now apply abs_B2R_lt_emax].
        now unfold f, B2R; apply F2R_neq_0; case s. }
    apply generic_format_bpow, Z.max_lub.
    * unfold Prec_gt_0 in prec_gt_0_; lia.
    * apply Z.le_max_r.
  + now unfold f, B2R; apply F2R_neq_0; case s.
Qed.

Definition Bpred_pos pred_pos_nan x :=
  match x with
  | B754_finite _ mx _ _ =>
    let d :=
      if (mx~0 =? shift_pos (Z.to_pos prec) 1)%positive then
        Bldexp mode_NE Bone (fexp (snd (Bfrexp x) - 1))
      else
        Bulp x in
    Bminus prec emax prec_gt_0_ Hmax (fun _ => pred_pos_nan) mode_NE x d
  | _ => x
  end.

(* TODO: move *)
Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof.
intros [sx|sx|sx plx Hx|sx mx ex Hx] ; simpl ; try discriminate.
intros; case sx; simpl.
- unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
- unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
Qed.

Theorem Bpred_pos_correct :
  forall pred_pos_nan x,
  (0 < B2R x)%R ->
  B2R (Bpred_pos pred_pos_nan x) = pred_pos radix2 fexp (B2R x) /\
  is_finite (Bpred_pos pred_pos_nan x) = true /\
  Bsign (Bpred_pos pred_pos_nan x) = false.
Proof.
intros pred_pos_nan x.
generalize (Bfrexp_correct x).
case x.
- simpl; intros s _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- simpl; intros s _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- simpl; intros s pl Hpl _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- intros sx mx ex Hmex Hfrexpx Px.
  assert (Hsx : sx = false).
  { revert Px; case sx; unfold B2R, F2R; simpl; [|now intro].
    intro Px; exfalso; revert Px; apply Rle_not_lt.
    rewrite <-(Rmult_0_l (bpow radix2 ex)).
    apply Rmult_le_compat_r; [apply bpow_ge_0|apply IZR_le; lia]. }
  clear Px; rewrite Hsx in Hfrexpx |- *; clear Hsx sx.
  specialize (Hfrexpx (eq_refl _)).
  simpl in Hfrexpx; rewrite B2R_FF2B in Hfrexpx.
  destruct Hfrexpx as (Hfrexpx_bounds, (Hfrexpx_eq, Hfrexpx_exp)).
  unfold Bpred_pos, Bfrexp.
  simpl (snd (_, snd _)).
  rewrite Hfrexpx_exp.
  set (x' := B754_finite _ _ _ _).
  set (xr := F2R _).
  assert (Nzxr : xr <> 0%R).
  { unfold xr, F2R; simpl.
    rewrite <-(Rmult_0_l (bpow radix2 ex)); intro H.
    apply Rmult_eq_reg_r in H; [|apply Rgt_not_eq, bpow_gt_0].
    apply eq_IZR in H; lia. }
  assert (Hulp := Bulp_correct x').
  specialize (Hulp (eq_refl _)).
  assert (Hldexp := Bldexp_correct mode_NE Bone (fexp (mag radix2 xr - 1))).
  rewrite Bone_correct, Rmult_1_l in Hldexp.
  assert (Fbpowxr : generic_format radix2 fexp
                      (bpow radix2 (fexp (mag radix2 xr - 1)))).
  { apply generic_format_bpow, Z.max_lub.
    - unfold Prec_gt_0 in prec_gt_0_; lia.
    - apply Z.le_max_r. }
  assert (H : Rlt_bool (Rabs
               (round radix2 fexp (round_mode mode_NE)
                  (bpow radix2 (fexp (mag radix2 xr - 1)))))
              (bpow radix2 emax) = true); [|rewrite H in Hldexp; clear H].
  { apply Rlt_bool_true; rewrite round_generic;
      [|apply valid_rnd_round_mode|apply Fbpowxr].
    rewrite Rabs_pos_eq; [|apply bpow_ge_0]; apply bpow_lt.
    apply Z.max_lub_lt; [|unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia].
    apply (Zplus_lt_reg_r _ _ (prec + 1)); ring_simplify.
    rewrite Z.add_1_r; apply Zle_lt_succ, mag_le_bpow.
    - exact Nzxr.
    - apply (Rlt_le_trans _ (bpow radix2 emax)).
      + change xr with (B2R x'); apply abs_B2R_lt_emax.
      + apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
  set (d := if (mx~0 =? _)%positive then _ else _).
  set (minus_nan := fun _ => _).
  assert (Hminus := Bminus_correct prec emax prec_gt_0_ Hmax minus_nan mode_NE
                                   x' d (eq_refl _)).
  assert (Fd : is_finite d = true).
  { unfold d; case (_ =? _)%positive.
    - now rewrite (proj1 (proj2 Hldexp)), is_finite_Bone.
    - now rewrite (proj1 (proj2 Hulp)). }
  specialize (Hminus Fd).
  assert (Px : (0 <= B2R x')%R).
  { unfold B2R, x', F2R; simpl.
    now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
  assert (Pd : (0 <= B2R d)%R).
  { unfold d; case (_ =? _)%positive.
    - rewrite (proj1 Hldexp).
      now rewrite round_generic; [apply bpow_ge_0|apply valid_rnd_N|].
    - rewrite (proj1 Hulp); apply ulp_ge_0. }
  assert (Hdlex : (B2R d <= B2R x')%R).
  { unfold d; case (_ =? _)%positive.
    - rewrite (proj1 Hldexp).
      rewrite round_generic; [|now apply valid_rnd_N|now simpl].
      apply (Rle_trans _ (bpow radix2 (mag radix2 xr - 1))).
      + apply bpow_le, Z.max_lub.
        * unfold Prec_gt_0 in prec_gt_0_; lia.
        * apply (Zplus_le_reg_r _ _ 1); ring_simplify.
          apply mag_ge_bpow.
          replace (_ - 1)%Z with emin by ring.
          now change xr with (B2R x'); apply abs_B2R_ge_emin.
      + rewrite <-(Rabs_pos_eq _ Px).
        now change xr with (B2R x'); apply bpow_mag_le.
    - rewrite (proj1 Hulp); apply ulp_le_id.
      + assert (B2R x' <> 0%R); [exact Nzxr|lra].
      + apply generic_format_B2R. }
  assert (H : Rlt_bool
            (Rabs
               (round radix2
                  (FLT_exp (3 - emax - prec) prec)
                  (round_mode mode_NE) (B2R x' - B2R d)))
            (bpow radix2 emax) = true); [|rewrite H in Hminus; clear H].
  { apply Rlt_bool_true.
    rewrite <-round_NE_abs; [|now apply FLT_exp_valid].
    rewrite Rabs_pos_eq; [|lra].
    apply (Rle_lt_trans _ (B2R x')).
    - apply round_le_generic;
        [now apply FLT_exp_valid|now apply valid_rnd_N| |lra].
      apply generic_format_B2R.
    - apply (Rle_lt_trans _ _ _ (Rle_abs _)), abs_B2R_lt_emax. }
  rewrite (proj1 Hminus).
  rewrite (proj1 (proj2 Hminus)).
  rewrite (proj2 (proj2 Hminus)).
  split; [|split; [reflexivity|now case (Rcompare_spec _ _); [lra| |]]].
  unfold pred_pos, d.
  case (Pos.eqb_spec _ _); intro Hd; case (Req_bool_spec _ _); intro Hpred.
  + rewrite (proj1 Hldexp).
    rewrite (round_generic _ _ _ _ Fbpowxr).
    change xr with (B2R x').
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    * now unfold pred_pos; rewrite Req_bool_true.
  + exfalso; apply Hpred.
    assert (Hmx : IZR (Z.pos mx) = bpow radix2 (prec - 1)).
    { apply (Rmult_eq_reg_l 2); [|lra]; rewrite <-mult_IZR.
      change (2 * Z.pos mx)%Z with (Z.pos mx~0); rewrite Hd.
      rewrite shift_pos_correct, Z.mul_1_r.
      change (IZR (Z.pow_pos _ _)) with (bpow radix2 (Z.pos (Z.to_pos prec))).
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      change 2%R with (bpow radix2 1); rewrite <-bpow_plus.
      f_equal; ring. }
    unfold x' at 1; unfold B2R at 1; unfold F2R; simpl.
    rewrite Hmx, <-bpow_plus; f_equal.
    apply (Z.add_reg_l 1); ring_simplify; symmetry; apply mag_unique_pos.
    unfold F2R; simpl; rewrite Hmx, <-bpow_plus; split.
    * right; f_equal; ring.
    * apply bpow_lt; lia.
  + rewrite (proj1 Hulp).
    assert (H : ulp radix2 fexp (B2R x')
                = bpow radix2 (fexp (mag radix2 (B2R x') - 1)));
      [|rewrite H; clear H].
    { unfold ulp; rewrite Req_bool_false; [|now simpl].
      unfold cexp; f_equal.
      assert (H : (mag radix2 (B2R x') <= emin + prec)%Z).
      { assert (Hcm : canonical_mantissa prec emax mx ex = true).
        { now generalize Hmex; unfold bounded; rewrite Bool.andb_true_iff. }
        apply (canonical_canonical_mantissa _ _ false) in Hcm.
        revert Hcm; fold emin; unfold canonical, cexp; simpl.
        change (F2R _) with (B2R x'); intro Hex.
        apply Z.nlt_ge; intro H'; apply Hd.
        apply Pos2Z.inj_pos; rewrite shift_pos_correct, Z.mul_1_r.
        apply eq_IZR; change (IZR (Z.pow_pos _ _))
          with (bpow radix2 (Z.pos (Z.to_pos prec))).
        rewrite Z2Pos.id; [|exact prec_gt_0_].
        change (Z.pos mx~0) with (2 * Z.pos mx)%Z.
        rewrite Z.mul_comm, mult_IZR.
        apply (Rmult_eq_reg_r (bpow radix2 (ex - 1)));
          [|apply Rgt_not_eq, bpow_gt_0].
        change 2%R with (bpow radix2 1); rewrite Rmult_assoc, <-!bpow_plus.
        replace (1 + _)%Z with ex by ring.
        unfold B2R at 1, F2R in Hpred; simpl in Hpred; rewrite Hpred.
        change (F2R _) with (B2R x'); rewrite Hex.
        unfold FLT_exp; rewrite Z.max_l; [f_equal; ring|lia]. }
      now unfold fexp, FLT_exp; do 2 (rewrite Z.max_r; [|lia]). }
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid| |change xr with (B2R x') in Nzxr; lra].
      apply generic_format_B2R.
    * now unfold pred_pos; rewrite Req_bool_true.
  + rewrite (proj1 Hulp).
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    * now unfold pred_pos; rewrite Req_bool_false.
Qed.

Lemma Bmax_float_proof :
  valid_binary
    (F754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof.
unfold valid_binary, bounded; apply andb_true_intro; split.
- unfold canonical_mantissa; apply Zeq_bool_true.
  set (p := Z.pos (digits2_pos _)).
  assert (H : p = prec).
  { unfold p; rewrite Zpos_digits2_pos, Pos2Z.inj_sub.
    - rewrite shift_pos_correct, Z.mul_1_r.
      assert (P2pm1 : (0 <= 2 ^ prec - 1)%Z).
      { apply (Zplus_le_reg_r _ _ 1); ring_simplify.
        change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
        apply Zpower_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
      apply Zdigits_unique;
        rewrite Z.pow_pos_fold, Z2Pos.id; [|exact prec_gt_0_]; simpl; split.
      + rewrite (Z.abs_eq _ P2pm1).
        replace prec with (prec - 1 + 1)%Z at 2 by ring.
        rewrite Zpower_plus; [| unfold Prec_gt_0 in prec_gt_0_; lia|lia].
        simpl; unfold Z.pow_pos; simpl.
        assert (1 <= 2 ^ (prec - 1))%Z; [|lia].
        change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
        apply Zpower_le; simpl; unfold Prec_gt_0 in prec_gt_0_; lia.
      + now rewrite Z.abs_eq; [lia|].
    - change (_ < _)%positive
        with (Z.pos 1 < Z.pos (shift_pos (Z.to_pos prec) 1))%Z.
      rewrite shift_pos_correct, Z.mul_1_r, Z.pow_pos_fold.
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
      apply Zpower_lt; unfold Prec_gt_0 in prec_gt_0_; lia. }
  unfold FLT_exp; rewrite H, Z.max_l; [ring|].
  unfold Prec_gt_0 in prec_gt_0_; lia.
- apply Zle_bool_true; unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Definition Bmax_float := FF2B _ Bmax_float_proof.

Definition Bsucc succ_nan x :=
  match x with
  | B754_zero _ => Bldexp mode_NE Bone emin
  | B754_infinity false => x
  | B754_infinity true => Bopp succ_nan Bmax_float
  | B754_nan _ _ _ => build_nan prec emax (succ_nan x)
  | B754_finite false _ _ _ =>
    Bplus prec emax prec_gt_0_ Hmax (fun _ => succ_nan) mode_NE x (Bulp x)
  | B754_finite true _ _ _ =>
    Bopp succ_nan (Bpred_pos succ_nan (Bopp succ_nan x))
  end.

(* TODO: move *)
Lemma Bsign_Bopp :
  forall opp_nan x, is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof. now intros opp_nan [s|s|s pl H|s m e H]. Qed.

Lemma Bsucc_correct :
  forall succ_nan x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc succ_nan x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc succ_nan x) = true /\
    (Bsign (Bsucc succ_nan x) = Bsign x && is_finite_strict x)%bool
  else
    B2FF (Bsucc succ_nan x) = F754_infinity false.
Proof.
assert (Hsucc : succ radix2 fexp 0 = bpow radix2 emin).
{ unfold succ; rewrite Rle_bool_true; [|now right]; rewrite Rplus_0_l.
  unfold ulp; rewrite Req_bool_true; [|now simpl].
  destruct negligible_exp_FLT as (n, (Hne, Hn)).
  now unfold fexp; rewrite Hne; unfold FLT_exp; rewrite Z.max_r;
    [|unfold Prec_gt_0 in prec_gt_0_; lia]. }
intros succ_nan [s|s|s pl Hpl|sx mx ex Hmex]; try discriminate; intros _.
- generalize (Bldexp_correct mode_NE Bone emin); unfold Bsucc; simpl.
  assert (Hbemin : round radix2 fexp ZnearestE (bpow radix2 emin)
                   = bpow radix2 emin).
  { rewrite round_generic; [reflexivity|apply valid_rnd_N|].
    apply generic_format_bpow.
    unfold fexp, FLT_exp; rewrite Z.max_r; [now simpl|].
    unfold Prec_gt_0 in prec_gt_0_; lia. }
  rewrite Hsucc, Rlt_bool_true.
  + intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
    rewrite Bone_correct, Rmult_1_l, is_finite_Bone, Bsign_Bone.
    case Rlt_bool_spec; intro Hover.
    * now rewrite Bool.andb_false_r.
    * exfalso; revert Hover; apply Rlt_not_le, bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + rewrite Bone_correct, Rmult_1_l, Hbemin, Rabs_pos_eq; [|apply bpow_ge_0].
    apply bpow_lt; unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- unfold Bsucc; case sx.
  + case Rlt_bool_spec; intro Hover.
    * rewrite B2R_Bopp; simpl (Bopp _ (B754_finite _ _ _ _)).
      rewrite is_finite_Bopp.
      set (ox := B754_finite false mx ex Hmex).
      assert (Hpred := Bpred_pos_correct succ_nan ox).
      assert (Hox : (0 < B2R ox)%R); [|specialize (Hpred Hox); clear Hox].
      { now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0]. }
      rewrite (proj1 Hpred), (proj1 (proj2 Hpred)).
      unfold succ; rewrite Rle_bool_false; [split; [|split]|].
      { now unfold B2R, F2R, ox; simpl; rewrite Ropp_mult_distr_l, <-opp_IZR. }
      { now simpl. }
      { simpl (Bsign (B754_finite _ _ _ _)); simpl (true && _)%bool.
        rewrite Bsign_Bopp, (proj2 (proj2 Hpred)); [now simpl|].
        now destruct Hpred as (_, (H, _)); revert H; case (Bpred_pos _ _). }
      unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
      rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_lt_contravar.
      now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0].
    * exfalso; revert Hover; apply Rlt_not_le.
      apply (Rle_lt_trans _ (succ radix2 fexp 0)).
      { apply succ_le; [now apply FLT_exp_valid|apply generic_format_B2R|
                        apply generic_format_0|].
        unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
        rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_le_contravar.
        now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
      rewrite Hsucc; apply bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + set (x := B754_finite _ _ _ _).
    set (plus_nan := fun _ => succ_nan).
    assert (Hulp := Bulp_correct x (eq_refl _)).
    assert (Hplus := Bplus_correct prec emax prec_gt_0_ Hmax plus_nan mode_NE
                                   x (Bulp x) (eq_refl _)).
    rewrite (proj1 (proj2 Hulp)) in Hplus; specialize (Hplus (eq_refl _)).
    assert (Px : (0 <= B2R x)%R).
    { now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
    assert (Hsucc' : (succ radix2 fexp (B2R x)
                      = B2R x + ulp radix2 fexp (B2R x))%R).
    { now unfold succ; rewrite (Rle_bool_true _ _ Px). }
    rewrite (proj1 Hulp), <- Hsucc' in Hplus.
    rewrite round_generic in Hplus;
      [|apply valid_rnd_N| now apply generic_format_succ;
                           [apply FLT_exp_valid|apply generic_format_B2R]].
    rewrite Rabs_pos_eq in Hplus; [|apply (Rle_trans _ _ _ Px), succ_ge_id].
    revert Hplus; case Rlt_bool_spec; intros Hover Hplus.
    * split; [now simpl|split; [now simpl|]].
      rewrite (proj2 (proj2 Hplus)); case Rcompare_spec.
      { intro H; exfalso; revert H.
        apply Rle_not_lt, (Rle_trans _ _ _ Px), succ_ge_id. }
      { intro H; exfalso; revert H; apply Rgt_not_eq, Rlt_gt.
        apply (Rlt_le_trans _ (B2R x)); [|apply succ_ge_id].
        now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0]. }
      now simpl.
    * now rewrite (proj1 Hplus).
Qed.

Definition Bpred pred_nan x :=
  Bopp pred_nan (Bsucc pred_nan (Bopp pred_nan x)).

(* TODO: move *)
Lemma Rcompare_Ropp x y : Rcompare (- x) (- y) = Rcompare y x.
Proof.
destruct (Rcompare_spec y x);
  destruct (Rcompare_spec (- x) (- y));
  try reflexivity; exfalso; lra.
Qed.

(* TODO: move (ou supprimer, plus nécessaire dans master) *)
Lemma is_finite_strict_build_nan :
  forall n, is_finite_strict (build_nan prec emax n) = false.
Proof. now intros (n, Hn); revert Hn; case n. Qed.
  
(* TODO: move *)
Lemma Rlt_bool_Ropp x y : Rlt_bool (- x) (- y) = Rlt_bool y x.
Proof. now unfold Rlt_bool; rewrite Rcompare_Ropp. Qed.

Lemma Bpred_correct :
  forall pred_nan x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred pred_nan x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred pred_nan x) = true /\
    (Bsign (Bpred pred_nan x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2FF (Bpred pred_nan x) = F754_infinity true.
Proof.
intros pred_nan x Fx.
assert (Fox : is_finite (Bopp pred_nan x) = true).
{ now rewrite is_finite_Bopp. }
rewrite <-(Ropp_involutive (B2R x)), <-(B2R_Bopp _ _ pred_nan).
rewrite pred_opp, Rlt_bool_Ropp.
generalize (Bsucc_correct pred_nan _ Fox).
case (Rlt_bool _ _).
- intros (HR, (HF, HS)); unfold Bpred.
  rewrite B2R_Bopp, HR, is_finite_Bopp.
  rewrite <-(Bool.negb_involutive (Bsign x)), <-Bool.negb_andb.
  split; [reflexivity|split; [exact HF|]].
  replace (is_finite_strict x) with (is_finite_strict (Bopp pred_nan x));
    [|now case x; try easy; intros s pl Hpl; simpl;
        rewrite is_finite_strict_build_nan].
  rewrite Bsign_Bopp, <-(Bsign_Bopp pred_nan x), HS.
  + now simpl.
  + now revert Fx; case x.
  + now revert HF; case (Bsucc _ _).
- now unfold Bpred; case (Bsucc _ _); intro s; case s.
Qed.

(* TODO: spec *)
(*
  Definition EFclassify f :=
    match f with
    | E754_nan => NaN
    | E754_infinity false => PInf
    | E754_infinity true => NInf
    | E754_zero false => NZero
    | E754_zero true => PZero
    | E754_finite false m _ =>
      if (digits2_pos m =? Z.to_pos prec)%positive then PNormal
      else PSubn
    | E754_finite true m _ =>
      if (digits2_pos m =? Z.to_pos prec)%positive then NNormal
      else NSubn
    end.
*)

End Bsucc_pred.

Section Other_complements.

Lemma error_le_ulp_round :
  forall (beta : radix) (fexp : Z -> Z),
  Valid_exp fexp ->
  Monotone_exp fexp ->
  forall rnd : R -> Z, Valid_rnd rnd ->
  forall x : R,
  (Rabs (round beta fexp rnd x - x) <= ulp beta fexp (round beta fexp rnd x))%R.
Proof.
intros beta fexp Vexp Mexp rnd Vrnd x.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, round_0; [|exact Vrnd].
  unfold Rminus; rewrite Ropp_0, Rplus_0_l, Rabs_R0; apply ulp_ge_0. }
now apply Rlt_le, error_lt_ulp_round.
Qed.

(** Adding [ulp] is a, somewhat reasonable, overapproximation of [succ]. *)
Lemma succ_le_plus_ulp beta fexp (Mexp : Monotone_exp fexp) x :
  (succ beta fexp x <= x + ulp beta fexp x)%R.
Proof.
destruct (Rle_or_lt 0 x) as [Px|Nx]; [now right; apply succ_eq_pos|].
replace (_ + _)%R with (- (-x - ulp beta fexp x))%R by ring.
unfold succ; rewrite (Rle_bool_false _ _ Nx), <-ulp_opp.
apply Ropp_le_contravar; unfold pred_pos.
destruct (Req_dec (-x) (bpow beta (mag beta (-x) - 1))) as [Hx|Hx].
{ rewrite (Req_bool_true _ _ Hx).
   apply (Rplus_le_reg_r x); ring_simplify; apply Ropp_le_contravar.
   unfold ulp; rewrite Req_bool_false; [|lra].
   apply bpow_le, Mexp; lia. }
 now rewrite (Req_bool_false _ _ Hx); right.
Qed.

(** And it also lies in the format. *)
Lemma generic_format_plus_ulp
      beta fexp (Vexp : Valid_exp fexp) (Mexp : Monotone_exp fexp) x :
  generic_format beta fexp x ->
  generic_format beta fexp (x + ulp beta fexp x).
Proof.
intro Fx.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{ now rewrite <-(succ_eq_pos _ _ _ Px); apply generic_format_succ. }
apply generic_format_opp in Fx.
replace (_ + _)%R with (- (-x - ulp beta fexp x))%R by ring.
apply generic_format_opp; rewrite <-ulp_opp.
destruct (Req_dec (-x) (bpow beta (mag beta (-x) - 1))) as [Hx|Hx].
{ unfold ulp; rewrite Req_bool_false; [|lra].
  rewrite Hx at 1.
  unfold cexp.
  set (e := mag _ _).
  assert (Hfe : (fexp e < e)%Z).
  { now apply mag_generic_gt; [|lra|]. }
  replace (e - 1)%Z with (e - 1 - fexp e + fexp e)%Z by ring.
  rewrite bpow_plus.
  set (m := bpow _ (_ - _)).
  replace (_ - _)%R with ((m - 1) * bpow beta (fexp e))%R; [|unfold m; ring].
  case_eq (e - 1 - fexp e)%Z.
  { intro He; unfold m; rewrite He; simpl; ring_simplify (1 - 1)%R.
    rewrite Rmult_0_l; apply generic_format_0. }
  { intros p Hp; unfold m; rewrite Hp; simpl.
    pose (f := {| Defs.Fnum := (Z.pow_pos beta p - 1)%Z;
                  Defs.Fexp := fexp e |} : Defs.float beta).
    apply (generic_format_F2R' _ _ _ f); [|intro Hm'; unfold f; simpl].
    { now unfold Defs.F2R; simpl; rewrite minus_IZR. }
    unfold cexp.
    replace (IZR _) with (bpow beta (Z.pos p)); [|now simpl].
    rewrite <-Hp.
    assert (He : (1 <= e - 1 - fexp e)%Z); [lia|].
    set (e' := mag _ (_ * _)).
    assert (H : (e' = e - 1 :> Z)%Z); [|rewrite H; apply Mexp; lia].
    unfold e'; apply mag_unique.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|apply bpow_ge_0].
    rewrite Rabs_pos_eq;
      [|apply (Rplus_le_reg_r 1); ring_simplify;
        change 1%R with (bpow beta 0); apply bpow_le; lia].
    assert (beta_pos : (0 < IZR beta)%R).
    { apply (Rlt_le_trans _ 2); [lra|].
      apply IZR_le, Z.leb_le, radix_prop. }
    split.
    { replace (e - 1 - 1)%Z with (e - 1 - fexp e + -1  + fexp e)%Z by ring.
      rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0|].
      rewrite bpow_plus; simpl; unfold Z.pow_pos; simpl.
      rewrite Zmult_1_r.
      apply (Rmult_le_reg_r _ _ _ beta_pos).
      rewrite Rmult_assoc, Rinv_l; [|lra]; rewrite Rmult_1_r.
      apply (Rplus_le_reg_r (IZR beta)); ring_simplify.
      apply (Rle_trans _ (2 * bpow beta (e - 1 - fexp e))).
      { change 2%R with (1 + 1)%R; rewrite Rmult_plus_distr_r, Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <-bpow_1; apply bpow_le; lia. }
      rewrite Rmult_comm; apply Rmult_le_compat_l; [apply bpow_ge_0|].
      apply IZR_le, Z.leb_le, radix_prop. }
    apply (Rmult_lt_reg_r (bpow beta (- fexp e))); [apply bpow_gt_0|].
    rewrite Rmult_assoc, <-!bpow_plus.
    replace (fexp e + - fexp e)%Z with 0%Z by ring; simpl.
    rewrite Rmult_1_r; unfold Zminus; lra. }
  intros p Hp; exfalso; lia. }
replace (_ - _)%R with (pred_pos beta fexp (-x)).
{ now apply generic_format_pred_pos; [| |lra]. }
now unfold pred_pos; rewrite Req_bool_false.
Qed.

Lemma succ_round_ge_id beta fexp (Vexp : Valid_exp fexp)
      rnd (Vrnd : Valid_rnd rnd) x :
  (x <= succ beta fexp (round beta fexp rnd x))%R.
Proof.
apply (Rle_trans _ (round beta fexp Raux.Zceil x)).
{ now apply round_UP_pt. }
destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
{ now apply UP_le_succ_DN. }
apply succ_ge_id.
Qed.

Variable emin prec : Z.
Hypothesis prec_gt_0_ : Prec_gt_0 prec.

Lemma plus_ulp_rnd_ge x :
  let rx := round radix2 (FLT_exp emin prec) ZnearestE x in
  (x <= round radix2 (FLT_exp emin prec) ZnearestE
              (rx + ulp radix2 (FLT_exp emin prec) rx))%R.
Proof.
simpl.
set (rx := round _ _ _ x).
assert (Vexp : Valid_exp (FLT_exp emin prec)); [now apply FLT_exp_valid|].
assert (Vrnd : Valid_rnd ZnearestE); [now apply valid_rnd_N|].
apply (Rle_trans _ (succ radix2 (FLT_exp emin prec) rx)).
{ now apply succ_round_ge_id. }
rewrite round_generic; [|now simpl|].
{ apply succ_le_plus_ulp, FLT_exp_monotone. }
now apply generic_format_plus_ulp;
  [|apply FLT_exp_monotone|apply generic_format_round].
Qed.

End Other_complements.
