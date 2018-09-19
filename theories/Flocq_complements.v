Require Import ZArith.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.Digits.
Require Import Flocq.Core.Ulp.
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

Notation bounded := (bounded prec emax).
Notation valid_binary := (valid_binary prec emax).
Notation B2R := (B2R prec emax).
Notation B2FF := (B2FF prec emax).
Notation is_finite := (is_finite prec emax).
Notation is_finite_strict := (is_finite_strict prec emax).
Notation is_nan := (is_nan prec emax).
Notation Bsign := (Bsign prec emax).
Notation Bopp := (Bopp prec emax).
Notation binary_round := (binary_round prec emax).
Notation FF2B := (FF2B prec emax).
Notation binary_round_correct :=
  (binary_round_correct prec emax prec_gt_0_ Hmax).
Notation binary_overflow := (binary_overflow prec emax).

Definition Bnormfr_mantissa (x : binary_float prec emax) :=
  match x with
  | B754_finite _ _ _ mx ex _ =>
    if Z.eqb ex (-prec)%Z then Npos mx else 0%N
  | _ => 0%N
  end.

Definition Bldexp mode f e :=
  match f with
  | B754_finite _ _ sx mx ex _ =>
    FF2B _ (proj1 (binary_round_correct mode sx mx (ex+e)))
  | _ => f
  end.

Theorem Bldexp_correct :
  forall m f e,
  if Rlt_bool (Rabs (B2R f * bpow radix2 e)) (bpow radix2 emax) then
    (B2R (Bldexp m f e) = B2R f * bpow radix2 e)%R /\
    is_finite (Bldexp m f e) = is_finite f /\
    Bsign (Bldexp m f e) = Bsign f
  else
    B2FF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof.
Admitted.

Definition Ffrexp_core_binary s m e :=
  if (digits2_pos m =? Z.to_pos prec)%positive then
    (F754_finite s m (-prec)%Z, (e + prec)%Z)
  else
    let d := (prec - Z.pos (digits2_pos m))%Z in
    (F754_finite s (shift_pos (Z.to_pos d) m) (-prec)%Z, (e + prec - d)%Z).

Lemma Bfrexp_correct_aux :
  forall sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
  let z := fst (Ffrexp_core_binary sx mx ex) in
  let e := snd (Ffrexp_core_binary sx mx ex) in
  valid_binary z = true /\
  (/2 <= Rabs (FF2R radix2 z) < 1)%R /\
  (x = FF2R radix2 z * bpow radix2 e)%R.
Proof.
Admitted.

Definition Bfrexp f :=
  match f with
  | B754_finite _ _ s m e H =>
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
    rewrite Bone_correct, Rmult_1_l, Rlt_bool_true.
    * intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
      split; [|now split; [apply is_finite_Bone|apply Bsign_Bone]].
      simpl; unfold ulp; rewrite Req_bool_true; [|reflexivity].
      destruct negligible_exp_FLT as (n, (Hn, Hn')).
      change fexp with (FLT_exp emin prec); rewrite Hn.
      unfold FLT_exp; rewrite Z.max_r; [reflexivity|].
      unfold Prec_gt_0 in prec_gt_0_; lia.
    * rewrite Rabs_pos_eq; [|now apply bpow_ge_0]; apply bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + simpl; change (fexp _) with (fexp (-2 * emax - prec)).
    unfold fexp, FLT_exp; rewrite Z.max_r; [reflexivity|].
    unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- intro; discriminate.
- intros s pl Hpl; discriminate.
- intros s m e Hme _; unfold Bulp, ulp, cexp.
  set (f := B754_finite _ _ _ _ _ _).
  rewrite Req_bool_false.
  + destruct (Bfrexp_correct f (eq_refl _)) as (Hfr1, (Hfr2, Hfr3)).
    rewrite Hfr3.
    set (e' := fexp _).
    generalize (Bldexp_correct mode_NE Bone e').
    rewrite Bone_correct, Rmult_1_l, Rlt_bool_true.
    * intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
      now split; [|split; [apply is_finite_Bone|apply Bsign_Bone]].
    * rewrite Rabs_pos_eq; [|now apply bpow_ge_0].
      unfold e', fexp, FLT_exp.
      case (Z.max_spec (mag radix2 (B2R f) - prec) emin) as [(_, Hm)|(_, Hm)];
        rewrite Hm; apply bpow_lt;
        [now unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia|].
      apply (Zplus_lt_reg_r _ _ prec); ring_simplify.
      assert (mag radix2 (B2R f) <= emax)%Z;
        [|now unfold Prec_gt_0 in prec_gt_0_; lia].
      apply mag_le_bpow; [|now apply abs_B2R_lt_emax].
      now unfold f, B2R; apply F2R_neq_0; case s.
  + now unfold f, B2R; apply F2R_neq_0; case s.
Qed.

Definition Bpred_pos pred_pos_nan x :=
  match x with
  | B754_finite _ _ _ mx _ _ =>
    let d :=
      if (mx~0 =? shift_pos (Z.to_pos prec) 1)%positive then
        Bldexp mode_NE Bone (fexp (snd (Bfrexp x) - 1))
      else
        Bulp x in
    Bminus prec emax prec_gt_0_ Hmax (fun _ => pred_pos_nan) mode_NE x d
  | _ => x
  end.

Theorem Bpred_pos_correct :
  forall pred_pos_nan x,
  (0 < B2R x)%R ->
  B2R (Bpred_pos pred_pos_nan x) = pred_pos radix2 fexp (B2R x) /\
  is_finite (Bpred_pos pred_pos_nan x) = true /\
  Bsign (Bpred_pos pred_pos_nan x) = false.
Proof.
Admitted.

Lemma largest_normal_proof :
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

Definition largest_normal := FF2B _ largest_normal_proof.

Lemma smallest_positive_subnormal_proof :
  valid_binary (F754_finite false 1 emin) = true.
Proof.
unfold valid_binary, bounded; apply andb_true_intro; split.
- unfold canonical_mantissa; apply Zeq_bool_true.
  unfold digits2_pos, FLT_exp, emin; rewrite Z.max_r; [reflexivity|].
  unfold Prec_gt_0 in prec_gt_0_; lia.
- apply Zle_bool_true; unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Definition smallest_positive_subnormal :=
  FF2B _ smallest_positive_subnormal_proof.

Definition Bsucc succ_nan x :=
  match x with
  | B754_zero _ _ _ => smallest_positive_subnormal
  | B754_infinity _ _ false => x
  | B754_infinity _ _ true => largest_normal
  | B754_nan _ _ _ _ _ => build_nan prec emax (succ_nan x)
  | B754_finite _ _ false _ _ _ =>
    Bplus prec emax prec_gt_0_ Hmax (fun _ => succ_nan) mode_NE x (Bulp x)
  | B754_finite _ _ true _ _ _ =>
    Bopp succ_nan (Bpred_pos succ_nan (Bopp succ_nan x))
  end.

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
Admitted.

Definition Bpred pred_nan x :=
  Bopp pred_nan (Bsucc pred_nan (Bopp pred_nan x)).

(* TODO: move *)
Lemma Rcompare_Ropp x y : Rcompare (- x) (- y) = Rcompare y x.
Proof.
destruct (Rcompare_spec y x);
  destruct (Rcompare_spec (- x) (- y));
  try reflexivity; exfalso; lra.
Qed.

(* TODO: move *)
Lemma Rlt_bool_Ropp x y : Rlt_bool (- x) (- y) = Rlt_bool y x.
Proof. now unfold Rlt_bool; rewrite Rcompare_Ropp. Qed.

Lemma Bsign_Bopp opp_nan x :
  is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof.
now unfold Bsign, Bopp; case x; intro s; case s; try reflexivity; intros.
Qed.

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
  replace (is_finite_strict x) with (is_finite_strict (Bopp pred_nan x));
    [|now case x].
  rewrite Bsign_Bopp, <-(Bsign_Bopp pred_nan x), HF, HS.
  + now simpl.
  + now revert Fx; case x.
  + now revert HF; case (Bsucc _ _).
- now unfold Bpred; case (Bsucc _ _); intro s; case s.
Qed.

(*
Lemma digits2_pos_succ p :
  digits2_pos (p + 1) = digits2_pos p
  \/ digits2_pos (p + 1) = (digits2_pos p + 1)%positive.
Proof.
elim p; [intros p' Hp'|intros p' Hp'|]; simpl.
- rewrite Pos.add_1_r in Hp'.
  destruct Hp' as [Hp'|Hp']; rewrite Hp'; [now left|right].
  now rewrite Pos.add_succ_l.
- now left.
- now right.
Qed.

Lemma digits2_pos_shift_pos p p' :
  digits2_pos (shift_pos p p') = (p + digits2_pos p')%positive.
Proof.
Opaque Pos.add.
revert p'; elim p; [intros p'' Hp''|intros p'' Hp''|]; intro p'.
- simpl; rewrite !Hp''; lia.
- simpl; rewrite !Hp''; lia.
- simpl; lia.
Transparent Pos.add.
Qed.
*)

End Bsucc_pred.
