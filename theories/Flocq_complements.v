Require Import ZArith.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.Digits.
Require Import Flocq.Core.Ulp.
Require Import Flocq.IEEE754.Binary.

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

Definition Fsucc_pos_core_binary m e :=
  let m' := (m + 1)%positive in
  if (digits2_pos m' <=? Z.to_pos prec)%positive then
    F754_finite false m' e
  else if (e <? emax - prec)%Z then
    F754_finite false (shift_pos (Z.to_pos (prec - 1)) 1) (e + 1)
  else
    F754_infinity false.

Definition Bsucc_pos_correct_aux :
  forall mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z := Fsucc_pos_core_binary mx ex in
  valid_binary z = true /\
  if Rlt_bool (succ radix2 fexp x) (bpow radix2 emax) then
    FF2R radix2 z = succ radix2 fexp x /\
    is_finite_FF z = true /\ sign_FF z = false
  else
    z = F754_infinity false.
Proof.
Admitted.

Lemma smallest_positive_subnormal_proof :
  valid_binary (F754_finite false 1 emin) = true.
Proof.
Admitted.

Definition smallest_positive_subnormal :=
  FF2B prec emax _ smallest_positive_subnormal_proof.

Definition Bsucc_pos succ_pos_nan x :=
  match x with
  | B754_nan _ _ _ _ _ => build_nan prec emax (succ_pos_nan x)
  | B754_infinity _ _ _ => x
  | B754_zero _ _ _ => smallest_positive_subnormal
  | B754_finite _ _ _ mx ex Hx =>
    FF2B prec emax _ (proj1 (Bsucc_pos_correct_aux mx ex Hx))
  end.

Lemma Bsucc_pos_correct :
  forall succ_pos_nan x,
  is_finite x = true ->
  (0 <= B2R x)%R ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc_pos succ_pos_nan x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc_pos succ_pos_nan x) = true /\
    Bsign (Bsucc_pos succ_pos_nan x) = false
  else
    B2FF (Bsucc_pos succ_pos_nan x) = F754_infinity false.
Proof.
Admitted.

Definition Fpred_pos_core_binary m e :=
  match m with
  | 1%positive => F754_zero false
  | _ =>
    let m' := (m - 1)%positive in
    if ((Z.to_pos prec <=? digits2_pos m')%positive
        || (e <=? emin)%Z)%bool then
      F754_finite false m' e
    else
      F754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (e - 1)
  end.

Definition Bpred_pos_correct_aux :
  forall mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z := Fpred_pos_core_binary mx ex in
  valid_binary z = true /\
  FF2R radix2 z = pred radix2 fexp x /\
  is_finite_FF z = true /\ sign_FF z = false.
Proof.
Admitted.

Lemma largest_normal_proof :
  valid_binary
    (F754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof.
Admitted.

Definition largest_normal :=
  FF2B prec emax _ largest_normal_proof.

Definition Bpred_pos pred_pos_nan x :=
  match x with
  | B754_nan _ _ _ _ _ => build_nan prec emax (pred_pos_nan x)
  | B754_infinity _ _ _ => largest_normal
  | B754_zero _ _ _ => Bopp pred_pos_nan smallest_positive_subnormal
  | B754_finite _ _ _ mx ex Hx =>
    FF2B prec emax _ (proj1 (Bpred_pos_correct_aux mx ex Hx))
  end.

Lemma Bpred_pos_correct :
  forall pred_pos_nan x,
  is_finite x = true ->
  (0 <= B2R x)%R ->
  B2R (Bpred_pos pred_pos_nan x) = pred radix2 fexp (B2R x) /\
  is_finite (Bpred_pos pred_pos_nan x) = true /\
  Bsign (Bpred_pos pred_pos_nan x) = false.
Proof.
Admitted.

Definition Bsucc succ_nan x :=
  match x with
  | B754_nan _ _ _ _ _ => build_nan prec emax (succ_nan x)
  | B754_infinity _ _ false => Bsucc_pos succ_nan x
  | B754_infinity _ _ true =>
    Bopp succ_nan (Bpred_pos succ_nan (Bopp succ_nan x))
  | B754_zero _ _ _ => Bsucc_pos succ_nan x
  | B754_finite _ _ false _ _ _ => Bsucc_pos succ_nan x
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

Require Import Psatz.

Lemma Rcompare_Ropp x y : Rcompare (- x) (- y) = Rcompare y x.
Proof.
destruct (Rcompare_spec y x);
  destruct (Rcompare_spec (- x) (- y));
  try reflexivity; exfalso; lra.
Qed.

Lemma Rlt_bool_Ropp x y : Rlt_bool (- x) (- y) = Rlt_bool y x.
Proof. now unfold Rlt_bool; rewrite Rcompare_Ropp. Qed.

Lemma Bsign_Bopp opp_nan x :
  is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof.
unfold Bsign, Bopp.
now case x; intro s; case s; try reflexivity; intros pl Hpl.
Qed.

Lemma is_finite_strict_Bopp opp_nan x :
  is_finite_strict (Bopp opp_nan x) = is_finite_strict x.
Proof. now unfold is_finite_strict, Bopp; case x. Qed.

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
  rewrite is_finite_strict_Bopp in HS.
  rewrite Bsign_Bopp, <-(Bsign_Bopp pred_nan x), HF, HS.
  + now simpl.
  + now revert Fx; case x.
  + now revert HF; case (Bsucc _ _).
- now unfold Bpred; case (Bsucc _ _); intro s; case s.
Qed.

End Bsucc_pred.
