(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Flocq Require Import Raux.
Require Import ZArith.
Require Import Psatz.
Require Import Bool.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_specific_sig.

Module StdZRadix2 <: FloatCarrier.

Definition radix := radix2.
Definition radix_correct := refl_equal Lt.
Definition smantissa_type := Z.
Definition mantissa_type := positive.
Definition exponent_type := Z.

Definition MtoP := fun (m : positive) => m.
Definition PtoM := fun (m : positive) => m.
Definition MtoZ := fun (m : Z) => m.
Definition ZtoM := fun (m : Z) => m.
Definition EtoZ := fun (e : Z) => e.
Definition ZtoE := fun (e : Z) => e.

Definition exponent_zero := Z0.
Definition exponent_one := Zpos xH.
Definition exponent_neg := Zopp.
Definition exponent_add := Zplus.
Definition exponent_sub := Zminus.
Definition exponent_cmp := Zcompare.
Definition mantissa_zero := Z0.
Definition mantissa_one := xH.
Definition mantissa_add := Pplus.
Definition mantissa_sub := Pminus.
Definition mantissa_mul := Pmult.
Definition mantissa_cmp x y := Pcompare x y Eq.
Definition mantissa_pos := Zpos.
Definition mantissa_neg := Zneg.

Definition valid_mantissa := fun (m : positive) => True.

Definition mantissa_sign m :=
  match m with
  | Zneg p => Mnumber true p
  | Z0 => Mzero
  | Zpos p => Mnumber false p
  end.

Definition mantissa_even m :=
  match m with
  | xO _ => true
  | _ => false
  end.

Definition mantissa_shl m d :=
  match d with Zpos nb => iter_pos (fun x => xO x) nb m | _ => xH end.

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Fixpoint digits_aux m nb { struct m } :=
  match m with
  | xH => nb
  | xO p => digits_aux p (Psucc nb)
  | xI p => digits_aux p (Psucc nb)
  end.

Definition mantissa_digits m := Zpos (digits_aux m xH).

Definition mantissa_split_div m d pos :=
  match Zfast_div_eucl (Zpos m) (Zpos d) with
  | (Zpos q, r) => (q, adjust_pos r d pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_shr_aux v :=
  match v with
  | (xO p, pos_Eq) => (p, pos_Eq)
  | (xO p, _)      => (p, pos_Lo)
  | (xI p, pos_Eq) => (p, pos_Mi)
  | (xI p, _)      => (p, pos_Up)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_shr m d pos :=
  match d with
  | Zpos nb =>
    iter_pos mantissa_shr_aux nb (m, pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.


Fixpoint mantissa_shrp_aux m d :=
  match m with
  | xO m1 =>
      if (d =? 1)%positive then pos_Up else mantissa_shrp_aux m1 (Ppred d)
  | xI m1 => pos_Up
  | xH    =>
      if (d =? 1)%positive then pos_Mi else pos_Up
  end.

Lemma mantissa_shrp_aux_correct m d :
   mantissa_shrp_aux m (Psucc d) =
   match (m ?= shift radix 1 d)%positive with
        | Eq  => pos_Mi
        |  _  => pos_Up
        end.
Proof.
apply eq_trans with
   (if (m =? shift radix 1 d)%positive then pos_Mi else pos_Up);
     last first.
  now rewrite Pos.eqb_compare; destruct Pos.compare.
rewrite Pos2Z.inj_eqb, shift_correct, Z.pow_pos_fold, Zmult_1_l.
rewrite <- radix_to_pos, <- Pos2Z.inj_pow.
revert d; induction m as [| m | m]; intros d.
- case (Pos.succ_pred_or d); intro Hd.
    now rewrite Hd; simpl; destruct m.
  rewrite <- Hd, Pos.pow_succ_r.
  now unfold mantissa_shrp_aux; case Pos.eqb.
- case (Pos.succ_pred_or d); intro Hd.
    now rewrite Hd; destruct m.
  rewrite <- Hd at 2.
  rewrite Pos.pow_succ_r.
  rewrite <- Pos2Z.inj_eqb, Pos.eqb_compare, Pos.compare_xO_xO.
  rewrite <- Pos.eqb_compare, Pos2Z.inj_eqb, <- IHm; simpl.
  now rewrite Hd, Pos.pred_succ; destruct d.
case (Pos.succ_pred_or d); intro Hd.
    now rewrite Hd.
rewrite <- Hd at 2.
rewrite Pos.pow_succ_r.
now destruct d.
Qed.

Definition mantissa_shrp m d pos :=
  match pos with
  | pos_Eq => mantissa_shrp_aux m (Z.to_pos d)
  | _ => pos_Up
  end.

Definition mantissa_div := fun m d => mantissa_split_div m d pos_Eq.

Definition exponent_div2_floor n :=
  match n with
  | Z0 => (Z0, false)
  | Zpos xH => (Z0, true)
  | Zneg xH => (Zneg xH, true)
  | Zpos (xO p) => (Zpos p, false)
  | Zneg (xO p) => (Zneg p, false)
  | Zpos (xI p) => (Zpos p, true)
  | Zneg (xI p) => (Zneg (Psucc p), true)
  end.

Definition mantissa_sqrt m :=
  match Z.sqrtrem (Zpos m) with
  | (Zpos s, r) =>
    let pos :=
      match r with
      | Z0 => pos_Eq
      | Zpos r =>
        match Pos.compare r s with
        | Gt => pos_Up
        | _ => pos_Lo
        end
      | Zneg _ => pos_Eq (* dummy *)
      end in
    (s, pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition PtoM_correct := fun x : positive => refl_equal x.
Definition ZtoM_correct := fun x : Z => refl_equal x.
Definition ZtoE_correct := fun x : Z => refl_equal x.

Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_one_correct := refl_equal 1%Z.
Definition exponent_neg_correct := fun x => refl_equal (- EtoZ x)%Z.
Definition exponent_add_correct := fun x y => refl_equal (EtoZ x + EtoZ y)%Z.
Definition exponent_sub_correct := fun x y => refl_equal (EtoZ x - EtoZ y)%Z.
Definition exponent_cmp_correct := fun x y => refl_equal (EtoZ x ?= EtoZ y)%Z.

Lemma exponent_div2_floor_correct :
  forall e, let (e',b) := exponent_div2_floor e in
  EtoZ e = (2 * EtoZ e' + if b then 1 else 0)%Z.
Proof.
unfold EtoZ, exponent_div2_floor.
intros [|[e|e|]|[e|e|]] ; try easy.
rewrite <- Pos.add_1_r.
change (- (2 * Zpos e + 1) = 2 * - (Zpos e + 1) + 1)%Z.
ring.
Qed.

Definition mantissa_zero_correct := refl_equal Z0.
Definition mantissa_pos_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zpos x).
Definition mantissa_neg_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zneg x).
Definition mantissa_one_correct := conj (refl_equal xH) I.
Definition mantissa_add_correct :=
  fun x y (_ _ : True) => conj (refl_equal (MtoP x + MtoP y)%positive) I.
Definition mantissa_sub_correct :=
  fun x y (_ _ : True) (_ : (MtoP y < MtoP x)%positive) => conj (refl_equal (MtoP x - MtoP y)%positive) I.
Definition mantissa_mul_correct :=
  fun x y (Hx Hy : True) => conj (refl_equal (MtoP x * MtoP y)%positive) I.
Definition mantissa_cmp_correct :=
  fun x y (Hx Hy : True) => refl_equal (Zpos (MtoP x) ?= Zpos (MtoP y))%Z.
Definition mantissa_even_correct :=
  fun x (_ : True) => refl_equal (Z.even (Zpos x)).

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
case x ; repeat split.
Qed.

Lemma mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).
Proof.
intros x _.
rewrite <- digits_conversion.
rewrite <- Digits.Zdigits2_Zdigits.
unfold EtoZ, mantissa_digits, MtoP, Digits.Zdigits2.
replace (Zpos (Digits.digits2_pos x)) with (Zpos (Digits.digits2_pos x) + 1 - 1)%Z by ring.
generalize xH at 1 2.
induction x ; intros p ; simpl digits_aux ; simpl Digits.digits2_pos.
rewrite IHx, 2!Pos2Z.inj_succ.
ring.
rewrite IHx, 2!Pos2Z.inj_succ.
ring.
ring.
Qed.

Lemma mantissa_scale2_correct :
  forall x d, valid_mantissa x ->
  let (x',d') := mantissa_scale2 x d in
  (IZR (Zpos (MtoP x')) * bpow radix (EtoZ d') = IZR (Zpos (MtoP x)) * bpow radix2 (EtoZ d))%R /\
  valid_mantissa x'.
Proof.
now intros x d Vx.
Qed.

Lemma mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\
  valid_mantissa (mantissa_shl y z).
Proof.
repeat split.
unfold EtoZ in H0.
rewrite H0.
apply refl_equal.
Qed.

Lemma mantissa_shr_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpos (shift radix 1 x) <= Zpos (MtoP y))%Z ->
  let (sq,l) := mantissa_shr y z k in
  let (q,r) := Zdiv_eucl (Zpos (MtoP y)) (Zpos (shift radix 1 x)) in
  Zpos (MtoP sq) = q /\
  l = adjust_pos r (shift radix 1 x) k /\
  valid_mantissa sq.
Proof.
intros x y z k _ Ezx.
destruct z as [|z|z] ; try easy.
injection Ezx.
clear Ezx.
unfold MtoP.
intros -> Hy.
unfold mantissa_shr.
rewrite iter_pos_nat.
case_eq (iter_nat mantissa_shr_aux (Pos.to_nat x) (y, k)).
intros sq l H1.
generalize (Z.div_str_pos _ _ (conj (refl_equal Lt : (0 < Zpos _)%Z) Hy)).
generalize (Z_div_mod (Z.pos y) (Z.pos (shift radix 1 x)) (eq_refl Gt)).
unfold Zdiv.
case Z.div_eucl.
intros q r [H2 H3] H4.
refine ((fun H => conj (proj1 H) (conj (proj2 H) I)) _).
revert H2 H3 Hy.
change (adjust_pos r (shift radix 1 x) k) with
  (match Z.pos (shift radix 1 x) with Zpos v => adjust_pos r v k | _ => l end).
rewrite shift_correct.
rewrite Zpower_pos_nat.
rewrite Zmult_1_l.
revert sq l q r H1 H4.
induction (Pos.to_nat x) as [|p IHp].
- change (Zpower_nat radix 0) with 1%Z.
  intros sq l q r.
  rewrite Zmult_1_l.
  simpl.
  intros H1.
  injection H1.
  intros <- <-.
  clear H1.
  intros _ H1 H2.
  revert H1.
  assert (H: r = 0%Z) by omega.
  rewrite H, Zplus_0_r.
  split.
  exact H1.
  now destruct k.
- intros sq' l' q' r'.
  rewrite iter_nat_S.
  destruct (iter_nat mantissa_shr_aux p (y, k)) as [sq l].
  specialize (IHp sq l).
  intros H1 H0 H2 H3 Hy.
  revert H2.
  generalize (Zle_lt_trans _ _ _ (proj1 H3) (proj2 H3)).
  case_eq (Zpower_nat radix (S p)) ; try easy.
  intros m'.
  revert H3.
  rewrite Zpower_nat_S.
  revert IHp.
  destruct (Zpower_nat radix p) as [|m|m] ; try easy.
  intros IHp H3 H4 _ H2.
  injection H4.
  intros <-.
  clear H4.
  change (radix_val radix) with 2%Z in H3.
  change (Zpos (xO m)) with (2 * Zpos m)%Z in H2.
  destruct (Zle_or_lt (Zpos m) r') as [Hr|Hr].
  + destruct (IHp (2 * q' + 1)%Z (r' - Zpos m)%Z) as [H4 H5].
    reflexivity.
    clear -H0 ; omega.
    rewrite H2.
    ring.
    clear -Hr H3 ; omega.
    rewrite H2.
    rewrite <- (Zplus_0_l (Zpos m)) at 1.
    apply Zplus_le_compat with (2 := Hr).
    apply Zmult_le_0_compat.
    clear -H3 ; omega.
    now apply Zlt_le_weak.
    clear IHp.
    destruct q' as [|q'|q'] ; try easy.
    clear H0.
    destruct sq as [sq|sq|] ; try easy.
    simpl in H1.
    simpl in H4.
    split.
    injection H4.
    intros <-.
    apply f_equal, sym_eq.
    now destruct l ; injection H1.
    clear H4.
    unfold adjust_pos.
    destruct r' as [|r'|r'] ; try now elim Hr.
    apply sym_eq.
    replace l' with (match l with pos_Eq => pos_Mi | _ => pos_Up end).
    2: clear -H1 ; destruct l ; injection H1 ; easy.
    rewrite H5.
    clear H1 H5.
    destruct (Zcompare_spec (Zpos r') (Zpos m)) as [H|H|H].
    * elim Hr.
      now apply Zcompare_Gt.
    * rewrite (Zeq_minus _ _ H).
      simpl.
      case k ; try easy ; case m ; easy.
    * assert (H': (Zpos r' - Zpos m)%Z = Zpos (r' - m)) by now apply Z.pos_sub_gt.
      rewrite H'.
      unfold adjust_pos.
      clear -H H3.
      destruct m as [m|m|] ;
        case Zcompare ; try easy ; try (case k ; easy).
      clear -H3 H ; omega.
  + destruct (IHp (2 * q')%Z r') as [H4 H5].
    reflexivity.
    clear -H0 ; omega.
    rewrite H2.
    ring.
    clear -Hr H3 ; omega.
    rewrite H2.
    rewrite <- (Zplus_0_r (Zpos m)) at 1.
    apply Zplus_le_compat with (2 := proj1 H3).
    apply Zle_0_minus_le.
    replace (2 * Zpos m * q' - Zpos m)%Z with (Zpos m * (2 * q' - 1))%Z by ring.
    apply Zmult_le_0_compat.
    easy.
    clear -H0 ; omega.
    clear IHp.
    destruct q' as [|q'|q'] ; try easy.
    clear H0.
    destruct sq as [sq|sq|] ; try easy.
    simpl in H1.
    simpl in H4.
    split.
    injection H4.
    intros <-.
    apply f_equal, sym_eq.
    now destruct l ; injection H1.
    clear H4.
    unfold adjust_pos.
    apply sym_eq.
    replace l' with (match l with pos_Eq => pos_Eq | _ => pos_Lo end).
    2: clear -H1 ; destruct l ; injection H1 ; easy.
    rewrite H5.
    clear H1 H5.
    destruct r' as [|r'|r'] ; try now elim (proj1 H3).
    case k ; try easy ; case m ; easy.
    rewrite Zcompare_Lt with (1 := Hr).
    unfold adjust_pos.
    destruct m.
    case Zcompare ; try easy ; case k ; easy.
    case Zcompare ; try easy ; case k ; easy.
    now rewrite Hr.
Qed.

Lemma mantissa_shrp_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpower radix (Zpos x - 1) <= Zpos (MtoP y) < Zpos (shift radix 1 x))%Z ->
  let l := mantissa_shrp y z k in
  l = adjust_pos (Zpos (MtoP y)) (shift radix 1 x) k.
Proof.
intros x y [|z|z] k _ Ezx; try discriminate.
unfold MtoP.
unfold EtoZ in Ezx; rewrite Ezx; simpl Z.to_pos; clear z Ezx.
case (Pos.succ_pred_or x); intro Hx.
  rewrite Hx.
  now destruct y; destruct k.
rewrite <- Hx at 1.
rewrite Pos2Z.inj_succ.
replace (Z.succ (Z.pos (Pos.pred x)) - 1)%Z  with (Z.pos (Pos.pred x)) by lia.
intros [Hl _].
unfold mantissa_shrp; simpl Z.to_pos.
replace (mantissa_shrp_aux y x) with
     (mantissa_shrp_aux (xO y) (Psucc x)); last first.
  simpl.
  now rewrite Pos.pred_succ; destruct x.
rewrite mantissa_shrp_aux_correct.
replace  (shift radix 1 x) with (xO ((Z.to_pos radix) ^ (Pos.pred x))); last first.
  apply Pos2Z.inj.
  rewrite <- (Pos.mul_1_r (_ ^ _)), <- (Pos.mul_xO_r _ xH).
  rewrite Pos.mul_comm, <- Pos.pow_succ_r, Hx, shift_correct.
  rewrite !Z.pow_pos_fold, Pos2Z.inj_pow, radix_to_pos; lia.
simpl.
rewrite Pos.compare_xO_xO; try easy.
revert Hl.
rewrite <-Z.pow_pos_fold, <- radix_to_pos, <- Pos2Z.inj_pow_pos.
simpl.
case Pos.compare_spec; try easy.
  intro H; lia.
now destruct k.
Qed.

Lemma mantissa_div_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (Zpos (MtoP y) <= Zpos (MtoP x))%Z ->
  let (q,l) := mantissa_div x y in
  Zpos (MtoP q) = (Zpos (MtoP x) / Zpos (MtoP y))%Z /\
  Bracket.inbetween_int (Zpos (MtoP q)) (IZR (Zpos (MtoP x)) / IZR (Zpos (MtoP y)))%R (convert_location_inv l) /\
  valid_mantissa q.
Proof.
intros x y _ _.
unfold MtoP.
intros Hxy.
unfold mantissa_div, mantissa_split_div.
generalize (Z_div_mod (Z.pos x) (Z.pos y) (eq_refl Gt)).
rewrite Zfast_div_eucl_correct.
destruct Z.div_eucl as [q r].
intros [H1 H2].
assert (H: (0 < q)%Z).
  apply Zmult_lt_reg_r with (Zpos y).
  easy.
  rewrite Zmult_0_l, Zmult_comm.
  apply Zplus_lt_reg_r with r.
  rewrite Zplus_0_l.
  rewrite <- H1.
  now apply Zlt_le_trans with (2 := Hxy).
destruct q as [|q|q] ; try easy.
clear H Hxy.
assert (Hq := Zdiv_unique _ _ _ _ H2 H1).
refine (conj Hq (conj _ I)).
unfold Bracket.inbetween_int.
destruct (Zle_or_lt 2 (Zpos y)) as [Hy|Hy].
- assert (H: (1 < Zpos y)%Z) by now apply Zgt_lt, Zle_succ_gt.
  rewrite adjust_pos_correct by assumption.
  rewrite plus_IZR.
  rewrite <- (Rinv_r (IZR (Zpos y))) by now apply IZR_neq.
  apply Bracket.new_location_correct ; try assumption.
  now apply Rinv_0_lt_compat, IZR_lt.
  apply Bracket.inbetween_Exact.
  rewrite H1, plus_IZR, mult_IZR.
  field.
  now apply IZR_neq.
- rewrite Hq, H1.
  clear H1 Hq.
  cut (Zpos y = 1 /\ r = 0)%Z.
  2: omega.
  clear.
  intros [-> ->].
  simpl.
  apply Bracket.inbetween_Exact.
  unfold Rdiv.
  now rewrite Zdiv_1_r, Rinv_1, Rmult_1_r.
Qed.

Lemma mantissa_sqrt_correct :
  forall x, valid_mantissa x ->
  let (q,l) := mantissa_sqrt x in
  let (s,r) := Z.sqrtrem (Zpos (MtoP x)) in
  Zpos (MtoP q) = s /\
  match l with pos_Eq => r = Z0 | pos_Lo => (0 < r <= s)%Z | pos_Mi => False | pos_Up => (s < r)%Z end /\
  valid_mantissa q.
Proof.
intros x _.
unfold mantissa_sqrt, MtoP.
refine (_ (Z.sqrtrem_spec (Zpos x) _)).
2: easy.
case Z.sqrtrem.
intros s r [H1 H2].
destruct s as [|s|s].
simpl in H1.
rewrite <- H1 in H2.
now elim (proj2 H2).
repeat split.
destruct r as [|r|r].
apply eq_refl.
case Pcompare_spec.
intros ->.
split.
easy.
apply Zle_refl.
intros H.
split.
easy.
now apply Zlt_le_weak.
easy.
now elim (proj1 H2).
now elim (Zle_trans _ _ _ (proj1 H2) (proj2 H2)).
Qed.

End StdZRadix2.
