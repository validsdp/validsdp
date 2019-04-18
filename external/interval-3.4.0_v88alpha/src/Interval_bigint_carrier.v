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

Require Import Bool.
From Bignums Require Import BigN BigZ.
Require Import Psatz.
From Flocq Require Import Raux Digits.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_specific_sig.

Module BigIntRadix2 <: FloatCarrier.

Definition radix := radix2.
Definition radix_correct := refl_equal Lt.
Definition smantissa_type := BigZ.t.
Definition mantissa_type := BigN.t.
Definition exponent_type := BigZ.t.

Definition MtoZ := BigZ.to_Z.
Definition ZtoM := BigZ.of_Z.
Definition MtoP v := match BigN.to_Z v with Zpos w => w | _ => xH end.
Definition PtoM := BigN.of_pos.
Definition EtoZ := BigZ.to_Z.
Definition ZtoE := BigZ.of_Z.

Definition valid_mantissa v := exists p, BigN.to_Z v = Zpos p.

Definition exponent_zero := 0%bigZ.
Definition exponent_one := 1%bigZ.
Definition exponent_neg := BigZ.opp.
Definition exponent_add := BigZ.add.
Definition exponent_sub := BigZ.sub.
Definition exponent_cmp := BigZ.compare.
Definition mantissa_zero := 0%bigZ.
Definition mantissa_one := 1%bigN.
Definition mantissa_add := BigN.add.
Definition mantissa_sub := BigN.sub.
Definition mantissa_mul := BigN.mul.
Definition mantissa_cmp := BigN.compare.
Definition mantissa_pos := BigZ.Pos.
Definition mantissa_neg := BigZ.Neg.

Definition mantissa_sign m :=
  if BigZ.eqb m 0%bigZ then Mzero
  else
    match m with
    | BigZ.Pos p => Mnumber false p
    | BigZ.Neg p => Mnumber true p
    end.

Definition mantissa_shl m d :=
  BigN.shiftl m (BigZ.to_N d).

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Definition mantissa_digits m :=
  BigZ.Pos (BigN.Ndigits m - BigN.head0 m)%bigN.

Definition mantissa_even m := BigN.even m.

Definition mantissa_split_div m d pos :=
  let (q, r) := BigN.div_eucl m d in (q,
  if BigN.eqb r 0%bigN then
    match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  else
    match BigN.compare (BigN.shiftl r 1%bigN) d with
    | Lt => pos_Lo
    | Eq => match pos with pos_Eq => pos_Mi | _ => pos_Up end
    | Gt => pos_Up
    end).

Definition mantissa_div :=
  fun m d => mantissa_split_div m d pos_Eq.

(*
Definition mantissa_shr m d pos :=
  mantissa_split_div m (mantissa_shl 1%bigN d) pos.
*)

Definition mantissa_shr m d pos :=
  let dd := BigZ.to_N d in
  (BigN.shiftr m dd,
  let d1 := BigN.pred dd in
  match BigN.compare (BigN.tail0 m) d1 with
  | Gt => match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  | Eq => match pos with pos_Eq => pos_Mi | _ => pos_Up end
  | Lt =>
    if BigN.even (BigN.shiftr m d1) then pos_Lo
    else pos_Up
  end).

(*
Definition mantissa_shr m d pos :=
  let dd := BigZ.to_N d in
  let d1 := BigN.pred dd in
  (BigN.shiftr dd m,
  let p1 := BigN.is_even (BigN.shiftr d1 m) in
  let p2 := BigN.is_even (BigN.shiftr d1 (BigN.pred m)) in
  if p1 then
    if p2 then (* 00 *)
      pos_Lo
    else       (* 01 *)
      match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  else
    if p2 then (* 10 *)
      match pos with pos_Eq => pos_Mi | _ => pos_Up end
    else       (* 11 *)
      pos_Up).
*)

Definition mantissa_shrp m d pos :=
  match pos with
  | pos_Eq =>
        let dd := BigZ.to_N d in
         match BigN.compare (BigN.shiftl m 1) (BigN.shiftl 1 dd) with
        | Eq  => pos_Mi
        |  _  => pos_Up
        end
  | _ => pos_Up
  end.

Definition exponent_div2_floor e :=
  match e with
  | BigZ.Pos p =>
    (BigZ.Pos (BigN.shiftr p 1%bigN), negb (BigN.even p))
  | BigZ.Neg p =>
    let q := BigN.shiftr p 1%bigN in
    if BigN.even p then (BigZ.Neg q, false)
    else (BigZ.Neg (BigN.succ q), true)
  end.

Definition mantissa_sqrt m :=
  let s := BigN.sqrt m in
  let r := BigN.sub m (BigN.square s) in (s,
  if BigN.eqb r 0%bigN then pos_Eq
  else match BigN.compare r s with Gt => pos_Up | _ => pos_Lo end).

Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_one_correct := refl_equal 1%Z.
Definition mantissa_zero_correct := refl_equal Z0.

Definition ZtoM_correct := BigZ.spec_of_Z.
Definition ZtoE_correct := BigZ.spec_of_Z.
Definition exponent_neg_correct := BigZ.spec_opp.
Definition exponent_add_correct := BigZ.spec_add.
Definition exponent_sub_correct := BigZ.spec_sub.

Lemma exponent_div2_floor_correct :
  forall e, let (e',b) := exponent_div2_floor e in
  EtoZ e = (2 * EtoZ e' + if b then 1 else 0)%Z.
Proof.
unfold exponent_div2_floor.
intros [e|e].
unfold EtoZ.
simpl BigZ.to_Z.
rewrite BigN.spec_shiftr.
rewrite <- Z.div2_spec.
rewrite BigN.spec_even.
rewrite <- Zodd_even_bool.
apply Zdiv2_odd_eqn.
rewrite BigN.spec_even.
case_eq (Z.even [e]%bigN).
unfold EtoZ.
simpl BigZ.to_Z.
rewrite BigN.spec_shiftr.
rewrite <- Z.div2_spec.
rewrite (Zdiv2_odd_eqn [e]%bigN) at 2.
rewrite Zodd_even_bool.
intros ->.
simpl negb ; cbv iota.
ring.
unfold EtoZ.
simpl BigZ.to_Z.
rewrite BigN.spec_succ.
rewrite BigN.spec_shiftr.
rewrite <- Z.div2_spec.
rewrite (Zdiv2_odd_eqn [e]%bigN) at 2.
rewrite Zodd_even_bool.
intros ->.
simpl negb ; cbv iota.
ring.
Qed.

Lemma PtoM_correct :
  forall n, MtoP (PtoM n) = n.
intros.
unfold MtoP, PtoM.
rewrite BigN.spec_of_pos.
apply refl_equal.
Qed.

Lemma mantissa_pos_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_pos x) = Zpos (MtoP x).
intros x (p, H).
unfold MtoZ, MtoP.
simpl.
rewrite H.
apply refl_equal.
Qed.

Lemma mantissa_neg_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_neg x) = Zneg (MtoP x).
intros x (p, H).
unfold MtoZ, MtoP.
simpl.
rewrite H.
apply refl_equal.
Qed.

Lemma mantissa_even_correct :
  forall x, valid_mantissa x ->
  mantissa_even x = Z.even (Zpos (MtoP x)).
Proof.
intros x (px, Hx).
unfold mantissa_even, Zeven, MtoP.
generalize (BigN.spec_even x).
rewrite Hx.
case (BigN.even x) ;
  destruct px as [px|px| ] ; try easy.
Qed.

Lemma mantissa_one_correct :
  MtoP mantissa_one = xH /\ valid_mantissa mantissa_one.
Proof.
repeat split.
now exists xH.
Qed.

Lemma mantissa_add_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_add x y) = (MtoP x + MtoP y)%positive /\
  valid_mantissa (mantissa_add x y).
Proof.
intros x y (px, Hx) (py, Hy).
unfold mantissa_add, valid_mantissa, MtoP.
rewrite BigN.spec_add.
rewrite Hx, Hy.
repeat split.
now exists (px + py)%positive.
Qed.

Lemma mantissa_sub_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (MtoP y < MtoP x)%positive ->
  MtoP (mantissa_sub x y) = (MtoP x - MtoP y)%positive /\
  valid_mantissa (mantissa_sub x y).
Proof.
intros x y (px, Hx) (py, Hy).
unfold mantissa_sub, valid_mantissa, MtoP.
rewrite BigN.spec_sub.
rewrite Hx, Hy.
simpl.
rewrite Z.pos_sub_spec.
case Pos.compare_spec.
intros H1 H2.
elim (Pos.lt_irrefl py).
now rewrite H1 in H2.
intros H1 H2.
elim (Pos.lt_irrefl py).
now apply Pos.lt_trans with px.
intros H _.
repeat split.
now exists (px - py)%positive.
Qed.

Lemma mantissa_mul_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_mul x y) = (MtoP x * MtoP y)%positive /\
  valid_mantissa (mantissa_mul x y).
intros x y (px, Hx) (py, Hy).
unfold mantissa_mul, valid_mantissa, MtoP.
rewrite BigN.spec_mul.
rewrite Hx, Hy.
simpl.
split.
apply refl_equal.
exists (px * py)%positive.
apply refl_equal.
Qed.

Lemma mantissa_cmp_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  mantissa_cmp x y = Z.compare (Zpos (MtoP x)) (Zpos (MtoP y)).
intros x y (px, Hx) (py, Hy).
unfold mantissa_cmp, MtoP.
rewrite Hx, Hy, <- Hx, <- Hy.
apply BigN.spec_compare.
Qed.

Lemma exponent_cmp_correct :
  forall x y, exponent_cmp x y = Z.compare (MtoZ x) (MtoZ y).
intros.
unfold exponent_cmp, MtoZ.
apply sym_eq.
generalize (BigZ.spec_compare x y).
unfold Z.lt, Z.gt.
case (x ?= y)%bigZ ; intro H ; rewrite H ;
 first [ apply Z.compare_refl | apply refl_equal ].
Qed.

Lemma mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).
Proof.
intros x (px, Vx).
unfold mantissa_digits, EtoZ.
simpl.
rewrite BigN.spec_sub_pos.
rewrite BigN.spec_Ndigits.
rewrite <- digits_conversion.
rewrite <- Zplus_0_r.
rewrite <- (Zplus_opp_r [BigN.head0 x]%bigN)%Z.
rewrite Zplus_assoc.
apply (f_equal (fun v => v + _)%Z).
rewrite <- Zdigits_mult_Zpower.
2: now apply Zgt_not_eq.
2: apply BigN.spec_pos.
refine (_ (BigN.spec_head0 x _)).
2: now rewrite Vx.
intros (H1,H2).
unfold MtoP.
rewrite Vx.
set (d := Zdigits radix (Zpos px * radix ^ [BigN.head0 x]%bigN)).
cut (d <= Zpos (BigN.digits x) /\ Zpos (BigN.digits x) - 1 < d)%Z. omega.
unfold d ; clear d.
split.
apply Zdigits_le_Zpower.
rewrite Zabs_Zmult, Zmult_comm.
rewrite Z.abs_eq.
simpl Z.abs.
now rewrite <- Vx.
apply Zpower_ge_0.
apply Zdigits_gt_Zpower.
rewrite Zabs_Zmult, Zmult_comm.
rewrite Z.abs_eq.
simpl Z.abs.
now rewrite <- Vx.
apply Zpower_ge_0.
rewrite BigN.spec_Ndigits.
assert (Zpower 2 [BigN.head0 x]%bigN * 1 < Zpower 2 (Zpos (BigN.digits x)))%Z.
apply Z.le_lt_trans with (Zpower 2 [BigN.head0 x]%bigN * Zpos px)%Z.
apply Zmult_le_compat_l.
now case px.
apply (Zpower_ge_0 radix2).
rewrite <- Vx.
apply BigN.spec_head0.
now rewrite Vx.
change (~ ([BigN.head0 x]%bigN > Zpos (BigN.digits x))%Z).
intros H'.
apply (Zlt_not_le _ _ H).
rewrite Zmult_1_r.
apply (Zpower_le radix2).
apply Zlt_le_weak.
now apply Z.gt_lt.
Qed.

Lemma mantissa_scale2_correct :
  forall x d, valid_mantissa x ->
  let (x',d') := mantissa_scale2 x d in
  (IZR (Zpos (MtoP x')) * bpow radix (EtoZ d') = IZR (Zpos (MtoP x)) * bpow radix2 (EtoZ d))%R /\
  valid_mantissa x'.
Proof.
intros x d Vx.
repeat split.
exact Vx.
Qed.

Lemma mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\ valid_mantissa (mantissa_shl y z).
Proof.
intros x y z (py, Vy) Hz.
unfold mantissa_shl, MtoP, valid_mantissa.
rewrite BigN.spec_shiftl, Vy.
cutrewrite (Z.shiftl (Zpos py) [BigZ.to_N z]%bigN = Zpos (shift radix py x))%Z.
repeat split.
refl_exists.
unfold EtoZ in Hz.
rewrite spec_to_Z, Hz.
rewrite Z.shiftl_mul_pow2 by easy.
rewrite shift_correct.
now rewrite Z.pow_pos_fold.
Qed.

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
unfold mantissa_sign.
rewrite BigZ.spec_eqb.
case Z.eqb_spec.
easy.
change (BigZ.to_Z 0%bigZ) with Z0.
case x ; unfold valid_mantissa ; simpl ; intros ; rename n into H.
(* + *)
assert (BigN.to_Z t = Zpos (MtoP t)).
generalize H. clear.
unfold MtoP.
generalize (BigN.spec_pos t).
case (BigN.to_Z t) ; intros.
elim H0.
apply refl_equal.
apply refl_equal.
elim H.
apply refl_equal.
split.
exact H0.
exists (MtoP t).
exact H0.
(* - *)
assert (- BigN.to_Z t = Zneg (MtoP t))%Z.
generalize H. clear.
unfold MtoP.
generalize (BigN.spec_pos t).
case (BigN.to_Z t) ; intros.
elim H0.
apply refl_equal.
apply refl_equal.
elim H.
apply refl_equal.
split.
exact H0.
exists (MtoP t).
exact (Z.opp_inj _ (Zpos _) H0).
Qed.

Lemma mantissa_shr_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpos (shift radix 1 x) <= Zpos (MtoP y))%Z ->
  let (sq,l) := mantissa_shr y z k in
  let (q,r) := Z.div_eucl (Zpos (MtoP y)) (Zpos (shift radix 1 x)) in
  Zpos (MtoP sq) = q /\
  l = adjust_pos r (shift radix 1 x) k /\
  valid_mantissa sq.
Proof.
intros x y z k [y' Vy] Ezx.
unfold mantissa_shr, MtoP.
unfold EtoZ in Ezx.
rewrite Vy.
intros Hy.
unfold valid_mantissa.
rewrite BigN.spec_shiftr_pow2.
rewrite spec_to_Z_pos by now rewrite Ezx.
rewrite Vy, Ezx.
generalize (Z.div_str_pos _ _ (conj (refl_equal Lt : (0 < Zpos _)%Z) Hy)).
generalize (Z_div_mod (Z.pos y') (Z.pos (shift radix 1 x)) (eq_refl Gt)).
rewrite shift_correct, Zmult_1_l.
change (Zpower 2 (Zpos x)) with (Z.pow_pos radix x).
unfold Z.div.
case Z.div_eucl.
intros q r.
revert Hy.
change (adjust_pos r (shift radix 1 x) k) with
  (match Z.pos (shift radix 1 x) with Zpos v => adjust_pos r v k | _ => pos_Eq end).
rewrite shift_correct, Zmult_1_l.
intros Hy [H2 H3].
destruct q as [ |q|q] ; try easy.
intros _.
refine (conj (eq_refl _) (conj _ (ex_intro _ q (eq_refl _)))).
generalize (BigN.spec_tail0 y).
rewrite Vy.
intros H.
specialize (H (eq_refl Lt)).
destruct H as [yn [Hy1 Hy2]].
rewrite BigN.spec_compare.
rewrite BigN.spec_even.
rewrite BigN.spec_shiftr_pow2.
rewrite Vy.
rewrite BigN.spec_pred_pos ; rewrite BigZ.spec_to_Z_pos ; rewrite Ezx ; try easy.
unfold adjust_pos.
change (Z.pow_pos radix x) with (Z.pow_pos (Zpos 2) x).
rewrite <- Pos2Z.inj_pow_pos.
assert (Hp : (0 <= Zpos x - 1)%Z).
  now apply (Zlt_0_le_0_pred (Zpos x)).
assert (H2x : (2^x)%positive = xO (Z.to_pos (2 ^ (Zpos x - 1)))).
  clear -Hp.
  rewrite <- (Z2Pos.inj_pow_pos 2) by easy.
  change (Z.pow_pos 2 x) with (Zpower 2 (Zpos x)).
  pattern (Zpos x) at 1 ; replace (Zpos x) with (1 + (Zpos x - 1))%Z by ring.
  rewrite Zpower_plus by easy.
  rewrite Z2Pos.inj_mul ; try easy.
  now apply (Zpower_gt_0 radix2).
rewrite H2x.
case Z.compare_spec ; intros Hc.
- replace r with (Zpos (Z.to_pos (2^(Zpos x - 1)))).
  now rewrite Z.compare_refl.
  rewrite Z2Pos.id.
  2: apply (Zpower_gt_0 radix2) ; clear ; zify ; omega.
  replace (Zpower 2 (Zpos x - 1)) with (Zmod (Zpos y') (Zpower 2 (Zpos x))).
  apply sym_eq.
  apply Z.mod_unique_pos with (1 := H3) (2 := H2).
  rewrite Hy2, Hc.
  rewrite Zmult_plus_distr_l, (Zmult_comm 2), Zmult_1_l.
  rewrite <- Zmult_assoc.
  rewrite <- (Zpower_plus 2 1).
  ring_simplify (1 + (Zpos x - 1))%Z.
  rewrite Zplus_comm, Z_mod_plus_full.
  apply Zmod_small.
  split.
  apply (Zpower_ge_0 radix2).
  apply (Zpower_lt radix2).
  easy.
  apply (Z.lt_pred_l (Zpos x)).
  easy.
  now case x.
- rewrite Zeven_mod.
  assert (Hy': (Zpos y' / Zpower 2 (Zpos x - 1) = Zpos q * 2 + r / Zpower 2 (Zpos x - 1))%Z).
    rewrite H2.
    rewrite Zplus_comm, Zmult_comm.
    change (Z.pow_pos radix x) with (Zpower 2 (Zpos x)).
    pattern (Zpos x) at 1 ; replace (Zpos x) with (1 + (Zpos x - 1))%Z by ring.
    rewrite Zpower_plus by easy.
    rewrite Zmult_assoc.
    rewrite (Zplus_comm (Zpos q * 2)).
    apply Z_div_plus_full.
    now apply Zgt_not_eq, (Zpower_gt_0 radix2).
  rewrite Hy'.
  rewrite Zplus_comm, Z_mod_plus_full.
  case Z.compare_spec ; intros Hr.
  + contradict H2.
    rewrite Hy2, Hr.
    rewrite Z2Pos.id.
    2: apply (Zpower_gt_0 radix2) ; clear ; zify ; omega.
    change (Z.pow_pos radix x) with (Zpower 2 (Zpos x)).
    pattern (Zpos x) at 1 ; replace (Zpos x) with (1 + (Zpos x - 1))%Z by ring.
    rewrite Zpower_plus by easy.
    change (2 ^ 1)%Z with 2%Z.
    replace (2 * 2 ^ (Zpos x - 1) * Zpos q + 2 ^ (Zpos x - 1))%Z with ((1 + Zpos q * 2) * 2 ^ (Zpos x - 1))%Z by ring.
    replace (Zpos x - 1)%Z with (Zpos x - 2 - [BigN.tail0 y]%bigN + ([BigN.tail0 y]%bigN + 1))%Z by ring.
    rewrite Zpower_plus.
    2: clear -Hc ; omega.
    2: apply Z.le_le_succ_r, BigN.spec_pos.
    intros H2.
    apply (f_equal (fun v => Zmod v (2 ^ ([BigN.tail0 y]%bigN + 1)))) in H2.
    revert H2.
    rewrite Zmult_assoc, Z_mod_mult.
    rewrite Zmult_plus_distr_l.
    rewrite (Zmult_comm 2), <- Zmult_assoc, Zmult_1_l.
    rewrite Zplus_comm, (Zmult_comm 2).
    rewrite <- (Zpower_plus 2 _ 1).
    2: apply BigN.spec_pos.
    2: easy.
    rewrite Z_mod_plus_full.
    rewrite Zmod_small.
    apply Zgt_not_eq.
    apply (Zpower_gt_0 radix2).
    apply BigN.spec_pos.
    split.
    apply (Zpower_ge_0 radix2).
    apply (Zpower_lt radix2).
    apply Z.le_le_succ_r, BigN.spec_pos.
    apply Z.lt_succ_diag_r.
  + rewrite Zeq_bool_true.
    destruct r as [ |r|r] ; [ |easy| ].
    2: now elim (proj1 H3).
    destruct k ; try easy.
    contradict H2.
    rewrite Hy2, Zplus_0_r.
    change (Z.pow_pos radix x) with (Zpower 2 (Zpos x)).
    replace (Zpos x) with (Zpos x - 1 - [BigN.tail0 y]%bigN + 1 + [BigN.tail0 y]%bigN)%Z by ring.
    rewrite <- (Zmult_comm (Zpos q)).
    rewrite Zpower_plus.
    2: clear -Hc ; omega.
    2: apply BigN.spec_pos.
    rewrite Zmult_assoc.
    intros H.
    apply Z.mul_reg_r in H.
    2: apply Zgt_not_eq, (Zpower_gt_0 radix2), BigN.spec_pos.
    revert H.
    rewrite Zpower_plus ; try easy.
    2: clear -Hc ; omega.
    change (2 ^ 1)%Z with 2%Z.
    clear ; intros.
    apply (f_equal Z.even) in H.
    revert H.
    rewrite Zplus_comm, Z.even_add_mul_2.
    rewrite Zmult_assoc, Z.even_mul.
    now rewrite orb_comm.
    rewrite Zdiv_small.
    easy.
    split.
    apply H3.
    rewrite Z2Pos.id in Hr.
    exact Hr.
    now apply (Zpower_gt_0 radix2).
  + rewrite Zeq_bool_false.
    clear -Hr.
    now destruct r as [ |r|r].
    rewrite Zmod_small.
    apply Zgt_not_eq.
    apply Z.gt_lt, Zle_succ_gt.
    apply Z.div_le_lower_bound.
    now apply (Zpower_gt_0 radix2).
    rewrite Zmult_1_r.
    rewrite Z2Pos.id in Hr.
    now apply Zlt_le_weak.
    now apply (Zpower_gt_0 radix2).
    split.
    now apply BigNumPrelude.div_le_0.
    apply Z.div_lt_upper_bound.
    now apply (Zpower_gt_0 radix2).
    rewrite <- (Zpower_plus 2 _ 1) by easy.
    now ring_simplify (Zpos x - 1 + 1)%Z.
- replace r with Z0.
  reflexivity.
  apply sym_eq.
  replace Z0 with (Zmod (Zpos y') (Zpower 2 (Zpos x))).
  apply Z.mod_unique_pos with (1 := H3) (2 := H2).
  rewrite Hy2.
  replace [BigN.tail0 y]%bigN with ([BigN.tail0 y]%bigN - Zpos x + Zpos x)%Z by ring.
  rewrite Zpower_plus.
  rewrite Zmult_assoc.
  apply Z_mod_mult.
  clear -Hc ; omega.
  easy.
Qed.

Lemma mantissa_shrp_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpower radix (Zpos x - 1) <= Zpos (MtoP y) < Zpos (shift radix 1 x))%Z ->
  let l := mantissa_shrp y z k in
  l = adjust_pos (Zpos (MtoP y)) (shift radix 1 x) k.
Proof.
intros x y z k [v Hv] Ezx.
unfold mantissa_shrp.
case (Pos.succ_pred_or x); intro Hx.
  rewrite Hx.
  intros Hl; simpl in Hl.
  assert (MtoP y = 1%positive) by lia.
  rewrite H.
  unfold MtoP in H; rewrite Hv in H.
  destruct k; simpl; try easy.
  unfold EtoZ in Ezx.
  case BigN.compare_spec; try easy;
  intro H1; red in H1;
  rewrite !BigN.spec_shiftl, spec_to_Z, Ezx in H1;
  simpl Z.sgn in H1;
  rewrite Hx, Hv in H1; simpl in H1; compute in H1; rewrite H in H1; try discriminate H1; try lia.
  rewrite <- Hx at 1.
  rewrite Pos2Z.inj_succ.
  replace (Z.succ (Z.pos (Pos.pred x)) - 1)%Z  with (Z.pos (Pos.pred x)) by lia.
intros [Hl _].
unfold mantissa_shrp.
replace  (shift radix 1 x) with (xO ((Z.to_pos radix) ^ (Pos.pred x))); last first.
  apply Pos2Z.inj.
  rewrite <- (Pos.mul_1_r (_ ^ _)), <- (Pos.mul_xO_r _ xH).
  rewrite Pos.mul_comm, <- Pos.pow_succ_r, Hx, shift_correct.
  rewrite !Z.pow_pos_fold, Pos2Z.inj_pow, radix_to_pos; lia.
simpl.
replace
  (BigN.shiftl y 1 ?= BigN.shiftl 1 (BigZ.to_N z))%bigN
with
   (MtoP y ?= 2 ^ Pos.pred x)%positive.
  revert Hl.
  rewrite <-Z.pow_pos_fold, <- radix_to_pos, <- Pos2Z.inj_pow_pos.
  simpl.
  case Pos.compare_spec; try easy.
    intro H; lia.
  now destruct k.
rewrite BigN.spec_compare, !BigN.spec_shiftl.
rewrite Z.shiftl_1_l.
unfold EtoZ in Ezx.
rewrite spec_to_Z, Ezx.
unfold MtoP; rewrite Hv.
rewrite Z.mul_1_l.
rewrite <- Hx at 2.
rewrite Pos2Z.inj_succ.
rewrite Z.pow_succ_r, Z.mul_comm; try lia.
replace (Z.shiftl (Z.pos v) [1]%bigN)  with
  (Zpos v * 2)%Z by (cbn; rewrite Pos2Z.inj_mul; lia).
rewrite <- Pos2Z.inj_pow; try easy.
now rewrite <- Zmult_compare_compat_r.
Qed.

Lemma mantissa_div_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (Zpos (MtoP y) <= Zpos (MtoP x))%Z ->
  let (q,l) := mantissa_div x y in
  Zpos (MtoP q) = (Zpos (MtoP x) / Zpos (MtoP y))%Z /\
  Bracket.inbetween_int (Zpos (MtoP q)) (IZR (Zpos (MtoP x)) / IZR (Zpos (MtoP y)))%R (convert_location_inv l) /\
  valid_mantissa q.
Proof.
intros x y [x' Vx] [y' Vy].
unfold MtoP.
rewrite Vx, Vy.
unfold mantissa_div, mantissa_split_div.
generalize (BigN.spec_div_eucl x y).
generalize (Z_div_mod (Z.pos (MtoP x)) (Z.pos (MtoP y)) (eq_refl Gt)).
unfold MtoP.
rewrite Vx, Vy.
destruct BigN.div_eucl as [q r].
destruct Z.div_eucl as [q' r'].
intros [H1 H2] H.
injection H.
clear H.
intros Hr' Vq Hxy.
assert (H: (0 < q')%Z).
  apply Zmult_lt_reg_r with (Zpos y').
  easy.
  rewrite Zmult_0_l, Zmult_comm.
  apply Zplus_lt_reg_r with r'.
  rewrite Zplus_0_l.
  rewrite <- H1.
  now apply Z.lt_le_trans with (2 := Hxy).
destruct q' as [ |q'|q'] ; try easy.
rewrite Vq.
clear H Hxy.
assert (Hq := Zdiv_unique _ _ _ _ H2 H1).
refine (conj Hq (conj _ (ex_intro _ _ Vq))).
unfold Bracket.inbetween_int.
rewrite BigN.spec_eqb.
rewrite BigN.spec_compare.
rewrite BigN.spec_shiftl_pow2.
rewrite Hr', Vy.
change (BigN.to_Z 0) with Z0.
change (2 ^ [1]%bigN)%Z with 2%Z.
destruct (Z.eqb_spec r' 0) as [Hr|Hr].
- apply Bracket.inbetween_Exact.
  rewrite H1, Hq, Hr, Zplus_0_r.
  rewrite mult_IZR.
  field.
  now apply IZR_neq.
- replace (convert_location_inv _) with (Bracket.loc_Inexact (Z.compare (r' * 2) (Zpos y'))).
  2: now case Z.compare.
  apply Bracket.inbetween_Inexact.
  unfold Rdiv.
  rewrite H1, Zmult_comm.
  split ;
    apply Rmult_lt_reg_r with (IZR (Zpos y')) ;
    (try now apply IZR_lt) ;
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r, <- mult_IZR ;
    (try now apply IZR_neq) ;
    apply IZR_lt.
  clear -H2 Hr ; omega.
  rewrite Zmult_plus_distr_l.
  clear -H2 ; omega.
  rewrite H1, 2!plus_IZR, mult_IZR.
  destruct (Z.compare_spec (r' * 2) (Zpos y')) as [H|H|H].
  + apply Rcompare_Eq.
    rewrite <- H.
    rewrite mult_IZR.
    field.
    now apply IZR_neq.
  + apply Rcompare_Lt.
    apply Rminus_gt.
    match goal with |- (?a > 0)%R => replace a with ((IZR (Zpos y') - IZR r' * 2) / (2 * IZR (Zpos y')))%R end.
    apply Fourier_util.Rlt_mult_inv_pos.
    apply Rgt_minus.
    rewrite <- mult_IZR.
    now apply IZR_lt.
    apply Rmult_lt_0_compat.
    apply Rlt_0_2.
    now apply IZR_lt.
    field.
    now apply IZR_neq.
  + apply Rcompare_Gt.
    apply Rminus_lt.
    match goal with |- (?a < 0)%R => replace a with (- ((IZR r' * 2 - IZR (Zpos y')) / (2 * IZR (Zpos y'))))%R end.
    apply Ropp_lt_gt_0_contravar.
    apply Fourier_util.Rlt_mult_inv_pos.
    apply Rgt_minus.
    rewrite <- mult_IZR.
    now apply IZR_lt.
    apply Rmult_lt_0_compat.
    apply Rlt_0_2.
    now apply IZR_lt.
    field.
    now apply IZR_neq.
Qed.

Lemma mantissa_sqrt_correct :
  forall x, valid_mantissa x ->
  let (q,l) := mantissa_sqrt x in
  let (s,r) := Z.sqrtrem (Zpos (MtoP x)) in
  Zpos (MtoP q) = s /\
  match l with pos_Eq => r = Z0 | pos_Lo => (0 < r <= s)%Z | pos_Mi => False | pos_Up => (s < r)%Z end /\
  valid_mantissa q.
Proof.
intros x [x' Vx].
unfold mantissa_sqrt, MtoP.
rewrite BigN.spec_eqb.
rewrite BigN.spec_compare.
rewrite BigN.spec_sub.
rewrite BigN.spec_square.
rewrite BigN.spec_sqrt.
rewrite <- Z.sqrtrem_sqrt.
refine (_ (Z.sqrtrem_spec (Zpos x') _)).
2: easy.
rewrite Vx.
case_eq (Z.sqrtrem (Zpos x')).
intros s r Hsr.
simpl fst.
intros [H1 H2].
refine ((fun H => conj (proj1 H) (conj _ (proj2 H))) _).
clear H.
rewrite H1.
replace (s * s + r - s * s)%Z with r by ring.
rewrite Zmax_right by easy.
change [0]%bigN with Z0.
case Z.eqb_spec.
easy.
intros H.
assert (H3: (0 < r)%Z) by omega.
case Z.compare_spec ; intros H4.
apply (conj H3).
now rewrite H4.
apply (conj H3).
now apply Z.lt_le_incl.
exact H4.
destruct s as [ |s|s].
simpl in H1.
rewrite <- H1 in H2.
now elim (proj2 H2).
split.
apply eq_refl.
exists s.
rewrite BigN.spec_sqrt.
rewrite <- Z.sqrtrem_sqrt.
now rewrite Vx, Hsr.
now elim (Z.le_trans _ _ _ (proj1 H2) (proj2 H2)).
Qed.

End BigIntRadix2.
