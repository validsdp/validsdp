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

Require Import Reals.
Require Import Bool.
Require Import ZArith.
From Flocq Require Import Core Digits Bracket Round Operations.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Psatz.
Import ssrbool.

Lemma FtoR_Rpos :
  forall beta m e,
  (0 < FtoR beta false m e)%R.
Proof.
intros beta m e.
rewrite FtoR_split.
now apply F2R_gt_0.
Qed.

Lemma FtoR_neg :
  forall beta s m e,
  (- FtoR beta s m e = FtoR beta (negb s) m e)%R.
Proof.
intros beta s m e.
rewrite 2!FtoR_split.
rewrite <- F2R_opp.
now case s.
Qed.

Lemma FtoR_Rneg :
  forall beta m e,
  (FtoR beta true m e < 0)%R.
Proof.
intros beta m e.
rewrite FtoR_split.
now apply F2R_lt_0.
Qed.

Lemma FtoR_abs :
  forall beta s m e,
  (Rabs (FtoR beta s m e) = FtoR beta false m e)%R.
Proof.
intros beta s m e.
rewrite 2!FtoR_split, <- F2R_abs.
now case s.
Qed.

Lemma FtoR_add :
  forall beta s m1 m2 e,
  (FtoR beta s m1 e + FtoR beta s m2 e)%R = FtoR beta s (m1 + m2) e.
Proof.
intros beta s m1 m2 e.
rewrite 3!FtoR_split.
unfold F2R. simpl.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
now case s.
Qed.

Lemma FtoR_sub :
  forall beta s m1 m2 e,
  (Zpos m2 < Zpos m1)%Z ->
  (FtoR beta s m1 e + FtoR beta (negb s) m2 e)%R = FtoR beta s (m1 - m2) e.
Proof.
intros beta s m1 m2 e Hm.
rewrite 3!FtoR_split.
unfold F2R. simpl.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
case s ; simpl.
rewrite (Z.pos_sub_spec m2 m1).
unfold Zlt in Hm ; simpl in Hm.
now rewrite Hm.
generalize (Zlt_gt _ _ Hm).
unfold Zgt. simpl.
intros H.
now rewrite (Z.pos_sub_spec m1 m2), H.
Qed.

Lemma FtoR_mul :
  forall beta s1 s2 m1 m2 e1 e2,
  (FtoR beta s1 m1 e1 * FtoR beta s2 m2 e2)%R =
  FtoR beta (xorb s1 s2) (m1 * m2) (e1 + e2).
Proof.
intros beta s1 s2 m1 m2 e1 e2.
rewrite 3!FtoR_split.
unfold F2R. simpl.
rewrite bpow_plus.
case s1 ; case s2 ; simpl ;
  rewrite <- Rmult_assoc, (Rmult_comm (IZR _)), (Rmult_assoc _ _ (IZR _)), <- mult_IZR ;
  simpl ; ring.
Qed.

Lemma shift_correct :
  forall beta m e,
  Zpos (shift beta m e) = (Zpos m * Zpower_pos beta e)%Z.
Proof.
intros beta m e.
rewrite Z.pow_pos_fold.
unfold shift.
set (r := match radix_val beta with Zpos r => r | _ => xH end).
rewrite iter_pos_nat.
rewrite Zpower_Zpower_nat by easy.
simpl Zabs_nat.
induction (nat_of_P e).
simpl.
now rewrite Pmult_comm.
rewrite iter_nat_S, Zpower_nat_S.
rewrite Zpos_mult_morphism.
rewrite IHn.
replace (Zpos r) with (radix_val beta).
ring.
unfold r.
generalize (radix_val beta) (radix_prop beta).
clear.
now intros [|p|p].
Qed.

Lemma FtoR_shift :
  forall beta s m e p,
  FtoR beta s m (e + Zpos p) = FtoR beta s (shift beta m p) e.
Proof.
intros beta s m e p.
rewrite 2!FtoR_split.
rewrite shift_correct.
rewrite F2R_change_exp with (e' := e).
ring_simplify (e + Zpos p - e)%Z.
case s ; unfold cond_Zopp.
now rewrite Zopp_mult_distr_l_reverse.
apply refl_equal.
pattern e at 1 ; rewrite <- Zplus_0_r.
now apply Zplus_le_compat_l.
Qed.

Lemma digits_conversion :
  forall beta p,
  Zdigits beta (Zpos p) = Zpos (count_digits beta p).
Proof.
intros beta p.
unfold Zdigits, count_digits.
generalize xH, (radix_val beta), p at 1 3.
induction p ; simpl ; intros.
case (Zlt_bool (Zpos p1) z).
apply refl_equal.
rewrite <- IHp.
now rewrite Pplus_one_succ_r.
case (Zlt_bool (Zpos p1) z).
apply refl_equal.
rewrite <- IHp.
now rewrite Pplus_one_succ_r.
now case (Zlt_bool (Zpos p0) z).
Qed.

(*
 * Fneg
 *)

Theorem Fneg_correct :
  forall beta (f : float beta),
  FtoX (Fneg f) = Xneg (FtoX f).
Proof.
intros.
case f ; intros.
apply refl_equal.
simpl.
rewrite Ropp_0.
apply refl_equal.
simpl.
rewrite FtoR_neg.
apply refl_equal.
Qed.

(*
 * Fabs
 *)

Theorem Fabs_correct :
  forall beta (f : float beta),
  FtoX (Fabs f) = Xabs (FtoX f).
Proof.
intros.
case f ; intros.
apply refl_equal.
simpl.
rewrite Rabs_R0.
apply refl_equal.
simpl.
rewrite FtoR_abs.
apply refl_equal.
Qed.

(*
 * Fscale
 *)

Theorem Fscale_correct :
  forall beta (f : float beta) d,
  FtoX (Fscale f d) = Xmul (FtoX f) (Xreal (bpow beta d)).
Proof.
intros beta [| |s m e] d ; simpl.
apply refl_equal.
now rewrite Rmult_0_l.
rewrite 2!FtoR_split.
unfold F2R. simpl.
rewrite Rmult_assoc.
now rewrite bpow_plus.
Qed.

(*
 * Fscale2
 *)

Lemma cond_Zopp_mult :
  forall s u v,
  cond_Zopp s (u * v) = (cond_Zopp s u * v)%Z.
Proof.
intros s u v.
case s.
apply sym_eq.
apply Zopp_mult_distr_l_reverse.
apply refl_equal.
Qed.

Theorem Fscale2_correct :
  forall beta (f : float beta) d,
  match radix_val beta with Zpos (xO _) => true | _ => false end = true ->
  FtoX (Fscale2 f d) = Xmul (FtoX f) (Xreal (bpow radix2 d)).
Proof.
intros beta [| |s m e] d Hb ; simpl.
apply refl_equal.
now rewrite Rmult_0_l.
revert Hb.
destruct beta as (beta, Hb). simpl.
destruct beta as [|[p|p|]|p] ; try easy.
intros _.
set (beta := Build_radix (Zpos p~0) Hb).
cut (FtoX
  match d return (float beta) with
  | 0%Z => Float s m e
  | Zpos nb =>
      Float s (iter_pos (fun x : positive => xO x) nb m) e
  | Zneg nb =>
      Float s (iter_pos (fun x : positive => Pmult p x) nb m) (e + d)
  end = Xreal (FtoR beta s m e * bpow radix2 d)).
(* *)
intro H.
destruct p as [p|p|] ; try exact H.
unfold FtoX.
rewrite 2!FtoR_split.
unfold F2R. simpl.
now rewrite bpow_plus, Rmult_assoc.
(* *)
destruct d as [|nb|nb].
now rewrite Rmult_1_r.
(* . *)
unfold FtoX.
apply f_equal.
rewrite 2!FtoR_split.
simpl.
replace (IZR (Zpower_pos 2 nb)) with (F2R (Defs.Float beta (Zpower_pos 2 nb) 0)).
2: apply Rmult_1_r.
rewrite <- F2R_mult.
simpl.
rewrite Zplus_0_r.
rewrite <- cond_Zopp_mult.
apply (f_equal (fun v => F2R (Defs.Float beta (cond_Zopp s v) e))).
apply (shift_correct radix2).
(* . *)
unfold FtoX.
apply f_equal.
rewrite 2!FtoR_split.
apply Rmult_eq_reg_r with (bpow radix2 (Zpos nb)).
2: apply Rgt_not_eq ; apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus.
change (Zneg nb) with (Zopp (Zpos nb)).
rewrite Zplus_opp_l, Rmult_1_r.
fold (e - Zpos nb)%Z.
simpl.
replace (IZR (Zpower_pos 2 nb)) with (F2R (Defs.Float beta (Zpower_pos 2 nb) 0)).
2: apply Rmult_1_r.
rewrite <- F2R_mult.
simpl.
rewrite Zplus_0_r.
rewrite (F2R_change_exp beta (e - Zpos nb) _ e).
2: generalize (Zgt_pos_0 nb) ; omega.
ring_simplify (e - (e - Zpos nb))%Z.
rewrite <- 2!cond_Zopp_mult.
apply (f_equal (fun v => F2R (Defs.Float beta (cond_Zopp s v) _))).
rewrite Z.pow_pos_fold.
rewrite iter_pos_nat.
rewrite 2!Zpower_Zpower_nat by easy.
simpl Zabs_nat.
unfold beta.
simpl radix_val.
clear.
revert m.
induction (nat_of_P nb).
easy.
intros m.
rewrite iter_nat_S, 2!Zpower_nat_S.
rewrite Zpos_mult_morphism.
replace (Zpos m * (Zpos (xO p) * Zpower_nat (Zpos (xO p)) n))%Z with (Zpos m * Zpower_nat (Zpos (xO p)) n * Zpos (xO p))%Z by ring.
rewrite <- IHn.
change (Zpos (xO p)) with (2 * Zpos p)%Z.
ring.
Qed.

(*
 * Fcmp
 *)

Lemma Fcmp_aux2_correct :
  forall beta m1 m2 e1 e2,
  Fcmp_aux2 beta m1 e1 m2 e2 =
  Xcmp (Xreal (FtoR beta false m1 e1)) (Xreal (FtoR beta false m2 e2)).
Proof.
intros beta m1 m2 e1 e2.
rewrite 2!FtoR_split.
simpl cond_Zopp.
unfold  Fcmp_aux2, Xcmp.
rewrite <- 2!digits_conversion.
rewrite (Zplus_comm e1), (Zplus_comm e2).
rewrite <- 2!mag_F2R_Zdigits ; [|easy..].
destruct (mag beta (F2R (Defs.Float beta (Zpos m1) e1))) as (b1, B1).
destruct (mag beta (F2R (Defs.Float beta (Zpos m2) e2))) as (b2, B2).
simpl.
assert (Z: forall m e, (0 < F2R (Defs.Float beta (Zpos m) e))%R).
intros m e.
now apply F2R_gt_0.
specialize (B1 (Rgt_not_eq _ _ (Z _ _))).
specialize (B2 (Rgt_not_eq _ _ (Z _ _))).
rewrite Rabs_pos_eq with (1 := Rlt_le _ _ (Z _ _)) in B1.
rewrite Rabs_pos_eq with (1 := Rlt_le _ _ (Z _ _)) in B2.
clear Z.
case Zcompare_spec ; intros Hed.
(* *)
rewrite Rcompare_Lt.
apply refl_equal.
apply Rlt_le_trans with (1 := proj2 B1).
apply Rle_trans with (2 := proj1 B2).
apply bpow_le.
clear -Hed. omega.
(* *)
clear.
unfold Fcmp_aux1.
case_eq (e1 - e2)%Z.
(* . *)
intros He.
rewrite Zminus_eq with (1 := He).
now rewrite Rcompare_F2R.
(* . *)
intros d He.
rewrite F2R_change_exp with (e' := e2).
rewrite shift_correct, He.
now rewrite Rcompare_F2R.
generalize (Zgt_pos_0 d).
omega.
(* . *)
intros d He.
rewrite F2R_change_exp with (e := e2) (e' := e1).
replace (e2 - e1)%Z with (Zpos d).
rewrite shift_correct.
now rewrite Rcompare_F2R.
apply Zopp_inj.
simpl. rewrite <- He.
ring.
generalize (Zlt_neg_0 d).
omega.
(* *)
rewrite Rcompare_Gt.
apply refl_equal.
apply Rlt_le_trans with (1 := proj2 B2).
apply Rle_trans with (2 := proj1 B1).
apply bpow_le.
clear -Hed. omega.
Qed.

Theorem Fcmp_correct :
  forall beta (x y : float beta),
  Fcmp x y = Xcmp (FtoX x) (FtoX y).
Proof.
intros.
case x ; intros ; simpl ; try apply refl_equal ;
  case y ; intros ; simpl ; try apply refl_equal ; clear.
now rewrite Rcompare_Eq.
case b.
rewrite Rcompare_Gt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_Lt.
apply refl_equal.
apply FtoR_Rpos.
case b ; apply refl_equal.
case b.
rewrite Rcompare_Lt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_Gt.
apply refl_equal.
apply FtoR_Rpos.
case b ; case b0.
rewrite Fcmp_aux2_correct.
simpl.
change true with (negb false).
repeat rewrite <- FtoR_neg.
generalize (FtoR beta false p0 z0).
generalize (FtoR beta false p z).
intros.
destruct (Rcompare_spec r0 r).
rewrite Rcompare_Lt.
apply refl_equal.
now apply Ropp_lt_contravar.
rewrite H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
apply refl_equal.
apply Ropp_lt_contravar.
exact H.
rewrite Rcompare_Lt.
apply refl_equal.
apply Rlt_trans with R0.
apply FtoR_Rneg.
apply FtoR_Rpos.
rewrite Rcompare_Gt.
apply refl_equal.
apply Rlt_trans with R0.
apply FtoR_Rneg.
apply FtoR_Rpos.
rewrite Fcmp_aux2_correct.
apply refl_equal.
Qed.

(*
 * Fmin
 *)

Theorem Fmin_correct :
  forall beta (x y : float beta),
  FtoX (Fmin x y) = Xmin (FtoX x) (FtoX y).
Proof.
intros.
unfold Fmin, Rmin.
rewrite (Fcmp_correct beta x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_Lt.
exact Hx.
exact H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
exact Hy.
apply Rnot_le_lt with (1 := H).
Qed.

(*
 * Fmax
 *)

Theorem Fmax_correct :
  forall beta (x y : float beta),
  FtoX (Fmax x y) = Xmax (FtoX x) (FtoX y).
Proof.
intros.
unfold Fmax, Rmax.
rewrite (Fcmp_correct beta x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_Lt.
exact Hy.
exact H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
exact Hx.
apply Rnot_le_lt with (1 := H).
Qed.

Ltac refl_exists :=
  repeat match goal with
  | |- ex ?P => eapply ex_intro
  end ;
  repeat split.

Definition normalize beta prec m e :=
  match (Zpos (count_digits beta m) - Zpos prec)%Z with
  | Zneg nb => ((shift beta m nb), (e + Zneg nb)%Z)
  | _ => (m, e)
  end.

Lemma normalize_identity :
  forall beta prec m e,
  (Zpos prec <= Zpos (count_digits beta m))%Z ->
  normalize beta prec m e = (m, e).
Proof.
intros beta prec m e.
unfold Zle, normalize.
rewrite <- (Zcompare_plus_compat _ _ (- Zpos prec)).
rewrite Zplus_opp_l, Zplus_comm.
unfold Zminus.
case Zplus ; [easy|easy|].
intros p H.
now elim H.
Qed.

Definition convert_location_inv l :=
  match l with
  | pos_Eq => loc_Exact
  | pos_Lo => loc_Inexact Lt
  | pos_Mi => loc_Inexact Eq
  | pos_Up => loc_Inexact Gt
  end.

Lemma convert_location_bij :
  forall l, convert_location_inv (convert_location l) = l.
Proof.
now destruct l as [|[| |]].
Qed.

Definition mode_choice mode s m l :=
  match mode with
  | rnd_UP => cond_incr (round_sign_UP s l) m
  | rnd_DN => cond_incr (round_sign_DN s l) m
  | rnd_ZR => m
  | rnd_NE => cond_incr (round_N (negb (Z.even m)) l) m
  end.

Lemma adjust_mantissa_correct :
  forall mode s m pos,
  Zpos (adjust_mantissa mode m pos s) = mode_choice mode s (Zpos m) (convert_location_inv pos).
Proof.
intros mode s m pos.
unfold adjust_mantissa, need_change, mode_choice.
case mode ; case s ; case pos ; simpl ; try apply Zpos_succ_morphism ; try apply refl_equal.
destruct m ;  try apply Zpos_succ_morphism ; try apply refl_equal.
destruct m ;  try apply Zpos_succ_morphism ; try apply refl_equal.
Qed.

Lemma adjust_pos_correct :
  forall q r pos,
  (1 < Zpos q)%Z ->
  (0 <= r < Zpos q)%Z ->
  convert_location_inv (adjust_pos r q pos) = new_location (Zpos q) r (convert_location_inv pos).
Proof.
unfold adjust_pos, new_location, new_location_even, new_location_odd.
intros [q|q|] r pos Hq (Hr1, Hr2).
destruct r as [|r|r] ; simpl.
now case pos.
change (r~1 ?= q~1)%positive with (r ?= q)%positive.
now case ((r ?= q)%positive) ; case pos ; simpl.
unfold Zeven.
now elim Hr1.
destruct r as [|r|r] ; simpl.
now case pos.
change (r~0 ?= q~0)%positive with (r ?= q)%positive.
now case ((r ?= q)%positive) ; case pos.
now elim Hr1.
discriminate Hq.
Qed.

Lemma even_radix_correct :
  forall beta,
  match radix_val beta with Zpos (xO _) => true | _ => false end = Z.even beta.
Proof.
intros (beta, Hb).
revert Hb.
case beta ; try easy.
Qed.

Lemma odd_radix_correct :
  forall beta,
  match radix_val beta with Zpos (xO _) => false | _ => true end = negb (Z.even beta).
Proof.
intros (beta, Hb).
revert Hb.
case beta ; try easy.
now intros [p|p|].
Qed.

Lemma Fround_at_prec_correct :
  forall beta mode prec s m1 e1 pos x,
  (0 < x)%R ->
  ( let (m2, e2) := normalize beta prec m1 e1 in
    inbetween_float beta (Zpos m2) e2 x (convert_location_inv pos) ) ->
  FtoX (Fround_at_prec mode prec (@Ufloat beta s m1 e1 pos)) =
    Xreal (round beta mode prec (if s then Ropp x else x)).
Proof with auto with typeclass_instances.
intros beta mode prec s m1 e1 pos x Hx.
case_eq (normalize beta prec m1 e1).
intros m2 e2 Hn Hl.
unfold round.
rewrite round_trunc_sign_any_correct with (choice := mode_choice mode) (m := Zpos m2) (e := e2) (l := convert_location_inv pos)...
(* *)
unfold Round.truncate, Round.truncate_aux, FLX_exp.
replace (Zdigits beta (Zpos m2) + e2 - Zpos prec - e2)%Z with (Zdigits beta (Zpos m2) - Zpos prec)%Z by ring.
replace (Rlt_bool (if s then (-x)%R else x) 0) with s.
revert Hn.
unfold Fround_at_prec, normalize.
case_eq (Zpos (count_digits beta m1) - Zpos prec)%Z.
(* . *)
intros Hd Heq.
injection Heq.
intros He Hm. clear Heq.
apply (f_equal Xreal).
rewrite FtoR_split.
rewrite adjust_mantissa_correct.
rewrite <- Hm, digits_conversion, Hd.
simpl.
now rewrite He.
(* . *)
intros d Hd Heq.
injection Heq.
intros He Hm. clear Heq.
rewrite <- Hm, digits_conversion, Hd.
rewrite shift_correct, Zmult_1_l.
fold (Zpower beta (Zpos d)).
unfold Zdiv, Zmod.
assert (Zpower beta (Zpos d) > 0)%Z.
apply Zlt_gt.
now apply Zpower_gt_0.
generalize (Z_div_mod (Zpos m1) (Zpower beta (Zpos d)) H).
clear H.
case Zdiv_eucl. intros q r (Hq, Hr).
rewrite He.
cut (0 < q)%Z.
(* .. *)
clear -Hr.
case q ; try easy.
clear q. intros q _.
apply (f_equal Xreal).
rewrite FtoR_split.
rewrite adjust_mantissa_correct.
simpl.
apply (f_equal (fun v => F2R (Defs.Float beta (cond_Zopp s (mode_choice mode s (Zpos q) v)) (e2 + Zpos d)))).
rewrite <- (Zmult_1_l (Zpower_pos beta d)).
rewrite <- shift_correct.
apply adjust_pos_correct ; rewrite shift_correct, Zmult_1_l.
now apply (Zpower_gt_1 beta (Zpos d)).
exact Hr.
(* .. *)
clear -Hd Hq Hr.
apply Zmult_lt_reg_r with (Zpower beta (Zpos d)).
now apply Zpower_gt_0.
apply Zplus_lt_reg_r with r.
simpl (0 * Zpower beta (Zpos d) + r)%Z.
rewrite Zmult_comm, <- Hq.
apply Zlt_le_trans with (1 := proj2 Hr).
fold (Zabs (Zpos m1)).
apply Zpower_le_Zdigits.
rewrite <- Hd.
rewrite <- digits_conversion.
now apply Zlt_minus_simpl_swap.
(* . *)
intros d Hd Heq.
injection Heq.
intros He Hm. clear Heq.
rewrite <- Hm.
rewrite shift_correct.
fold (Zpower beta (Zpos d)).
rewrite Zdigits_mult_Zpower ; try easy.
replace (Zdigits beta (Zpos m1) + Zpos d - Zpos prec)%Z with Z0.
simpl.
change (match Zpower_pos beta d with 0 => 0 | Zpos y1 => Zpos (m1 * y1) | Zneg y2 => Zneg (m1 * y2) end)%Z
  with (Zpos m1 * Zpower beta (Zpos d))%Z.
assert (forall A B : Type, forall f : A -> B, forall b : bool, forall v1 v2 : A, f (if b then v1 else v2) = if b then f v1 else f v2).
clear. now intros A B f [|].
rewrite (H (float beta) ExtendedR).
simpl FtoX.
rewrite 2!FtoR_split.
rewrite Zpos_succ_morphism, shift_correct.
rewrite (F2R_change_exp beta (e1 + Zneg d)%Z (cond_Zopp s (Zpos m1)) e1).
ring_simplify (e1 - (e1 + Zneg d))%Z.
replace (cond_Zopp s (Zpos m1) * beta ^ (- Zneg d))%Z with (cond_Zopp s (Zpos m1 * Zpower_pos beta d)).
rewrite <- (H Z ExtendedR (fun v => Xreal (F2R (Defs.Float beta (cond_Zopp s v) (e1 + Zneg d))))).
rewrite <- He.
apply (f_equal (fun v => Xreal (F2R (Defs.Float beta (cond_Zopp s v) (e1 + Zneg d))))).
clear.
unfold mode_choice, need_change_radix.
case mode ; case pos ; try easy.
rewrite Z.even_mul, Z.even_pow by easy.
unfold need_change_radix2.
rewrite even_radix_correct.
now case m1.
unfold cond_Zopp.
rewrite <- Zopp_mult_distr_l_reverse.
now case s.
pattern e1 at 2 ; rewrite <- Zplus_0_r.
now apply Zplus_le_compat_l.
change (Zpos d) with (Zopp (Zneg d)).
rewrite <- Hd.
rewrite digits_conversion.
ring.
(* .*)
clear -Hx.
apply sym_eq.
case s.
apply Rlt_bool_true.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
apply Rlt_bool_false.
now apply Rlt_le.
(* *)
clear.
intros x m l Hx.
case mode ; simpl.
now apply inbetween_int_UP_sign.
now apply inbetween_int_DN_sign.
now apply inbetween_int_ZR_sign with (l := l).
now apply inbetween_int_NE_sign with (x := x).
(* *)
case s.
rewrite Rabs_Ropp, Rabs_pos_eq.
exact Hl.
now apply Rlt_le.
rewrite Rabs_pos_eq.
exact Hl.
now apply Rlt_le.
(* *)
left.
unfold FLX_exp.
cut (0 <= Zdigits beta (Zpos m2) - Zpos prec)%Z. clear. omega.
change m2 with (fst (m2, e2)).
rewrite <- (f_equal (@fst _ _) Hn).
clear.
unfold normalize.
rewrite <- digits_conversion.
case_eq (Zdigits beta (Zpos m1) - Zpos prec)%Z ; unfold fst.
intros H.
now rewrite H.
intros p H.
now rewrite H.
intros p H.
rewrite shift_correct.
fold (Zpower beta (Zpos p)).
rewrite Zdigits_mult_Zpower ; try easy.
fold (Zopp (Zneg p)).
rewrite <- H.
now ring_simplify.
Qed.

Lemma normalize_correct :
  forall beta prec m e,
  F2R (Defs.Float beta (Zpos m) e) =
    let (m', e') := normalize beta prec m e in F2R (Defs.Float beta (Zpos m') e').
Proof.
intros beta prec m e.
unfold normalize.
case (Zpos (count_digits beta m) - Zpos prec)%Z ; intros ; try apply refl_equal.
rewrite shift_correct.
unfold F2R, Fnum, Fexp.
rewrite mult_IZR, Rmult_assoc.
apply f_equal.
rewrite IZR_Zpower_pos, <- bpow_powerRZ.
rewrite <- bpow_plus.
apply f_equal.
change (Zneg p) with (Zopp (Zpos p)).
ring.
Qed.

Definition ufloat_pos_Eq beta (x : ufloat beta) :=
  match x with Ufloat _ _ _ pos_Eq => True | Ufloat _ _ _ _ => False | _ => True end.

Lemma UtoX_pos_Eq :
  forall beta (x : ufloat beta),
  (UtoX x = Xnan -> x = Unan) ->
  ufloat_pos_Eq beta x.
Proof.
now intros beta [| |s m e [| | |]] H ; try exact I ; specialize (H (refl_equal _)).
Qed.

Lemma Fround_at_prec_pos_Eq :
  forall beta mode prec (x : ufloat beta),
  ufloat_pos_Eq beta x ->
  FtoX (Fround_at_prec mode prec x) = Xround beta mode prec (UtoX x).
Proof with auto with typeclass_instances.
intros beta mode prec [| |s m e [| | |]] H ; try elim H ; clear H.
apply refl_equal.
simpl. unfold round.
rewrite round_0...
unfold Xround, UtoX.
rewrite FtoR_split.
replace (F2R (Defs.Float beta (cond_Zopp s (Zpos m)) e)) with
  (if s then Ropp (F2R (Defs.Float beta (Zpos m) e)) else F2R (Defs.Float beta (Zpos m) e)).
apply Fround_at_prec_correct.
now apply F2R_gt_0.
unfold inbetween_float.
rewrite (normalize_correct beta prec m e).
destruct (normalize beta prec m e) as (m', e').
now constructor.
rewrite <- F2R_opp.
now case s.
Qed.

(*
 * Fnearbyint_exact
 *)

Lemma Rdiv_lt_mult_pos a b c :
 (0 < b -> a * b  < c -> a < c / b)%R.
Proof.
intros Hb Hab.
apply (Rmult_lt_reg_r b _ _ Hb).
now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_le_mult_pos a b c :
 (0 < b -> a * b  <= c -> a <= c / b)%R.
Proof.
intros Hb Hab.
apply (Rmult_le_reg_r b _ _ Hb).
now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_gt_mult_pos a b c :
 (0 < b -> a < b * c -> a / b < c)%R.
Proof.
intros Hb Hab.
apply (Rmult_lt_reg_r b _ _ Hb).
now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Rdiv_ge_mult_pos a b c :
 (0 < b -> a <= b * c -> a / b <= c)%R.
Proof.
intros Hb Hab.
apply (Rmult_le_reg_r b _ _ Hb).
now unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra.
Qed.

Lemma Znearest_IZR c z : Znearest c (IZR z) = z.
Proof.
unfold Znearest; rewrite Zceil_IZR, Zfloor_IZR.
now destruct Rcompare; try easy; destruct c.
Qed.

Lemma Rnearbyint_IZR mode z : Rnearbyint mode (IZR z) = IZR z.
Proof.
now destruct mode; simpl; rewrite ?Zceil_IZR, ?Zfloor_IZR, ?Ztrunc_IZR, ?Znearest_IZR.
Qed.

Lemma adjust_mantissa_Eq mode b p : adjust_mantissa mode p pos_Eq b = p.
Proof. now destruct mode. Qed.

Lemma need_change_radix2_Eq beta mode p b :
  need_change_radix2 beta mode p pos_Eq b = false.
Proof. now destruct mode; simpl. Qed.

Lemma radix_to_pos (r : radix) : Z.pos (Z.to_pos r) = r.
Proof.  now destruct r as [[]]. Qed.

Lemma shift1_correct r e :
  shift r 1 e =  (Z.to_pos r ^ e)%positive.
Proof.
generalize (shift_correct r 1 e).
rewrite Zmult_1_l, <-(radix_to_pos r) at 1.
rewrite <-Pos2Z.inj_pow_pos.
now intro H; injection H.
Qed.

Lemma Rcompare_div_l x y z :
  (0 < y)%R -> Rcompare (x / y) z = Rcompare x (y * z).
Proof.
intro yP.
replace x with (y * (x / y))%R at 2.
  now rewrite Rcompare_mult_l.
field; lra.
Qed.

Lemma Rcompare_div_r x y z :
  (0 < z)%R -> Rcompare x (y / z) = Rcompare (z * x) y.
Proof.
intro yP.
rewrite Rcompare_sym, Rcompare_div_l, Rcompare_sym; try easy.
  now destruct Rcompare.
Qed.

Lemma Rlt_bool_float beta b m e : Rlt_bool (FtoR beta b m e) 0 = b.
Proof.
destruct e as [|p | p]; destruct b; simpl;
  apply  Rlt_bool_true || apply Rlt_bool_false; try lra.
- now apply IZR_lt.
- now apply IZR_le.
- assert (H1 : (0 < Z.pow_pos beta p)%Z).
    apply Zpower_pos_gt_0; apply radix_gt_0.
  revert H1.
  destruct Z.pow_pos; simpl; try lia; intros _.
  now apply IZR_lt.
- assert (H1 : (0 < Z.pow_pos beta p)%Z).
    apply Zpower_pos_gt_0; apply radix_gt_0.
  revert H1.
  destruct Z.pow_pos; simpl; try lia; intros _.
  now apply IZR_le.
- apply Rdiv_gt_mult_pos.
  apply IZR_lt.
  apply Zpower_pos_gt_0; apply radix_gt_0.
  rewrite Rmult_0_r.
  now apply IZR_lt.
- apply Rdiv_le_mult_pos.
  apply IZR_lt.
  apply Zpower_pos_gt_0; apply radix_gt_0.
  rewrite Rmult_0_l.
  now apply IZR_le.
Qed.

Lemma Fnearbyint_exact_correct :
  forall beta mode (x : float beta),
  FtoX (Fnearbyint_exact mode x) = Xnearbyint mode (FtoX x).
Proof.
intros beta mode x.
assert (bP := Zle_bool_imp_le _ _ (radix_prop beta)).
unfold Fnearbyint_exact, Fround_at_exp.
destruct x as [| |b p z]; simpl float_to_ufloat; lazy iota beta; try easy.
  now generalize (Rnearbyint_IZR mode 0); simpl; intro H; rewrite H.
destruct z as [| p1 | n1]; simpl Zminus; lazy iota beta.
- now rewrite adjust_mantissa_Eq; simpl; rewrite Rnearbyint_IZR.
- now simpl; rewrite need_change_radix2_Eq, Rnearbyint_IZR.
rewrite <-digits_conversion, shift1_correct.
case Z.compare_spec; intro H.
(* *)
set (x := Float b p _).
set (p1 := adjust_pos _ _ _).
pose (y := (FtoR beta b p (Z.neg n1))).
apply trans_equal with (y :=
 Xreal (IZR
 (cond_Zopp (Rlt_bool y 0)
      (mode_choice mode (Rlt_bool y 0)
                    0  (convert_location_inv p1))))).
  unfold y; rewrite Rlt_bool_float.
  now destruct b; destruct mode; simpl; destruct p1.
apply (f_equal Xreal).
apply sym_equal.
assert (V : (1 < beta ^ Z.pos n1)%Z) by now apply Zpower_gt_1.
assert (V0 : (1 < IZR (beta ^ Z.pos n1))%R) by now apply IZR_lt.
assert (V1 : (Z.pos p < beta ^ Z.pos n1)%Z).
  generalize (Zdigits_correct beta (Z.pos p)).
  now rewrite H; intros [_ V3].
assert (V2 : inbetween_int 0 (Rabs y) (convert_location_inv p1)).
  unfold p1, inbetween_int.
  rewrite adjust_pos_correct; try lia; last 2 first.
  - now rewrite Pos2Z.inj_pow, radix_to_pos.
  - now rewrite Pos2Z.inj_pow, radix_to_pos; lia.
  simpl; unfold y, p1;  rewrite FtoR_abs.
  rewrite Pos2Z.inj_pow, radix_to_pos.
  replace  1%R
    with
    (0 +
      IZR (beta ^ Z.pos n1)* (1 / IZR (beta ^ Z.pos n1)))%R; last first.
    field; last now apply Rlt_neq_sym; lra.
  apply new_location_correct; try lia.
  - apply Rdiv_lt_0_compat; try lra.
  apply inbetween_Exact.
  simpl.
  rewrite Z.pow_pos_fold.
  now field; lra.
destruct mode; apply (f_equal IZR).
- now eapply inbetween_int_UP_sign.
- now eapply inbetween_int_DN_sign.
- now eapply inbetween_int_ZR_sign with (l := (convert_location_inv p1)).
- now eapply inbetween_int_NE_sign.
(* *)
set (x := Float b p _).
set (p1 := pos_Lo).
pose (y := (FtoR beta b p (Z.neg n1))).
apply trans_equal with (y :=
 Xreal (IZR
 (cond_Zopp (Rlt_bool y 0)
      (mode_choice mode (Rlt_bool y 0)
                    0  (convert_location_inv p1))))).
  unfold y; rewrite Rlt_bool_float.
  now destruct b; destruct mode; simpl; destruct p1.
apply (f_equal Xreal).
apply sym_equal.
assert (0 < IZR (Zpos p))%R as V by now apply IZR_lt.
assert (V0 : (1 < beta ^ Z.pos n1)%Z) by now apply Zpower_gt_1.
assert (V1 : (1 < IZR (beta ^ Z.pos n1))%R) by now apply IZR_lt.
assert (V2 : (Z.pos p < beta ^ Z.pos n1)%Z).
  generalize (Zdigits_correct beta (Z.pos p)).
  intros [_ V2].
  apply Zlt_trans with (1 := V2).
  apply Zpower_lt; lia.
assert (V3 : inbetween_int 0 (Rabs y) (convert_location_inv p1)).
  unfold y, p1, inbetween_int.
  rewrite FtoR_abs.
  apply inbetween_Inexact; simpl; rewrite Z.pow_pos_fold.
  - split; try lra.
    - apply Rdiv_lt_0_compat; lra.
    - apply Rdiv_gt_mult_pos; try lra.
      rewrite Rmult_1_r; apply IZR_lt; lia.
  - rewrite Rcompare_div_l; try lra.
    replace (IZR (beta ^ Z.pos n1) * ((0 + 1) / 2))%R with
            (IZR (beta ^ Z.pos n1) / 2)%R; last first.
      now unfold Rdiv; ring.
    rewrite Rcompare_div_r; try lra.
    rewrite <- (mult_IZR 2).
    rewrite Rcompare_IZR.
    apply Zcompare_Lt; apply Zgt_lt.
    apply Zgt_le_trans with (m := (beta * Z.pos p)%Z); last first.
      now apply Zmult_le_compat_r; lia.
    apply Zle_gt_trans with (m := (beta ^ (1 + Zdigits beta (Z.pos p)))%Z).
      now apply Zpower_le; lia.
    rewrite Zpower_plus, Z.pow_1_r; try lia; last first.
      now apply Zdigits_ge_0.
    apply Zmult_gt_compat_l; try lia.
    generalize (Zdigits_correct beta (Z.pos p)); lia.
destruct mode; apply (f_equal IZR).
- now eapply inbetween_int_UP_sign.
- now eapply inbetween_int_DN_sign.
- now eapply inbetween_int_ZR_sign with (l := (convert_location_inv p1)).
- now eapply inbetween_int_NE_sign.
(* *)
rewrite Zdiv_eucl_unique.
set (q := (_ / _)%Z).
set (r := (_ mod _)%Z).
assert (Pq : (0 < q)%Z).
  apply  Z.div_str_pos; split; try lia.
  generalize (Zdigits_correct beta (Z.pos p)); intros [U1 U2].
  apply Zle_trans with (2 := U1).
  rewrite Pos2Z.inj_pow, radix_to_pos.
  now apply Zpower_le; lia.
assert (Pr : (0 <= r < Z.pos (Z.to_pos beta ^ n1))%Z).
  now apply Z_mod_lt.
revert Pq.
case_eq  q; try lia; intros q1 Hq1; try lia; intros _.
unfold FtoX.
rewrite FtoR_split.
rewrite adjust_mantissa_correct, adjust_pos_correct; last 2 first.
- rewrite Pos2Z.inj_pow, radix_to_pos.
  now apply Zpower_gt_1.
- now apply Pr.
unfold F2R; simpl bpow; rewrite Rmult_1_r.
pose (ll := new_location (Z.pos (Z.to_pos beta ^ n1)) r loc_Exact).
assert (V : inbetween_int q (IZR (Zpos p) / IZR (Z.pow_pos beta n1)) ll).
  unfold q, inbetween_int, ll.
  replace  (IZR (Z.pos p / Z.pos (Z.to_pos beta ^ n1) + 1))%R
    with
    (IZR (Z.pos p / Z.pos (Z.to_pos beta ^ n1)) +
      IZR (Z.pos (Z.to_pos beta ^ n1)) * (1 / IZR (Z.pos (Z.to_pos beta ^ n1))))%R; last first.
    rewrite plus_IZR; simpl.
    field.
    apply Rlt_neq_sym.
    now apply IZR_lt.
  apply new_location_correct; try lia.
  - apply Rdiv_lt_0_compat; try lra.
    now apply IZR_lt.
  - rewrite Pos2Z.inj_pow, radix_to_pos.
    now apply Zpower_gt_1.
  apply inbetween_Exact.
  unfold r.
  rewrite Pos2Z.inj_pow, radix_to_pos, Z.pow_pos_fold.
  assert (0 < beta ^ Z.pos n1)%Z.
    apply Zpower_gt_0; lia.
  rewrite (Z_div_mod_eq (Z.pos p) (beta ^ Z.pos n1)) at 1; try lia.
  rewrite plus_IZR, mult_IZR.
  field.
  apply Rlt_neq_sym; apply IZR_lt; lia.
unfold Fnum; apply sym_equal.
rewrite <-(Rlt_bool_float beta b p (Z.neg n1)) at 2 3.
destruct mode; unfold Xlift, Rnearbyint, F2R; do 2 eapply f_equal.
- apply inbetween_int_UP_sign.
  now rewrite FtoR_abs, <- Hq1.
- apply inbetween_int_DN_sign.
  now rewrite FtoR_abs, <- Hq1.
- apply inbetween_int_ZR_sign with (l := ll).
  now rewrite FtoR_abs, <- Hq1.
- apply inbetween_int_NE_sign with (l := ll).
  now rewrite FtoR_abs, <- Hq1.
Qed.

(*
 * Fadd
 *)

Lemma Fadd_slow_aux1_correct :
  forall beta sx sy mx my e,
  UtoX (Fadd_slow_aux1 beta sx sy mx my e) =
  Xadd (FtoX (@Float beta sx mx e)) (FtoX (@Float beta sy my e)).
Proof.
intros.
simpl Xbind2.
unfold Fadd_slow_aux1.
change (Zpos mx + Zneg my)%Z with (Zpos mx - Zpos my)%Z.
case_eq (eqb sx sy) ; intro H.
(* == *)
rewrite (eqb_prop _ _ H).
rewrite FtoR_add.
apply refl_equal.
(* != *)
replace sy with (negb sx).
clear H.
case_eq (Zpos mx - Zpos my)%Z.
intro H.
rewrite <- (FtoR_neg beta sx).
unfold FtoR.
change (Zneg mx) with (- Zpos mx)%Z.
rewrite (Zminus_eq _ _ H).
rewrite Rplus_opp_r.
apply refl_equal.
intro p.
unfold Zminus, Zplus.
simpl.
rewrite Z.pos_sub_spec.
case_eq (mx ?= my)%positive ; intros ; try discriminate H0.
rewrite (FtoR_sub beta sx).
now inversion H0.
apply Zgt_lt.
exact H.
intro p.
unfold Zminus, Zplus.
simpl.
rewrite Z.pos_sub_spec.
case_eq (mx ?= my)%positive ; intros ; try discriminate H0.
pattern sx at 2 ; rewrite <- (negb_involutive sx).
rewrite Rplus_comm.
rewrite (FtoR_sub beta (negb sx)).
now inversion H0.
exact H.
generalize H. clear.
now case sx ; case sy.
Qed.

Lemma Fadd_slow_aux2_correct :
  forall beta sx sy mx my ex ey,
  UtoX (Fadd_slow_aux2 beta sx sy mx my ex ey) =
  Xadd (FtoX (@Float beta sx mx ex)) (FtoX (@Float beta sy my ey)).
Proof.
intros.
unfold Xbind2, FtoX.
unfold Fadd_slow_aux2.
case_eq (ex - ey)%Z ; intros ; rewrite Fadd_slow_aux1_correct ;
  unfold FtoX, Xbind2.
(* . *)
replace ey with ex.
apply refl_equal.
rewrite <- (Zplus_0_l ey).
rewrite <- H.
ring.
(* . *)
rewrite <- FtoR_shift.
rewrite <- H.
replace (ey + (ex - ey))%Z with ex. 2: ring.
apply refl_equal.
(* . *)
rewrite <- FtoR_shift.
replace (ex + Zpos p)%Z with ey.
apply refl_equal.
change (Zpos p) with (- Zneg p)%Z.
rewrite <- H.
ring.
Qed.

Theorem Fadd_slow_aux_correct :
  forall beta (x y : float beta),
  UtoX (Fadd_slow_aux x y) = Xadd (FtoX x) (FtoX y).
Proof.
intros.
case x.
(* . *)
case y ; intros ; apply refl_equal.
(* . *)
simpl.
case y.
apply refl_equal.
unfold FtoX.
rewrite Rplus_0_l.
apply refl_equal.
intros sy my ey.
unfold FtoX.
rewrite Rplus_0_l.
apply refl_equal.
(* . *)
intros sx mx ex.
simpl.
case y.
apply refl_equal.
unfold FtoX.
rewrite Rplus_0_r.
apply refl_equal.
intros sy my ey.
rewrite Fadd_slow_aux2_correct.
apply refl_equal.
Qed.

Theorem Fadd_slow_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fadd_slow mode prec x y) = Xround beta mode prec (Xadd (FtoX x) (FtoX y)).
Proof.
intros beta mode prec x y.
unfold Fadd_slow.
rewrite Fround_at_prec_pos_Eq.
now rewrite Fadd_slow_aux_correct.
apply UtoX_pos_Eq.
rewrite Fadd_slow_aux_correct.
destruct x as [| |sx mx ex].
easy.
now case y.
now case y.
Qed.

Definition Fadd_correct := Fadd_slow_correct.

(*
 * Fadd_exact
 *)

Theorem Fadd_exact_correct :
  forall beta (x y : float beta),
  FtoX (Fadd_exact x y) = Xadd (FtoX x) (FtoX y).
Proof.
intros.
unfold Fadd_exact.
rewrite <- (Fadd_slow_aux_correct _ x y).
case (Fadd_slow_aux x y) ; simpl ; try apply refl_equal.
intros.
case p0 ; apply refl_equal.
Qed.

(*
 * Fsub
 *)

Lemma Fsub_split :
  forall beta mode prec (x y : float beta),
  FtoX (Fsub mode prec x y) = (FtoX (Fadd mode prec x (Fneg y))).
Proof.
intros.
unfold Fneg, Fadd, Fsub, Fadd_slow, Fsub_slow.
case y ; trivial.
Qed.

Theorem Fsub_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fsub mode prec x y) = Xround beta mode prec (Xsub (FtoX x) (FtoX y)).
Proof.
intros.
rewrite Fsub_split.
rewrite Xsub_split.
rewrite <- Fneg_correct.
apply Fadd_correct.
Qed.

(*
 * Fsub_exact
 *)

Lemma Fsub_exact_split :
  forall beta (x y : float beta),
  FtoX (Fsub_exact x y) = FtoX (Fadd_exact x (Fneg y)).
Proof.
intros beta x y.
now case y.
Qed.

Theorem Fsub_exact_correct :
  forall beta (x y : float beta),
  FtoX (Fsub_exact x y) = Xsub (FtoX x) (FtoX y).
Proof.
intros beta x y.
rewrite Fsub_exact_split.
rewrite Fadd_exact_correct.
rewrite Fneg_correct.
apply sym_eq, Xsub_split.
Qed.

(*
 * Fmul
 *)

Theorem Fmul_aux_correct :
  forall beta (x y : float beta),
  UtoX (Fmul_aux x y) = Xmul (FtoX x) (FtoX y).
Proof.
intros beta [ | | sx mx ex ] [ | | sy my ey ] ; simpl ; try apply refl_equal.
(* . *)
rewrite Rmult_0_l.
apply refl_equal.
(* . *)
rewrite Rmult_0_l.
apply refl_equal.
(* . *)
rewrite Rmult_0_r.
apply refl_equal.
(* . *)
rewrite FtoR_mul.
apply refl_equal.
Qed.

Theorem Fmul_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fmul mode prec x y) = Xround beta mode prec (Xmul (FtoX x) (FtoX y)).
Proof.
intros beta mode prec x y.
unfold Fmul.
rewrite Fround_at_prec_pos_Eq.
now rewrite Fmul_aux_correct.
apply UtoX_pos_Eq.
rewrite Fmul_aux_correct.
destruct x as [| |sx mx ex].
easy.
now case y.
now case y.
Qed.

(*
 * Fmul_exact
 *)

Theorem Fmul_exact_correct :
  forall beta (x y : float beta),
  FtoX (Fmul_exact x y) = Xmul (FtoX x) (FtoX y).
Proof.
intros beta x y.
unfold Fmul_exact.
rewrite <- (Fmul_aux_correct _ x y).
case (Fmul_aux x y) ; try easy.
intros s m e l.
now case l.
Qed.

Theorem Fdiv_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fdiv mode prec x y) = Xround beta mode prec (Xdiv (FtoX x) (FtoX y)).
Proof with auto with typeclass_instances.
intros beta mode prec [ | | sx mx ex] [ | | sy my ey] ;
  simpl ; unfold Xdiv' ;
  try rewrite is_zero_correct_zero ;
  try apply refl_equal ;
  rewrite is_zero_correct_float.
unfold Rdiv.
rewrite Rmult_0_l.
apply sym_eq.
apply (f_equal Xreal).
apply round_0...
unfold Xround, Fdiv, Fdiv_aux, Fdiv_aux2.
set (e := Zmin ((Zdigits beta (Zpos mx) + ex) - (Zdigits beta (Zpos my) + ey) - Zpos prec) (ex - ey)).
generalize (Div.Fdiv_core_correct beta (Zpos mx) ex (Zpos my) ey e eq_refl eq_refl).
unfold Div.Fdiv_core.
rewrite Zle_bool_true by apply Zle_min_r.
match goal with |- context [let (m,e') := ?v in let '(q,r) := Zfast_div_eucl _ _ in _] => set (me := v) end.
assert (me = (Zpos mx * Zpower beta (ex - ey - e), e))%Z as ->.
{ unfold me, e ; clear.
  destruct (_ + Zpos prec - _)%Z as [|p|p] eqn:He.
  - rewrite Zmin_r by omega.
    now rewrite Z.sub_diag, Zmult_1_r.
  - rewrite Zmin_l by (zify ; omega).
    change (Zneg p) with (Zopp (Zpos p)).
    fold (Zpower beta (Zpos p)).
    rewrite <- He.
    apply (f_equal2 (fun v1 v2 => (_ * Zpower beta v1, v2)%Z)) ; ring.
  - rewrite Zmin_r by (zify ; omega).
    now rewrite Z.sub_diag, Zmult_1_r. }
rewrite Zfast_div_eucl_correct.
destruct Zdiv_eucl as [m r].
set (l := new_location _ _ _).
intros H1.
assert (Zpos prec <= Zdigits beta m)%Z as H2.
{ generalize (Div.mag_div_F2R beta (Zpos mx) ex (Zpos my) ey eq_refl eq_refl).
  cbv zeta.
  intros H2.
  refine (_ (cexp_inbetween_float _ (FLX_exp (Zpos prec)) _ _ _ _ _ H1 (or_introl _))).
  unfold cexp, FLX_exp, e.
  intros H3.
  zify ; omega.
  apply Rmult_lt_0_compat.
  now apply F2R_gt_0.
  apply Rinv_0_lt_compat.
  now apply F2R_gt_0.
  unfold cexp, FLX_exp, e.
  zify ; omega. }
destruct m as [|p|p].
- now elim H2.
- replace (FtoR beta sx mx ex / FtoR beta sy my ey)%R with
  (if xorb sx sy then - (FtoR beta false mx ex / FtoR beta false my ey) else (FtoR beta false mx ex / FtoR beta false my ey))%R.
apply (Fround_at_prec_correct beta mode prec _ p e).
apply Rmult_lt_0_compat.
apply FtoR_Rpos.
apply Rinv_0_lt_compat.
apply FtoR_Rpos.
rewrite normalize_identity.
rewrite convert_location_bij.
now rewrite 2!FtoR_split.
now rewrite <- digits_conversion.
rewrite 4!FtoR_split.
assert (F2R (Defs.Float beta (Zpos my) ey) <> 0%R).
apply Rgt_not_eq.
now apply F2R_gt_0.
unfold cond_Zopp.
now case sx ; case sy ; repeat rewrite F2R_Zopp ; simpl ; field.
destruct (Bracket.inbetween_float_bounds _ _ _ _ _ H1) as (_, H5).
elim (Rlt_not_le _ _ H5).
apply Rle_trans with 0%R.
apply F2R_le_0.
unfold Fnum.
now apply (Zlt_le_succ (Zneg p)).
- apply Rlt_le.
apply Rmult_lt_0_compat.
now apply F2R_gt_0.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
Qed.

Lemma Fsqrt_correct :
  forall beta mode prec (x : float beta),
  FtoX (Fsqrt mode prec x) = Xround beta mode prec (Xsqrt (FtoX x)).
Proof with auto with typeclass_instances.
intros beta mode prec [ | | sx mx ex] ; simpl ; unfold Xsqrt' ; try easy.
(* *)
case is_negative_spec.
intros H.
elim (Rlt_irrefl _ H).
intros _.
apply sym_eq.
apply (f_equal Xreal).
rewrite sqrt_0.
apply round_0...
(* *)
unfold Fsqrt, Fsqrt_aux, Fsqrt_aux2.
case is_negative_spec.
case sx ; simpl.
easy.
intros H.
elim (Rlt_not_le _ _ H).
apply Rlt_le.
apply FtoR_Rpos.
case sx.
intros H.
elim (Rle_not_lt _ _ H).
apply FtoR_Rneg.
intros _.
unfold Xround.
set (e1 := Zmax _ _).
destruct (if Z.even _ then _ else _) as [s' e''] eqn:Hse.
set (e' := Zdiv2 e'').
assert (e' = Zdiv2 (ex - e1) /\ s' = ex - 2 * e')%Z as [He1 He2].
{ generalize (Zdiv2_odd_eqn (ex - e1)).
  rewrite <- Z.negb_even.
  destruct Z.even eqn:H ; injection Hse ; intros <- <-.
  rewrite Zplus_0_r.
  intros H0.
  apply (conj eq_refl).
  fold e' in H0.
  rewrite <- H0.
  ring.
  change (if negb false then _ else _) with 1%Z.
  intros H'.
  unfold e'.
  rewrite H' at 1 3.
  rewrite Z.add_simpl_r.
  rewrite Zdiv2_div, (Zmult_comm 2), Z.div_mul by easy.
  apply (conj eq_refl).
  clear -H' ; omega. }
assert (e' = Zmin (Zdiv2 (Zdigits beta (Zpos mx) + ex) - Zpos prec) (Z.div2 ex)) as He1'.
{ rewrite He1.
  unfold e1.
  rewrite <- Z.sub_min_distr_l, Zminus_0_r.
  rewrite <- Z.min_mono.
  replace (ex - _)%Z with (Zdigits beta (Zpos mx) + ex + (-Zpos prec) * 2)%Z by ring.
  now rewrite Zdiv2_div, Z.div_add, <- Zdiv2_div.
  intros x y ; apply f_equal.
  intros x y.
  rewrite 2!Zdiv2_div.
  now apply Z.div_le_mono. }
assert (2 * e' <= ex)%Z as He.
{ rewrite He1'.
  set (foo := (Zdiv2 _ - _)%Z).
  clear.
  assert (Zmin foo (Zdiv2 ex) <= Zdiv2 ex)%Z as H by apply Zle_min_r.
  generalize (Zdiv2_odd_eqn ex).
  destruct Z.odd ; intros ; omega. }
generalize (Sqrt.Fsqrt_core_correct beta (Zpos mx) ex e' eq_refl He).
unfold Sqrt.Fsqrt_core.
set (m' := match s' with Z0 => _ | _ => _ end).
assert (m' = Zpos mx * Zpower beta (ex - 2 * e'))%Z as ->.
{ rewrite <- He2.
  destruct s' as [|p|p].
  now rewrite Zmult_1_r.
  easy.
  clear -He He2 ; zify ; omega. }
destruct Z.sqrtrem as [m' r].
set (lz := if Zeq_bool _ _ then _ else _).
intros H1.
assert (Zpos prec <= Zdigits beta m')%Z as H2.
{ assert (e' <= Zdiv2 (Zdigits beta (Zpos mx) + ex + 1) - Zpos prec)%Z as He'.
  { rewrite He1'.
    apply Zle_trans with (1 := Zle_min_l _ _).
    apply Zplus_le_compat_r.
    rewrite 2!Zdiv2_div.
    apply Z.div_le_mono.
    easy.
    apply Z.le_succ_diag_r. }
  refine (_ (cexp_inbetween_float _ (FLX_exp (Zpos prec)) _ _ _ _ _ H1 (or_introl _))).
  unfold cexp, FLX_exp.
  rewrite (Sqrt.mag_sqrt_F2R beta (Zpos mx) ex eq_refl).
  clear -He He' ; intros ; omega.
  apply sqrt_lt_R0.
  now apply F2R_gt_0.
  unfold cexp, FLX_exp.
  now rewrite (Sqrt.mag_sqrt_F2R beta (Zpos mx) ex eq_refl). }
destruct m' as [|p|p].
now elim H1.
apply (Fround_at_prec_correct beta mode prec false p e').
apply sqrt_lt_R0.
apply FtoR_Rpos.
rewrite normalize_identity.
rewrite convert_location_bij.
now rewrite FtoR_split.
now rewrite <- digits_conversion.
destruct (Bracket.inbetween_float_bounds _ _ _ _ _ H1) as (_, H5).
elim (Rlt_not_le _ _ H5).
apply Rle_trans with R0.
apply F2R_le_0.
unfold Fnum.
now apply (Zlt_le_succ (Zneg p)).
apply sqrt_ge_0.
Qed.
