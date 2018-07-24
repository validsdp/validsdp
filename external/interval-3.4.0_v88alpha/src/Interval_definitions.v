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

Require Import Reals ZArith.
Require Import Psatz.
From Flocq Require Import Core.
Require Import Interval_xreal.

Inductive rounding_mode : Set :=
  rnd_UP | rnd_DN | rnd_ZR | rnd_NE.

Definition Rnearbyint mode r :=
  match mode with
  | rnd_UP => IZR (Zceil r)
  | rnd_DN => IZR (Zfloor r)
  | rnd_ZR => IZR (Ztrunc r)
  | rnd_NE => IZR (ZnearestE r)
  end.

Notation Xnearbyint := (fun mode => Xlift (Rnearbyint mode)).

Lemma Rnearbyint_le :
  forall mode x y,
  (x <= y)%R ->
  (Rnearbyint mode x <= Rnearbyint mode y)%R.
Proof.
intros mode x y Hxy.
destruct mode ; simpl.
now apply IZR_le, Zceil_le.
now apply IZR_le, Zfloor_le.
now apply IZR_le, Ztrunc_le.
now apply IZR_le; destruct (valid_rnd_N (fun x => negb (Z.even x))); auto.
Qed.


Lemma Rnearbyint_error_DN x :
  (-1 <= Rnearbyint rnd_DN x - x <= 0)%R.
Proof.
assert (H := (Zfloor_ub x, Zfloor_lb x)).
case H; simpl; lra.
Qed.

Lemma Rnearbyint_error_UP x :
  (0 <= Rnearbyint rnd_UP x - x <= 1)%R.
Proof.
assert (H := (Zfloor_ub (- x), Zfloor_lb (- x))).
simpl; unfold Zceil; rewrite opp_IZR.
case H; simpl; lra.
Qed.

Lemma Rnearbyint_error_ZR_neg x :
  (x <= 0 ->
   0 <= Rnearbyint rnd_ZR x - x <= 1)%R.
Proof.
simpl; unfold Ztrunc.
case Rlt_bool_spec; try lra.
intros; apply Rnearbyint_error_UP.
intros H H0.
assert (H1 : x = 0%R) by lra.
assert (H2 := Zfloor_IZR 0); simpl in H2.
rewrite H1, H2; simpl; lra.
Qed.

Lemma Rnearbyint_error_ZR_pos x :
  (0 <= x ->
   -1 <= Rnearbyint rnd_ZR x - x <= 0)%R.
Proof.
simpl; unfold Ztrunc.
case Rlt_bool_spec; try lra.
now intros; apply Rnearbyint_error_DN.
Qed.

Lemma Rnearbyint_error_ZR x :
  (-1 <= Rnearbyint rnd_ZR x - x <= 1)%R.
Proof.
assert (H := (Rnearbyint_error_ZR_neg x, Rnearbyint_error_ZR_pos x)).
case H; simpl; lra.
Qed.

Lemma Rnearbyint_error_NE x :
  (- (1/2) <= Rnearbyint rnd_NE x - x <= 1/2)%R.
Proof.
simpl.
assert (H := Znearest_half (fun x => negb (Z.even x)) x).
split_Rabs; lra.
Qed.

Lemma Rnearbyint_error m x :
  (-1 <= Rnearbyint m x - x <= 1)%R.
Proof.
assert (H1 := Rnearbyint_error_DN x).
assert (H2 := Rnearbyint_error_UP x).
assert (H3 := Rnearbyint_error_ZR x).
assert (H4 := Rnearbyint_error_NE x).
case m; lra.
Qed.

Notation radix2 := Zaux.radix2 (only parsing).

Section Definitions.

Variable beta : radix.

Fixpoint count_digits_aux nb pow (p q : positive) { struct q } : positive :=
  if Zlt_bool (Zpos p) pow then nb
  else
    match q with
    | xH => nb
    | xI r => count_digits_aux (Psucc nb) (Zmult beta pow) p r
    | xO r => count_digits_aux (Psucc nb) (Zmult beta pow) p r
    end.

Definition count_digits n :=
  count_digits_aux 1 beta n n.

Definition FtoR (s : bool) m e :=
  let sm := if s then Zneg m else Zpos m in
  match e with
  | Zpos p => IZR (sm * Zpower_pos beta p)
  | Z0 => IZR sm
  | Zneg p => (IZR sm / IZR (Zpower_pos beta p))%R
  end.

End Definitions.

Definition rnd_of_mode mode :=
  match mode with
  | rnd_UP => rndUP
  | rnd_DN => rndDN
  | rnd_ZR => rndZR
  | rnd_NE => rndNE
  end.

Definition round beta mode prec :=
  round beta (FLX_exp (Zpos prec)) (rnd_of_mode mode).

Definition Xround beta mode prec := Xlift (round beta mode prec).

Inductive float (beta : radix) : Set :=
  | Fnan : float beta
  | Fzero : float beta
  | Float : bool -> positive -> Z -> float beta.

Arguments Fnan {beta}.
Arguments Fzero {beta}.
Arguments Float {beta} _ _ _.

Definition FtoX {beta} (f : float beta) :=
  match f with
  | Fzero => Xreal 0
  | Fnan => Xnan
  | Float s m e => Xreal (FtoR beta s m e)
  end.

Instance zpos_gt_0 : forall prec, Prec_gt_0 (Zpos prec).
Proof.
easy.
Qed.

Instance valid_rnd_of_mode : forall mode, Valid_rnd (rnd_of_mode mode).
Proof.
destruct mode ; simpl ; auto with typeclass_instances.
Qed.

Lemma FtoR_split :
  forall beta s m e,
  FtoR beta s m e = F2R (Defs.Float beta (cond_Zopp s (Zpos m)) e).
Proof.
intros.
unfold FtoR, F2R, cond_Zopp. simpl.
case e.
now rewrite Rmult_1_r.
intros p.
now rewrite mult_IZR.
now intros p.
Qed.

Lemma is_zero_correct_zero :
  is_zero 0 = true.
Proof.
destruct (is_zero_spec 0).
apply refl_equal.
now elim H.
Qed.

Lemma is_zero_correct_float :
  forall beta s m e,
  is_zero (FtoR beta s m e) = false.
Proof.
intros beta s m e.
rewrite FtoR_split.
case is_zero_spec ; try easy.
intros H.
apply eq_0_F2R in H.
now destruct s.
Qed.
