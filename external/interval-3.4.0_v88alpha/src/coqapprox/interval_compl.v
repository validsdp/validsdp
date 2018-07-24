(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

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

Require Import ZArith Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.bigop.
Require Import Coquelicot.Coquelicot.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_interval.
Require Import Rstruct xreal_ssr_compat taylor_thm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

Notation IInan := Interval_interval.Inan (only parsing).

Lemma contains_Xreal (xi : interval) (x : ExtendedR) :
  contains xi x -> contains xi (Xreal (proj_val x)).
Proof. by case: x =>//; case: xi. Qed.

(*******************************************************************************)
(** For convenience, define a predicate [not_empty'] equivalent to [not_empty] *)
(*******************************************************************************)

Definition not_empty' (xi : interval) := exists v : ExtendedR, contains xi v.

Lemma not_emptyE xi : not_empty' xi -> not_empty xi.
Proof.
case: xi =>[|l u] [v Hv]; first by exists R0.
case: v Hv =>[//|r] Hr.
by exists r.
Qed.

Lemma not_empty'E xi : not_empty xi -> not_empty' xi.
Proof.
case=>[r Hr]; by exists (Xreal r).
Qed.

(**************************************************************)
(** Some support results relating inequalities and [contains] *)
(**************************************************************)

Definition intvl a b x := (a <= x <= b)%R.

Lemma intvl_connected a b : connected (intvl a b).
Proof.
move=> x y Hx Hy z Hz; split.
- exact: Rle_trans (proj1 Hx) (proj1 Hz).
- exact: Rle_trans (proj2 Hz) (proj2 Hy).
Qed.

Lemma intvl_l l u x0 :
  intvl l u x0 -> intvl l u l.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl || apply: Rle_trans H2. Qed.

Lemma intvl_u l u x0 :
  intvl l u x0 -> intvl l u u.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl || apply: Rle_trans H2. Qed.

Lemma intvl_lVu l u x0 x :
  intvl l u x -> intvl l u x0 -> intvl l x0 x \/ intvl x0 u x.
Proof.
move=> [H1 H2] [H3 H4].
have [Hle|Hlt] := Rle_lt_dec x x0.
by left.
by move/Rlt_le in Hlt; right.
Qed.

(********************************************)
(** Some support results about monotonicity *)
(********************************************)

Section PredArg.
Variable P : R -> Prop.

Definition Rincr (f : R -> R) :=
  forall x y : R,
  P x -> P y ->
  (x <= y -> f x <= f y)%R.

Definition Rdecr (f : R -> R) :=
  forall x y : R,
  P x -> P y ->
  (x <= y -> f y <= f x)%R.

Definition Rmonot (f : R -> R) :=
  Rincr f \/ Rdecr f.

Definition Rpos_over (g : R -> R) :=
  forall x : R, (P x -> 0 <= g x)%R.

Definition Rneg_over (g : R -> R) :=
  forall x : R, (P x -> g x <= 0)%R.

Definition Rcst_sign (g : R -> R) :=
  Rpos_over g \/ Rneg_over g.

Definition Rderive_over (f f' : R -> R) :=
  forall x : R, P x -> is_derive f x (f' x).

Lemma Rderive_pos_imp_incr (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rpos_over f' -> Rincr f.
Proof.
rewrite /Rpos_over /Rincr.
move=> Hco Hder H0 x y Hx Hy Hxy; rewrite //=.
eapply (derivable_pos_imp_increasing f f' P) =>//.
move=> r Hr.
move/(_ _ Hr) in Hder.
move/(_ _ Hr) in H0.
apply: conj H0.
exact/is_derive_Reals.
Qed.

Lemma Rderive_neg_imp_decr (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rneg_over f' -> Rdecr f.
Proof.
rewrite /Rneg_over /Rdecr.
move=> Hco Hder H0 x y Hx Hy Hxy; rewrite //=.
eapply (derivable_neg_imp_decreasing f f' P) =>//.
move=> r Hr.
move/(_ _ Hr) in Hder.
move/(_ _ Hr) in H0.
apply: conj H0.
exact/is_derive_Reals.
Qed.

Lemma Rderive_cst_sign (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rcst_sign f' -> Rmonot f.
Proof.
move=> Hco Hder [H|H].
left; exact: Rderive_pos_imp_incr H.
right; exact: Rderive_neg_imp_decr H.
Qed.

End PredArg.

(********************************************************************)
(** Instantiation of [taylor_thm.Cor_Taylor_Lagrange] for intervals *)
(********************************************************************)

Section NDerive.
Variable xf : R -> ExtendedR.
Let f x := proj_val (xf x).
Let Dn := Derive_n f.
Variable dom : R -> Prop.
Hypothesis Hdom : connected dom.
Variable n : nat.
Hypothesis Hdef : forall r, dom r -> xf r <> Xnan.
Hypothesis Hder : forall n r, dom r -> ex_derive_n f n r.

Theorem ITaylor_Lagrange x0 x :
  dom x0 ->
  dom x ->
  exists xi : R,
  dom xi /\
  (f x - \big[Rplus/0%R]_(0 <= i < n.+1)
          (Dn i x0 / INR (fact i) * (x - x0)^i))%R =
  (Dn n.+1 xi / INR (fact n.+1) * (x - x0) ^ n.+1)%R /\
  (x <= xi <= x0 \/ x0 <= xi <= x)%R.
Proof.
move=> Hx0 Hx.
case (Req_dec x0 x)=> [->|Hneq].
  exists x; split =>//=; split; last by auto with real.
  rewrite (Rminus_diag_eq x) // Rmult_0_l Rmult_0_r.
  rewrite big_nat_recl // pow_O big1 /Dn /=; try field.
  by move=> i _; rewrite Rmult_0_l Rmult_0_r.
have Hlim x1 x2 : (x1 < x2)%R -> dom x1 -> dom x2 ->
  forall (k : nat) (r1 : R), (k <= n)%coq_nat ->
  (fun r2 : R => x1 <= r2 <= x2)%R r1 ->
  derivable_pt_lim (Dn k) r1 (Dn (S k) r1).
  move=> Hx12 Hdom1 Hdom2 k y Hk Hy.
  have Hdy: (dom y) by move: Hdom; rewrite /connected; move/(_ x1 x2); apply.
  by apply/is_derive_Reals/Derive_correct; apply: (Hder k.+1 Hdy).
destruct (total_order_T x0 x) as [[H1|H2]|H3]; last 2 first.
    by case: Hneq.
  have H0 : (x <= x0 <= x0)%R by auto with real.
  have H : (x <= x <= x0)%R by auto with real.
  case: (Cor_Taylor_Lagrange x x0 n (fun n r => (Dn n r))
    (Hlim _ _ (Rgt_lt _ _ H3) Hx Hx0) x0 x H0 H) => [c [Hc Hc1]].
  exists c.
  have Hdc : dom c.
    move: Hdom; rewrite /connected; move/(_ x x0); apply=>//.
    by case: (Hc1 Hneq)=> [J|K]; lra.
  split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
  rewrite sum_f_to_big in Hc.
  exact: Hc.
have H0 : (x0 <= x0 <= x)%R by auto with real.
have H : (x0 <= x <= x)%R by auto with real.
case: (Cor_Taylor_Lagrange x0 x n (fun n r => Dn n r)
  (Hlim _ _ (Rgt_lt _ _ H1) Hx0 Hx) x0 x H0 H) => [c [Hc Hc1]].
exists c.
have Hdc : dom c.
  move: Hdom; rewrite /connected; move/(_ x0 x); apply=>//.
  by case: (Hc1 Hneq)=> [J|K]; lra.
split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
rewrite sum_f_to_big in Hc.
exact: Hc.
Qed.

End NDerive.

(******************************************************************************)
(** The sequel of the file is parameterized by an implementation of intervals *)
(******************************************************************************)

Module IntervalAux (I : IntervalOps).

(** The following predicate will be used by [Ztech]. *)
Definition isNNegOrNPos (X : I.type) : bool :=
  if I.sign_large X is Xund then false else true.

Lemma isNNegOrNPos_false (X : I.type) :
  I.convert X = IInan -> isNNegOrNPos X = false.
Proof.
move=> H; rewrite /isNNegOrNPos; have := I.sign_large_correct X.
by case: I.sign_large =>//; rewrite H; move/(_ Xnan I) =>//; case.
Qed.

Definition gt0 xi : bool :=
  if I.sign_strict xi is Xgt then true else false.

Definition apart0 xi : bool :=
  match I.sign_strict xi with
  | Xlt | Xgt => true
  | _ => false
  end.

Lemma gt0_correct X x :
  contains (I.convert X) (Xreal x) -> gt0 X -> (0 < x)%R.
Proof.
move=> Hx; rewrite /gt0.
have := I.sign_strict_correct X; case: I.sign_strict=>//.
by case/(_ _ Hx) =>/=.
Qed.

Lemma apart0_correct X x :
  contains (I.convert X) (Xreal x) -> apart0 X -> (x <> 0)%R.
Proof.
move=> Hx; rewrite /apart0.
have := I.sign_strict_correct X; case: I.sign_strict=>//;
  by case/(_ _ Hx) =>/=; auto with real.
Qed.

(*******************************************************)
(** Support results about [I.midpoint] and [not_empty] *)
(*******************************************************)

Definition Imid i : I.type := I.bnd (I.midpoint i) (I.midpoint i).

Lemma not_empty_Imid (X : I.type) :
  not_empty (I.convert X) -> not_empty (I.convert (Imid X)).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
apply: not_emptyE.
exists (I.convert_bound (I.midpoint X)).
red.
have e : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> _] := I.midpoint_correct X e.
by auto with real.
Qed.

Lemma Imid_subset (X : I.type) :
  not_empty (I.convert X) ->
  subset' (I.convert (Imid X)) (I.convert X).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [->] := I.midpoint_correct X HX.
case: I.convert =>[//|l u].
move => H [//|x].
intros [H1 H2].
by rewrite (Rle_antisym _ _ H2 H1).
Qed.

Lemma Imid_contains (X : I.type) :
  not_empty (I.convert X) ->
  contains (I.convert (Imid X)) (I.convert_bound (I.midpoint X)).
Proof.
move=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
split ; apply Rle_refl.
Qed.

Lemma Xreal_Imid_contains (X : I.type) :
  not_empty (I.convert X) ->
  contains (I.convert (Imid X)) (Xreal (proj_val (I.convert_bound (I.midpoint X)))).
Proof.
move=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
split ; apply Rle_refl.
Qed.

(******************************************************************************)
(** Correctness predicates dealing with reals only, weaker than [I.extension] *)
(******************************************************************************)

Lemma R_from_nat_correct :
  forall (b : I.type) (n : nat),
  contains (I.convert (I.fromZ (Z.of_nat n)))
           (Xreal (INR n)).
Proof. move=> b n; rewrite INR_IZR_INZ; exact: I.fromZ_correct. Qed.

Lemma only0 v : contains (I.convert I.zero) (Xreal v) -> v = 0%R.
Proof. by rewrite I.zero_correct; case; symmetry; apply Rle_antisym. Qed.

Section PrecArgument.

Variable prec : I.precision.

Lemma mul_0_contains_0_l y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec X Y)) (Xreal 0).
Proof.
move=> Hy H0.
have H0y ry : (Xreal 0) = (Xreal 0 * Xreal ry)%XR by rewrite /= Rmult_0_l.
case: y Hy => [|ry] Hy; [rewrite (H0y 0%R)|rewrite (H0y ry)];
  apply: I.mul_correct =>//.
by case ->: (I.convert Y) Hy.
Qed.

Lemma mul_0_contains_0_r y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec Y X)) (Xreal 0).
Proof.
move=> Hy H0.
have Hy0 ry : (Xreal 0) = (Xreal ry * Xreal 0)%XR by rewrite /= Rmult_0_r.
case: y Hy => [|ry] Hy; [rewrite (Hy0 0%R)|rewrite (Hy0 ry)];
  apply: I.mul_correct=>//.
by case: (I.convert Y) Hy.
Qed.

Lemma pow_contains_0 (X : I.type) (n : Z) :
  (n > 0)%Z ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.power_int prec X n)) (Xreal 0).
Proof.
move=> Hn HX.
rewrite (_: (Xreal 0) = (Xpower_int (Xreal 0) n)); first exact: I.power_int_correct.
case: n Hn =>//= p Hp; rewrite pow_ne_zero //.
by zify; auto with zarith.
Qed.

Lemma subset_sub_contains_0 x0 (X0 X : I.type) :
  contains (I.convert X0) x0 ->
  subset' (I.convert X0) (I.convert X) ->
  contains (I.convert (I.sub prec X X0)) (Xreal 0).
Proof.
move=> Hx0 Hsub.
destruct x0 as [|x0].
rewrite I.sub_propagate_r //.
now destruct (I.convert X0).
replace (Xreal 0) with (Xreal x0 - Xreal x0)%XR.
apply I.sub_correct with (2 := Hx0).
now apply Hsub.
apply (f_equal Xreal).
now apply Rminus_diag_eq.
Qed.

End PrecArgument.
End IntervalAux.
