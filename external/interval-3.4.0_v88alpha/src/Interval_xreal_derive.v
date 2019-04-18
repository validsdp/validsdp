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
Require Import Interval_missing.
Require Import Interval_xreal.

Theorem derivable_imp_defined :
  forall f r d u v,
  f (Xreal r) = Xreal u -> u <> v ->
  derivable_pt_lim (proj_fun v f) r d ->
  locally_true r (fun a => exists w, f (Xreal a) = Xreal w).
Proof.
intros.
(* by continuity ... *)
assert (continuity_pt (proj_fun v f) r).
apply derivable_continuous_pt.
exists d.
exact H1.
clear H1.
(* ... the projected result cannot be the default value ... *)
replace u with (proj_fun v f r) in H0.
destruct (continuity_pt_ne _ _ _ H0 H2) as (delta, (Hdelta, H3)).
exists delta.
split.
exact Hdelta.
intros.
generalize (H3 _ H1).
unfold proj_fun.
(* ... so the result is not NaN *)
case (f (Xreal (r + h))).
intro H4.
elim H4.
apply refl_equal.
intros.
exists r0.
apply refl_equal.
unfold proj_fun.
rewrite H.
apply refl_equal.
Qed.

Theorem derivable_imp_defined_any :
  forall f r d u,
  f (Xreal r) = Xreal u ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, f (Xreal a) = Xreal w).
Proof.
intros.
eapply derivable_imp_defined.
apply H.
apply Rlt_not_eq.
apply Rlt_plus_1.
apply H0.
Qed.

Theorem derivable_imp_defined_any_2 :
  forall f1 f2 r d1 d2 u1 u2,
  f1 (Xreal r) = Xreal u1 ->
  f2 (Xreal r) = Xreal u2 ->
 (forall v, derivable_pt_lim (proj_fun v f1) r d1) ->
 (forall v, derivable_pt_lim (proj_fun v f2) r d2) ->
  locally_true r (fun a =>
    (exists w1, f1 (Xreal a) = Xreal w1) /\
    (exists w2, f2 (Xreal a) = Xreal w2)).
Proof.
intros.
apply locally_true_and.
apply (derivable_imp_defined_any _ _ _ _ H H1).
apply (derivable_imp_defined_any _ _ _ _ H0 H2).
Qed.

Theorem derivable_imp_defined_gt :
  forall f r d u t,
  f (Xreal r) = Xreal u -> (t < u)%R ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, (t < w)%R /\ f (Xreal a) = Xreal w).
Proof.
intros.
apply locally_true_imp with
  (fun a => (exists w, f (Xreal a) = Xreal w) /\ (t < proj_fun 0 f a)%R).
intros x ((w, H2), H3).
exists w.
split.
replace (proj_fun 0 f x) with w in H3.
exact H3.
unfold proj_fun.
rewrite H2.
apply refl_equal.
exact H2.
apply locally_true_and.
eapply derivable_imp_defined_any ; eassumption.
apply continuity_pt_gt.
replace (proj_fun 0 f r) with u.
exact H0.
unfold proj_fun.
rewrite H.
apply refl_equal.
apply derivable_continuous_pt.
exists d.
apply H1.
Qed.

Theorem derivable_imp_defined_lt :
  forall f r d u t,
  f (Xreal r) = Xreal u -> (u < t)%R ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, (w < t)%R /\ f (Xreal a) = Xreal w).
Proof.
intros.
apply locally_true_imp with
  (fun a => (exists w, f (Xreal a) = Xreal w) /\ (proj_fun 0 f a < t)%R).
intros x ((w, H2), H3).
exists w.
split.
replace (proj_fun 0 f x) with w in H3.
exact H3.
unfold proj_fun.
now rewrite H2.
exact H2.
apply locally_true_and.
eapply derivable_imp_defined_any ; eassumption.
apply continuity_pt_lt.
replace (proj_fun 0 f r) with u.
exact H0.
unfold proj_fun.
rewrite H.
apply refl_equal.
apply derivable_continuous_pt.
exists d.
apply H1.
Qed.

Theorem derivable_imp_defined_ne :
  forall f r d u t,
  f (Xreal r) = Xreal u -> (u <> t)%R ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, (w <> t)%R /\ f (Xreal a) = Xreal w).
Proof.
intros.
apply locally_true_imp with
  (fun a => (exists w, f (Xreal a) = Xreal w) /\ (proj_fun 0 f a <> t)%R).
intros x ((w, H2), H3).
exists w.
split.
replace (proj_fun 0 f x) with w in H3.
exact H3.
unfold proj_fun.
rewrite H2.
apply refl_equal.
exact H2.
apply locally_true_and.
eapply derivable_imp_defined_any ; eassumption.
apply continuity_pt_ne.
replace (proj_fun 0 f r) with u.
exact H0.
unfold proj_fun.
rewrite H.
apply refl_equal.
apply derivable_continuous_pt.
exists d.
apply H1.
Qed.

Definition Xderive_pt f x y' :=
  match x, y', f x with
  | Xreal r, Xreal d, Xreal _ => forall v, derivable_pt_lim (proj_fun v f) r d
  | _, Xnan, _ => True
  | _, _, _ => False
  end.

Definition Xderive f f' := forall x, Xderive_pt f x (f' x).

Ltac xtotal_get_spec1 f :=
  match f with
  | Req_bool => Req_bool_spec
  | Rle_bool => Rle_bool_spec
  | Rlt_bool => Rlt_bool_spec
  | is_zero => is_zero_spec
  | is_positive => is_positive_spec
  | is_negative => is_negative_spec
  end.

Ltac xtotal_destruct_xreal v :=
  match v with
  | context [?f ?x] =>
    let r := fresh "r" in
    let X := fresh "X" in
    case_eq v ; [ intros X | intros r X ] ; try rewrite X in *
  | _ =>
    let r := fresh "r" in
    destruct v as [|r]
  end.

Ltac xtotal_aux :=
  trivial ;
  try discriminate ;
  match goal with
  | H: False |- _ => elim H
  (*
  | |- ?v = ?v => apply refl_equal
  | |- True => exact I
  | H: Xreal _ = Xnan |- _ => discriminate H
  | H: Xnan = Xreal _ |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: false = true |- _ => discriminate H
  *)
  | H: ?v = ?v |- _ => clear H
  | H: Xreal _ = Xreal _ |- _ =>
    injection H ; clear H ; intro H
  | H: context [match ?v with Xnan => _ | Xreal _ => _ end] |- _ =>
    xtotal_destruct_xreal v ; try discriminate H ; trivial
  (*| H: match ?v with true => Xnan | false => Xreal _ end = Xreal _ |- _ =>
    (*case_eq v ; intro X ; rewrite X in H ; [ discriminate H | idtac ]*)
    xtotal_destruct_xreal v ; [ discriminate H | idtac ]
  | H: match ?v with true => Xnan | false => Xreal _ end = Xnan |- _ =>
    (*case_eq v ; intro X ; rewrite X in H ; [ idtac | discriminate H ]*)
    xtotal_destruct_xreal v ; [ idtac | discriminate H ]*)
  | H1 : Xderive ?f1 ?f2 , H2 : context [?f2 ?v] |- _ =>
    generalize (H1 v) ; clear H1 ; intro H1 ; unfold Xderive_pt in H1
  | H: ?v = Xreal _ |- _ => rewrite H in *
  | H: ?v = Xnan |- _ => rewrite H in *
  | v: R, H: ?v = _ |- _ =>
    try rewrite H in * ; clear H v
  | v: R, H: _ = ?v |- _ =>
    try rewrite <- H in * ; clear H v
  | H: context [?f ?v] |- _ =>
    let s := xtotal_get_spec1 f in
    let Y := fresh "Y" in
    destruct (s v) as [Y|Y]
  | H: match ?v with true => Xnan | false => Xreal _ end = _ |- _ =>
    let X := fresh "X" in
    case_eq v ; intro X ; rewrite X in H ; try discriminate H
  | |- match ?v with Xnan => _ | Xreal _ => _ end =>
    xtotal_destruct_xreal v
  | |- context [?f ?v] =>
    let s := xtotal_get_spec1 f in
    let Y := fresh "Y" in
    destruct (s v) as [Y|Y]
  end.

Ltac xtotal :=
  unfold Xderive_pt, Xinv', Xdiv', Xsqrt', Xtan', Xln', Xpower_int, Xpower_int', Xmask, Xbind2, Xbind in * ;
  repeat xtotal_aux.

Theorem Xderive_pt_add :
  forall f g f' g' x,
  Xderive_pt f x f' -> Xderive_pt g x g' ->
  Xderive_pt (fun x => Xadd (f x) (g x)) x (Xadd f' g').
Proof.
intros f g f' g' x Hf Hg.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (plus_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X0 X Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold plus_fct, proj_fun.
now rewrite Hw1, Hw2.
now apply derivable_pt_lim_plus.
Qed.

Theorem Xderive_pt_sub :
  forall f g f' g' x,
  Xderive_pt f x f' -> Xderive_pt g x g' ->
  Xderive_pt (fun x => Xsub (f x) (g x)) x (Xsub f' g').
Proof.
intros f g f' g' x Hf Hg.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (minus_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X0 X Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold minus_fct, proj_fun.
now rewrite Hw1, Hw2.
now apply derivable_pt_lim_minus.
Qed.

Theorem Xderive_pt_mul :
  forall f g f' g' x,
  Xderive_pt f x f' -> Xderive_pt g x g' ->
  Xderive_pt (fun x => Xmul (f x) (g x)) x (Xadd (Xmul f' (g x)) (Xmul g' (f x))).
Proof.
intros f g f' g' x Hf Hg.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (mult_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X0 X Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold mult_fct, proj_fun.
now rewrite Hw1, Hw2.
replace r1 with (proj_fun v g r).
replace r3 with (proj_fun v f r).
rewrite (Rmult_comm r0).
now apply derivable_pt_lim_mult.
unfold proj_fun.
now rewrite X0.
unfold proj_fun.
now rewrite X.
Qed.

Theorem Xderive_pt_div :
  forall f g f' g' x,
  Xderive_pt f x f' -> Xderive_pt g x g' ->
  Xderive_pt (fun x => Xdiv (f x) (g x)) x (Xdiv (Xsub (Xmul f' (g x)) (Xmul g' (f x))) (Xmul (g x) (g x))).
Proof.
intros f g f' g' x Hf Hg.
xtotal.
elim Y.
apply Rmult_0_l.
intro v.
apply derivable_pt_lim_eq_locally with (div_fct (proj_fun v f) (proj_fun v g)).
generalize (derivable_imp_defined_any _ _ _ _ X0 Hf).
generalize (derivable_imp_defined_ne _ _ _ _ _ X Y0 Hg).
intros H2 H1.
apply locally_true_imp with (2 := locally_true_and _ _ _ H1 H2).
intros x ((w1, Hw1), (w2, (Hw2a, Hw2b))).
unfold div_fct, proj_fun.
rewrite Hw1, Hw2b.
destruct (is_zero_spec w2).
now elim Hw2a.
apply refl_equal.
replace r1 with (proj_fun v g r).
replace r3 with (proj_fun v f r).
fold (Rsqr (proj_fun v g r)).
apply derivable_pt_lim_div.
apply Hf.
apply Hg.
unfold proj_fun.
now rewrite X.
unfold proj_fun.
now rewrite X0.
unfold proj_fun.
now rewrite X.
Qed.

Theorem Xderive_pt_neg :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xneg (f x)) x (Xneg f').
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (opp_fct (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold opp_fct, proj_fun.
now rewrite Hw.
now apply derivable_pt_lim_opp.
Qed.

Theorem Xderive_pt_abs :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xabs (f x)) x (match Xcmp (f x) (Xreal 0) with Xlt => Xneg f' | Xgt => f' | _ => Xnan end).
Proof.
intros f f' x Hf.
xtotal.
revert X.
now case Xcmp.
revert X.
now case Xcmp.
simpl Xcmp in X0.
destruct (Rcompare_spec r1 0) ; try easy.
intro v.
apply derivable_pt_lim_eq_locally with (fun x => Ropp (proj_fun v f x)).
apply locally_true_imp with (2 := derivable_imp_defined_lt _ _ _ _ _ X H Hf).
intros x (w, (Hw1, Hw2)).
unfold proj_fun.
rewrite Hw2.
now rewrite Rabs_left.
inversion X0.
now apply derivable_pt_lim_opp.
intro v.
apply derivable_pt_lim_eq_locally with (proj_fun v f).
apply locally_true_imp with (2 := derivable_imp_defined_gt _ _ _ _ _ X H Hf).
intros x (w, (Hw1, Hw2)).
unfold proj_fun.
rewrite Hw2.
rewrite Rabs_right.
apply refl_equal.
apply Rle_ge.
now apply Rlt_le.
inversion X0.
now rewrite <- H1.
Qed.

Theorem Xderive_pt_inv :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xinv (f x)) x (Xneg (Xdiv f' (Xsqr (f x)))).
Proof.
intros f f' x Hf.
xtotal.
elim Y.
apply Rmult_0_l.
intro v.
apply derivable_pt_lim_eq_locally with (inv_fct (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_ne _ _ _ _ _ X Y0 Hf).
intros x (w, (Hw1, Hw2)).
unfold inv_fct, proj_fun.
rewrite Hw2.
destruct (is_zero_spec w).
now elim Hw1.
apply refl_equal.
apply derivable_pt_lim_eq with (div_fct (fct_cte 1) (proj_fun v f)).
intro x.
unfold div_fct, fct_cte, Rdiv.
apply Rmult_1_l.
replace (- (r0 / Rsqr r1))%R with ((0 * proj_fun v f r - r0 * fct_cte 1 r) / Rsqr (proj_fun v f r))%R.
apply (derivable_pt_lim_div (fct_cte 1)).
apply derivable_pt_lim_const.
apply Hf.
unfold proj_fun.
now rewrite X.
unfold proj_fun, fct_cte.
rewrite X.
now field.
Qed.

Theorem Xderive_pt_sqrt :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xsqrt (f x)) x (Xdiv f' (Xadd (Xsqrt (f x)) (Xsqrt (f x)))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
assert (Hx: (0 < r1)%R).
destruct Y.
exact H.
elim Y0.
now rewrite <- H, sqrt_0, Rplus_0_l.
apply derivable_pt_lim_eq_locally with (comp sqrt (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_gt _ _ _ _ R0 X Hx Hf).
intros x (w, (Hw1, Hw2)).
unfold comp, proj_fun.
rewrite Hw2.
destruct (is_negative_spec w).
elim (Rlt_not_le _ _ Hw1).
now left.
apply refl_equal.
unfold Rdiv.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
replace (sqrt r1 + sqrt r1)%R with (2 * sqrt r1)%R by ring.
now apply derivable_pt_lim_sqrt.
Qed.

Theorem Xderive_pt_sin :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xsin (f x)) x (Xmul f' (Xcos (f x))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp sin (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
apply derivable_pt_lim_sin.
Qed.

Theorem Xderive_pt_cos :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xcos (f x)) x (Xmul f' (Xneg (Xsin (f x)))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp cos (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
apply derivable_pt_lim_cos.
Qed.

Theorem Xderive_pt_tan :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xtan (f x)) x (Xmul f' (Xadd (Xreal 1) (Xsqr (Xtan (f x))))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp tan (proj_fun v f)).
assert (continuity_pt (comp cos (proj_fun v f)) r).
apply derivable_continuous_pt.
exists (- sin (proj_fun v f r) * r0)%R.
unfold derivable_pt_abs.
apply derivable_pt_lim_comp.
apply Hf.
apply derivable_pt_lim_cos.
replace (cos r1) with (comp cos (proj_fun v f) r) in Y.
generalize (derivable_imp_defined_any _ _ _ _ X Hf).
generalize (continuity_pt_ne _ _ R0 Y H).
intros H2 H1.
apply locally_true_imp with (2 := locally_true_and _ _ _ H1 H2).
unfold comp, proj_fun.
intros x ((w, Hw1), Hw2).
rewrite Hw1.
rewrite Hw1 in Hw2.
destruct (is_zero_spec (cos w)).
now elim Hw2.
apply refl_equal.
unfold comp, proj_fun.
now rewrite X.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
change (sin r1 / cos r1 * (sin r1 / cos r1))%R with (Rsqr (tan r1))%R.
now apply derivable_pt_lim_tan.
Qed.

Theorem Xderive_pt_exp :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xexp (f x)) x (Xmul f' (Xexp (f x))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp exp (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
apply (derivable_pt_lim_exp r1).
Qed.

Theorem Xderive_pt_ln :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xln (f x)) x (match Xcmp (f x) (Xreal 0) with Xgt => Xdiv f' (f x) | _ => Xnan end).
Proof.
intros f f' x Hf.
xtotal.
revert X.
now case Xcmp.
revert X.
now case Xcmp.
revert X.
now case Xcmp.
revert X0.
now case Xcmp.
revert X0.
now case Xcmp.
simpl Xcmp in X0.
destruct (Rcompare_spec r1 0) ; try easy.
now elim Rle_not_lt with (1 := Y0).
simpl Xcmp in X0.
destruct (Rcompare_spec r1 0) ; try easy.
intro v.
apply derivable_pt_lim_eq_locally with (comp ln (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_gt _ _ _ _ R0 X H Hf).
intros x (w, (Hw1, Hw2)).
unfold comp, proj_fun.
rewrite Hw2.
destruct (is_positive_spec w).
easy.
now elim (Rlt_not_le _ _ Hw1).
injection X0.
clear X0.
intros <-.
unfold Rdiv.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
now apply derivable_pt_lim_ln.
Qed.

Theorem Xderive_pt_atan :
  forall f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xatan (f x)) x (Xdiv f' (Xadd (Xreal 1) (Xsqr (f x)))).
Proof.
intros f f' x Hf.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp atan (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
unfold Rdiv.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
apply (derivable_pt_lim_atan r1).
Qed.

Theorem Xderive_pt_power_int :
  forall n f f' x,
  Xderive_pt f x f' ->
  Xderive_pt (fun x => Xpower_int (f x) n) x (Xmul f' (Xmul (Xreal (IZR n)) (Xpower_int (f x) (Z.pred n)))).
Proof.
intros n f f' x Hf.
destruct n as [|n|n].
(* *)
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp (fun x => powerRZ x 0) (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_0_l, Rmult_0_r.
unfold comp, proj_fun.
simpl.
apply derivable_pt_lim_const.
(* *)
replace (Xpower_int (f x) (Z.pred (Zpos n))) with (match f x with Xnan => Xnan | Xreal r => Xreal (pow r (pred (nat_of_P n))) end).
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp (fun x => pow x (nat_of_P n)) (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X.
rewrite <- (positive_nat_Z n), <- INR_IZR_INZ.
apply derivable_pt_lim_pow_pos.
apply lt_O_nat_of_P.
case (f x).
easy.
intros r.
unfold Xpower_int, Xpower_int', Xbind.
case_eq (Z.pred (Zpos n))%Z.
intros H.
replace (nat_of_P n) with 1.
easy.
apply inj_eq_rev.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
apply Zsucc_eq_compat in H.
now rewrite <- Zsucc_pred in H.
intros p H.
apply f_equal.
apply f_equal.
apply inj_eq_rev.
rewrite pred_of_minus.
rewrite inj_minus1.
now rewrite <- 2!Zpos_eq_Z_of_nat_o_nat_of_P.
apply lt_le_S.
apply lt_O_nat_of_P.
now case n.
(* *)
replace (Xpower_int (f x) (Z.pred (Zneg n))) with (match f x with Xnan => Xnan | Xreal r => if is_zero r then Xnan else Xreal (/ (pow r (S (nat_of_P n)))) end).
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp (fun x => Rinv (pow x (nat_of_P n))) (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_ne _ _ _ _ _ X Y Hf).
intros x (w, (Hw1, Hw2)).
unfold comp, proj_fun.
rewrite Hw2.
now case is_zero_spec.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
change (fun x => (/ x ^ nat_of_P n)%R) with (comp Rinv (fun x => pow x (nat_of_P n))).
unfold proj_fun.
rewrite X.
change (IZR (Zneg n)) with (Ropp (IZR (Zpos n))).
rewrite <- positive_nat_Z, <- INR_IZR_INZ.
replace (- INR (nat_of_P n) * / (r1 * r1 ^ nat_of_P n))%R with
  ((0 * r1 ^ (nat_of_P n) - 1 * fct_cte 1 r1) / Rsqr (r1 ^ (nat_of_P n)) * (INR (nat_of_P n) * (r1 ^ pred (nat_of_P n))))%R.
apply derivable_pt_lim_comp.
apply derivable_pt_lim_pow.
apply derivable_pt_lim_eq with (div_fct (fct_cte 1) (fun x => x)).
intros x.
apply Rmult_1_l.
apply derivable_pt_lim_div with (x := (r1 ^ nat_of_P n)%R).
apply derivable_pt_lim_const.
apply derivable_pt_lim_id.
now apply pow_nonzero.
unfold fct_cte.
unfold Rsqr.
pattern (nat_of_P n) at -5 ; replace (nat_of_P n) with (1 + pred (nat_of_P n))%nat.
rewrite pow_add.
field.
refine (conj _ Y).
now apply pow_nonzero.
rewrite pred_of_minus.
apply le_plus_minus_r.
apply lt_le_S.
apply lt_O_nat_of_P.
case (f x).
easy.
intros r.
simpl.
rewrite <- Pplus_one_succ_r.
now rewrite nat_of_P_succ_morphism.
Qed.

Theorem Xderive_pt_partial_fun :
  forall g f f',
 (forall x y, g x = Xreal y -> f x = Xreal y) ->
  forall x,
  Xderive_pt g x f' ->
  Xderive_pt f x f'.
Proof.
intros g f f' Heq x Hg.
assert (Heqx := Heq x).
xtotal.
now assert (H := Heqx _ (refl_equal _)).
intro v.
apply derivable_pt_lim_eq_locally with (2 := Hg v).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X Hg).
intros x (w, Hw).
unfold proj_fun.
rewrite Hw.
now rewrite (Heq _ _ Hw).
Qed.

Theorem Xderive_pt_eq_fun :
  forall g f f',
 (forall x, f x = g x) ->
  forall x,
  Xderive_pt g x f' ->
  Xderive_pt f x f'.
Proof.
intros g f f' Heq x Hg.
apply Xderive_pt_partial_fun with (2 := Hg).
intros.
now rewrite Heq.
Qed.

Theorem Xderive_pt_identity :
  forall x, Xderive_pt (fun x => x) x (Xmask (Xreal 1) x).
Proof.
intros [|x].
exact I.
intro.
apply derivable_pt_lim_id.
Qed.

Theorem Xderive_pt_constant :
  forall v x,
  Xderive_pt (fun _ => Xreal v) x (Xmask (Xreal 0) x).
Proof.
intros v [|x].
exact I.
unfold proj_fun.
intros w.
apply (derivable_pt_lim_const v).
Qed.

Theorem Xderive_MVT :
  forall f f',
  Xderive f f' ->
  forall dom : R -> Prop,
  connected dom ->
 (forall x, dom x -> f' (Xreal x) <> Xnan) ->
  forall m, dom m ->
  forall x, dom x ->
  exists c, dom c /\
  f (Xreal x) = Xadd (f (Xreal m)) (Xmul (f' (Xreal c)) (Xsub (Xreal x) (Xreal m))).
Proof.
intros f f' Hd dom Hdom Hf'.
set (fr := proj_fun 0 f).
set (fr' := proj_fun 0 f').
unfold Xderive, Xderive_pt in Hd.
(* f defined on [a,b] *)
assert (R1: forall x, dom x -> f (Xreal x) = Xreal (fr x)).
intros x Hx.
generalize (Hd (Xreal x)) (Hf' x Hx).
unfold fr, proj_fun at 2.
case (f' (Xreal x)).
intros _ H.
elim H.
apply refl_equal.
case (f (Xreal x)).
intros _ H _.
elim H.
intros r _ _ _.
apply refl_equal.
(* f' defined on [a,b] *)
assert (R2: forall x, dom x -> f' (Xreal x) = Xreal (fr' x)).
intros x Hx.
generalize (Hd (Xreal x)) (Hf' x Hx).
unfold fr', proj_fun at 2.
case (f' (Xreal x)).
intros _ H.
elim H.
apply refl_equal.
intros r _ _.
apply refl_equal.
(* for any u < v *)
assert (H9: forall u v, dom u -> dom v -> (u < v)%R ->
        exists c, dom c /\ f (Xreal v) = Xadd (f (Xreal u)) (Xmul (f' (Xreal c)) (Xsub (Xreal v) (Xreal u)))).
intros u v Hu Hv Huv.
destruct (MVT_cor3 fr fr' u v Huv) as [c [P1 [P2 P3]]].
intros c Hc1 Hc2.
assert (Hc := Hdom _ _ Hu Hv _ (conj Hc1 Hc2)).
generalize (Hd (Xreal c)).
rewrite (R2 _ Hc), (R1 _ Hc).
intro H2.
exact (H2 R0).
exists c.
assert (Hc := Hdom _ _ Hu Hv _ (conj P1 P2)).
split.
exact Hc.
rewrite (R2 _ Hc), (R1 _ Hu), (R1 _ Hv).
simpl.
apply f_equal.
exact P3.
(* . *)
intros m Hm x Hx.
destruct (total_order_T m x) as [[H|H]|H].
now apply (H9 m x).
(* m = x *)
exists m.
split.
exact Hm.
rewrite H, (R1 _ Hx), (R2 _ Hx).
simpl.
apply f_equal.
ring.
(* m > x *)
destruct (H9 x m Hx Hm H) as (c, (Hc, H0)).
exists c.
split.
exact Hc.
rewrite H0.
rewrite (R2 _ Hc), (R1 _ Hx).
simpl.
apply f_equal.
ring.
Qed.
