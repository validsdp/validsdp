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

Require Import Reals Psatz.
Require Import Coquelicot.Coquelicot.
Require Import Interval_missing.

Local Open Scope R_scope.

Lemma Rolle_lim (f : R -> R) (a b : R) (h : R -> R) :
  (forall x : R, a < x < b \/ b < x < a -> derivable_pt_lim f x (h x)) ->
  (forall x : R, a <= x <= b \/ b <= x <= a -> continuity_pt f x) ->
  a <> b ->
  f a = f b ->
  exists c : R, (a < c < b \/ b < c < a) /\ derivable_pt_lim f c 0.
Proof.
intros Hd Hc hdif Heq.
destruct (total_order_T a b) as [[H1|H2]|H3].
- assert (pr : forall x : R, a < x < b -> derivable_pt f x).
  {
    intros y hy.
    unfold derivable_pt, derivable_pt_abs.
    exists (h y).
    now apply Hd; left.
  }
  destruct (Rolle f a b pr) as [k [P HkP]]; trivial.
  + now intros y Hy; apply Hc; left.
  + exists k; split; [now left|].
    now rewrite <-derive_pt_eq; apply HkP.
- now destruct hdif.
- assert (pr : forall x : R, b < x < a -> derivable_pt f x).
  { intros y hy.
    unfold derivable_pt, derivable_pt_abs.
    exists (h y).
    now apply Hd; right.
  }
  destruct (Rolle f b a pr) as [k [P HkP]]; trivial.
  + now intros y Hy; apply Hc; right.
  + now symmetry.
  + exists k; split; [now right|].
    rewrite <-derive_pt_eq; apply HkP.
Qed.

Section TaylorLagrange.

Variables a b : R.
Variable n : nat.

Notation Cab x := (a <= x <= b) (only parsing).
Notation Oab x := (a < x < b) (only parsing).

Variable D : nat -> R -> R.

Notation Tcoeff n x0 := (D n x0 / (INR (fact n))) (only parsing).

Notation Tterm n x0 x := (Tcoeff n x0 * (x - x0)^n) (only parsing).

Notation Tsum n x0 x := (sum_f_R0 (fun i => Tterm i x0 x) n) (only parsing).

Lemma continuity_pt_sum (f : nat -> R -> R) (x : R) :
  (forall k, (k <= n)%nat -> continuity_pt (f k) x) ->
  continuity_pt
  (fun y => (sum_f_R0 (fun n => f n y) n)) x.
Proof.
elim n.
  now intro Hf; simpl; apply continuity_pt_ext with (f O); trivial; apply Hf.
intros n' IHn Hf; simpl; apply continuity_pt_plus.
  apply IHn; intros k Hk; apply Hf; omega.
now apply Hf.
Qed.

Lemma derivable_pt_lim_sum (f : nat -> R -> R) (x : R) (lf : nat -> R) :
  (forall i, (i <= n)%nat -> derivable_pt_lim (f i) x (lf i)) ->
  derivable_pt_lim
  (fun y => (sum_f_R0 (fun n => f n y) n)) x
  (sum_f_R0 lf n).
Proof.
elim n.
  intros Hf; simpl; apply derivable_pt_lim_eq with (f O); trivial.
  now apply (Hf 0%nat).
intros n' IHn Hf; simpl; apply derivable_pt_lim_plus.
  now apply IHn; intros i Hi; apply Hf; auto.
now apply Hf.
Qed.

Section TL.

Hypothesis derivable_pt_lim_Dp :
  forall k x, (k <= n)%nat -> Oab x ->
  derivable_pt_lim (D k) x (D (S k) x).

Hypothesis continuity_pt_Dp :
  forall k x, (k <= n)%nat -> Cab x ->
  continuity_pt (D k) x.

Variables x0 x : R.

(** Define [c : R] so that the function [g : R -> R] below satisfies g(x0)=0. *)
Let c := (D 0 x - Tsum n x0 x) / (x - x0)^(S n).
Let g := fun y => D 0 x - Tsum n y x - c * (x - y)^(S n).

Hypotheses (Hx0 : Cab x0) (Hx : Cab x).

Lemma derivable_pt_lim_aux (y : R) :
  Oab y ->
  derivable_pt_lim g y (- ((D (S n) y) / (INR (fact n)) * (x - y)^n)
                        + c * (INR (S n)) * (x - y)^n).
Proof.
intros Hy.
unfold g.
apply derivable_pt_lim_eq with
  ((fun y : R => (D 0 x - Tsum n y x)%R) + (fun y : R => - c *(x-y)^(S n))%R)%F.
  intros t; unfold plus_fct; simpl; ring.
apply derivable_pt_lim_plus.
- change (fun x1 : R => (D 0 x - Tsum n x1 x)%R) with
    ((fun x1 : R => D 0 x)%R - (fun x1 => Tsum n x1 x)%R)%F.
  rewrite <-Rminus_0_l.
  apply derivable_pt_lim_minus.
    now apply derivable_pt_lim_const.
  assert (Hdtt : forall i : nat,
    (i <= n)%nat ->
    derivable_pt_lim (fun x1 : R => Tterm i x1 x) y
    (/ INR (fact i) * D (S i) y * (x - y) ^ i + (Tcoeff i y) *
    ((INR i * (x - y) ^ pred i) * (-1)))).
  {
    intros i Hi.
    change (fun y : R => (Tcoeff i y * (x - y) ^ i)%R) with
      ((fun y : R => Tcoeff i y) * (fun y => (x - y) ^ i)%R)%F.
    assert (Hmul := derivable_pt_lim_mult (fun y0 : R => Tcoeff i y0)
      (fun y0 : R => (x - y0) ^ i) y (/ INR (fact i) * D (S i) y)
      ((INR i * (x - y) ^ pred i) * -(1))).
    simpl in Hmul.
    apply Hmul; clear Hmul.
    - unfold Rdiv.
      apply derivable_pt_lim_eq with (mult_real_fct (/ INR (fact i)) (D i))%R.
        now intros; unfold mult_real_fct; rewrite Rmult_comm.
      apply derivable_pt_lim_scal.
      now apply derivable_pt_lim_Dp.
    - apply derivable_pt_lim_eq with (comp (fun y => y ^ i) (fun y => x - y)).
        now intros y'; unfold comp.
      apply derivable_pt_lim_comp; [|apply derivable_pt_lim_pow].
      rewrite <-Rminus_0_l.
      apply derivable_pt_lim_minus.
        now apply derivable_pt_lim_const.
      now apply derivable_pt_lim_id.
    }
  assert (Hs := derivable_pt_lim_sum (fun n x1 => Tterm n x1 x) y
    (fun i => / INR (fact i) * D (S i) y * (x - y) ^ i +
    D i y / INR (fact i) * (INR i * (x - y) ^ pred i * -1)) Hdtt).
  simpl in Hs.
  replace (D (S n) y / INR (fact n) * (x - y) ^ n) with
    (sum_f_R0 (fun i : nat => / INR (fact i) * D (S i) y * (x - y) ^ i +
    D i y / INR (fact i) * (INR i * (x - y) ^ pred i * -1)) n).
    now apply Hs.
  rewrite sum_eq with _ (fun i : nat =>
    D (S i) y * / INR (fact i) * (x + - y) ^ i -
    D i y / INR (fact i) * INR i * (x + - y) ^ pred i) n.
  + elim n; [simpl; field|intros n' IHn].
    simpl sum_f_R0.
    rewrite IHn.
    assert (Hinr : INR (S n') =
      match n' with 0%nat => 1 | S _ => INR n' + 1 end)
      by easy.
    rewrite <-Hinr.
    change (fact n' + n' * fact n')%nat with (fact (S n')).
    replace (D (S n') y / INR (fact (S n')) * INR (S n')) with
      (D (S n') y / INR (fact n')).
      change ((x + - y) * (x + - y) ^ n') with ((x + - y) ^ S n').
      unfold Rdiv, Rminus; ring.
    replace (fact (S n')) with (fact n' * (S n'))%nat.
      rewrite mult_INR; unfold Rdiv; field.
      split; apply not_0_INR; [easy|apply fact_neq_0].
    simpl; ring.
  + intros i Hi; unfold Rdiv, Rminus; ring.
- replace (c * INR (S n) * (x - y)^n) with
    (- c * (INR (S n) * (x - y)^ pred (S n) * -(1))) by (simpl ; ring).
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_eq with
    (comp (fun y => y ^ (S n)) (fun y => x - y)).
    now intros y'; unfold comp.
  apply derivable_pt_lim_comp; [|now apply derivable_pt_lim_pow].
  rewrite <-Rminus_0_l.
  apply derivable_pt_lim_minus.
    now apply derivable_pt_lim_const.
  now apply derivable_pt_lim_id.
Qed.

Theorem Taylor_Lagrange :
  exists xi : R,
  D 0 x - Tsum n x0 x =
  Tcoeff (S n) xi * (x - x0)^(S n)
  /\ (x0 <> x -> x0 < xi < x \/ x < xi < x0).
Proof.
intros.
destruct (Req_dec x0 x) as [Heq|Hdif].
  rewrite Heq.
  exists x.
  split; [|now intros H'; case H'].
  rewrite Rminus_diag_eq; [|trivial].
    now rewrite Rminus_diag_eq; [simpl|easy]; rewrite Rmult_0_l, Rmult_0_r.
  elim n.
    simpl; field.
  intros k Hk; simpl.
  now rewrite Hk, Rminus_diag_eq;
    [simpl|easy]; rewrite Rmult_0_l, Rmult_0_r, Rplus_0_r.
case (Rolle_lim g x0 x (fun d =>
  (- ((D (S n) d) / (INR (fact n)) * (x - d)^n) + c * (INR (S n)) * (x - d)^n))).
- intros y Hy; apply derivable_pt_lim_aux.
  split; destruct Hy as [H|H]; case Hx0; case Hx; case H; psatzl R.
- intros y Hy.
  apply continuity_pt_minus; [|reg].
  apply continuity_pt_minus; [reg|].
  apply continuity_pt_sum.
  intros n' hn'; apply continuity_pt_mult.
  + unfold Rdiv; apply continuity_pt_mult.
      apply continuity_pt_Dp; [easy|].
      split; destruct Hy as [H|H]; case Hx0; case Hx; case H; psatzl R.
    now reg.
  + now reg.
- easy.
- assert (Hgx0 : g x0 = 0).
    unfold g, c, Rdiv.
    rewrite Rmult_assoc, <-Rinv_l_sym; [ring|].
    now apply pow_nonzero; apply Rminus_eq_contra; intros H; case Hdif.
  assert (Hgx : g x = 0).
    unfold g, c, Rminus.
    rewrite Rplus_opp_r, pow_ne_zero; [|easy].
    ring_simplify.
    assert (Htsum : forall p, D 0 x - Tsum p x x = 0).
      induction p as [|n' IHn].
      simpl; field.
    unfold Rminus in IHn |-*; simpl.
    rewrite Ropp_plus_distr, <- Rplus_assoc, IHn; ring_simplify; trivial.
    now rewrite Rminus_diag_eq in Htsum.
  now rewrite Hgx0, Hgx.
- intros d [Hd1 Hd2].
  exists d.
  split.
  + assert (Hk : Oab d).
      destruct Hd1 as [Hy|Hy];
        split; case Hy; case Hx0; case Hx; psatzl R.
    assert (H1 := derivable_pt_lim_aux d Hk).
    assert ((- (D (S n) d / INR (fact n) * (x - d) ^ n) +
      c * INR (S n) * (x - d) ^ n) = 0).
      now apply uniqueness_limite with g d.
    assert (Hc : c = D (S n) d / INR (fact (S n))).
      assert (Hc1 := Rplus_opp_r_uniq _ _ H).
      rewrite Ropp_involutive in Hc1.
      assert (Hc2 : c * INR (S n) = D (S n) d / INR (fact n)).
        apply Rmult_eq_reg_r with ((x-d)^n); [easy|].
        apply pow_nonzero.
        destruct Hd1 as [H0|H0]; apply Rminus_eq_contra.
          now apply Rgt_not_eq; case H0.
        now apply Rlt_not_eq; case H0.
      apply Rmult_eq_reg_r with (INR (S n)); [|now apply not_0_INR].
      rewrite Hc2.
      replace (fact (S n)) with (fact n * (S n))%nat by (simpl; ring).
      rewrite mult_INR; field.
      split; apply not_0_INR; [easy|apply fact_neq_0].
    unfold c in Hc.
    apply Rmult_eq_reg_r with (/(x - x0) ^ S n).
      unfold Rdiv in Hc at 1; rewrite Hc; field.
      split; [|apply not_0_INR; apply fact_neq_0].
      apply pow_nonzero; apply Rminus_eq_contra; trivial.
      now intros H'; case Hdif.
    apply Rinv_neq_0_compat; apply pow_nonzero; apply Rminus_eq_contra.
    now intros H'; case Hdif.
  + now case Hd1.
Qed.

End TL.

Section CorTL.

Hypothesis derivable_pt_lim_Dp :
  forall k x, (k <= n)%nat -> Cab x ->
  derivable_pt_lim (D k) x (D (S k) x).

Theorem Cor_Taylor_Lagrange (x0 x : R) :
  Cab x0 -> Cab x ->
  exists c,
  D 0 x - Tsum n x0 x =
  Tcoeff (S n) c * (x - x0)^(S n)
  /\ (x0 <> x -> x0 < c < x \/ x < c < x0).
Proof.
intros Hx0 Hx.
apply Taylor_Lagrange.
- intros k x1 Hk Hab; apply derivable_pt_lim_Dp; trivial.
  now split; case Hab; left.
- intros k x1 Hk Hab.
  apply derivable_continuous_pt.
  unfold derivable_pt, derivable_pt_abs.
  exists (D (S k) x1).
  now apply derivable_pt_lim_Dp.
- exact Hx0.
- exact Hx.
Qed.

End CorTL.

End TaylorLagrange.
