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

Require Import Reals Psatz.
From Flocq Require Export Raux.

Ltac evar_last :=
  match goal with
  | |- ?f ?x =>
    let tx := type of x in
    let tx := eval simpl in tx in
    let tmp := fresh "tmp" in
    evar (tmp : tx) ;
    refine (@eq_ind tx tmp f _ x _) ;
    unfold tmp ; clear tmp
  end.

Lemma Rplus_lt_reg_l :
  forall r r1 r2 : R,
  (r + r1 < r + r2)%R -> (r1 < r2)%R.
Proof.
intros.
solve [ apply Rplus_lt_reg_l with (1 := H) |
        apply Rplus_lt_reg_r with (1 := H) ].
Qed.

Lemma Rplus_lt_reg_r :
  forall r r1 r2 : R,
  (r1 + r < r2 + r)%R -> (r1 < r2)%R.
Proof.
intros.
apply Rplus_lt_reg_l with r.
now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rmult_le_compat_neg_r :
  forall r r1 r2 : R,
  (r <= 0)%R -> (r1 <= r2)%R -> (r2 * r <= r1 * r)%R.
Proof.
intros.
rewrite (Rmult_comm r2).
rewrite (Rmult_comm r1).
apply Rmult_le_compat_neg_l.
exact H.
exact H0.
Qed.

Lemma Rmult_eq_compat_r :
  forall r r1 r2 : R,
  r1 = r2 -> (r1 * r)%R = (r2 * r)%R.
Proof.
intros.
rewrite (Rmult_comm r1).
rewrite (Rmult_comm r2).
apply Rmult_eq_compat_l.
exact H.
Qed.

Lemma Rmult_eq_reg_r :
  forall r r1 r2 : R,
  (r1 * r)%R = (r2 * r)%R -> r <> 0%R -> r1 = r2.
Proof.
intros.
apply Rmult_eq_reg_l with (2 := H0).
do 2 rewrite (Rmult_comm r).
exact H.
Qed.

Lemma Rsqr_plus1_pos x : (0 < 1 + Rsqr x)%R.
Proof. now apply (Rplus_lt_le_0_compat _ _ Rlt_0_1 (Rle_0_sqr x)). Qed.

Lemma Rsqr_plus1_neq0 x : (1 + Rsqr x <> 0)%R.
Proof. now apply Rgt_not_eq; apply Rlt_gt; apply Rsqr_plus1_pos. Qed.

Lemma Rmin_Rle :
  forall r1 r2 r,
  (Rmin r1 r2 <= r)%R <-> (r1 <= r)%R \/ (r2 <= r)%R.
Proof.
intros.
unfold Rmin.
split.
case (Rle_dec r1 r2) ; intros.
left. exact H.
right. exact H.
intros [H|H] ; case (Rle_dec r1 r2) ; intros H0.
exact H.
apply Rle_trans with (2 := H).
apply Rlt_le.
apply Rnot_le_lt with (1 := H0).
apply Rle_trans with r2 ; assumption.
exact H.
Qed.

Lemma Rle_Rinv_pos :
  forall x y : R,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
Proof.
intros.
apply Rle_Rinv.
exact H.
apply Rlt_le_trans with x ; assumption.
exact H0.
Qed.

Lemma Rle_Rinv_neg :
  forall x y : R,
  (y < 0)%R -> (x <= y)%R -> (/y <= /x)%R.
Proof.
intros.
apply Ropp_le_cancel.
repeat rewrite Ropp_inv_permute.
apply Rle_Rinv.
auto with real.
apply Rlt_le_trans with (Ropp y).
auto with real.
auto with real.
auto with real.
apply Rlt_dichotomy_converse.
left. exact H.
apply Rlt_dichotomy_converse.
left.
apply Rle_lt_trans with y ; assumption.
Qed.

Lemma Rmult_le_pos_pos :
  forall x y : R,
  (0 <= x)%R -> (0 <= y)%R -> (0 <= x * y)%R.
Proof.
exact Rmult_le_pos.
Qed.

Lemma Rmult_le_pos_neg :
  forall x y : R,
  (0 <= x)%R -> (y <= 0)%R -> (x * y <= 0)%R.
Proof.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_l ; assumption.
Qed.

Lemma Rmult_le_neg_pos :
  forall x y : R,
  (x <= 0)%R -> (0 <= y)%R -> (x * y <= 0)%R.
Proof.
intros.
rewrite <- (Rmult_0_l y).
apply Rmult_le_compat_r ; assumption.
Qed.

Lemma Rmult_le_neg_neg :
  forall x y : R,
  (x <= 0)%R -> (y <= 0)%R -> (0 <= x * y)%R.
Proof.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_neg_l ; assumption.
Qed.

Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
induction n; [easy|simpl].
now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma Rabs_def1_le :
  forall x a,
  (x <= a)%R -> (-a <= x)%R ->
  (Rabs x <= a)%R.
Proof.
intros.
case (Rcase_abs x) ; intros.
rewrite (Rabs_left _ r).
rewrite <- (Ropp_involutive a).
apply Ropp_le_contravar.
exact H0.
rewrite (Rabs_right _ r).
exact H.
Qed.

Lemma Rabs_def2_le :
  forall x a,
  (Rabs x <= a)%R ->
  (-a <= x <= a)%R.
Proof.
intros x a H.
assert (0 <= a)%R.
apply Rle_trans with (2 := H).
apply Rabs_pos.
generalize H. clear H.
unfold Rabs.
case (Rcase_abs x) ; split.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar.
exact H.
apply Rlt_le.
apply Rlt_le_trans with (1 := r).
exact H0.
generalize (Rge_le _ _ r).
clear r.
intro.
apply Rle_trans with (2 := H1).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
exact H0.
exact H.
Qed.

Theorem derivable_pt_lim_eq :
  forall f g,
 (forall x, f x = g x) ->
  forall x l,
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
intros f g H x l.
unfold derivable_pt_lim.
intros.
destruct (H0 _ H1) as (delta, H2).
exists delta.
intros.
do 2 rewrite <- H.
apply H2 ; assumption.
Qed.

Definition locally_true x (P : R -> Prop) :=
  exists delta, (0 < delta)%R /\
  forall h, (Rabs h < delta)%R -> P (x + h)%R.

Theorem derivable_pt_lim_eq_locally :
  forall f g x l,
  locally_true x (fun v => f v = g v) ->
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
intros f g x l (delta1, (Hd, Heq)) Hf eps Heps.
destruct (Hf eps Heps) as (delta2, H0).
clear Hf.
assert (0 < Rmin delta1 delta2)%R.
apply Rmin_pos.
exact Hd.
exact (cond_pos delta2).
exists (mkposreal (Rmin delta1 delta2) H).
intros.
rewrite <- Heq.
pattern x at 2 ; rewrite <- Rplus_0_r.
rewrite <- Heq.
rewrite Rplus_0_r.
apply H0.
exact H1.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_r.
rewrite Rabs_R0.
exact Hd.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_l.
Qed.

Theorem locally_true_and :
  forall P Q x,
  locally_true x P ->
  locally_true x Q ->
  locally_true x (fun x => P x /\ Q x).
Proof.
intros P Q x HP HQ.
destruct HP as (e1, (He1, H3)).
destruct HQ as (e2, (He2, H4)).
exists (Rmin e1 e2).
split.
apply Rmin_pos ; assumption.
intros.
split.
apply H3.
apply Rlt_le_trans with (1 := H).
apply Rmin_l.
apply H4.
apply Rlt_le_trans with (1 := H).
apply Rmin_r.
Qed.

Theorem locally_true_imp :
  forall P Q : R -> Prop,
 (forall x, P x -> Q x) ->
  forall x,
  locally_true x P ->
  locally_true x Q.
Proof.
intros P Q H x (d, (Hd, H0)).
exists d.
split.
exact Hd.
intros.
apply H.
apply H0.
exact H1.
Qed.

Theorem continuity_pt_lt :
  forall f x y,
  (f x < y)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (f u < y)%R).
Proof.
intros.
assert (0 < y - f x)%R.
apply Rplus_lt_reg_l with (f x).
rewrite Rplus_0_r.
replace (f x + (y - f x))%R with y. 2: ring.
exact H.
destruct (H0 _ H1) as (delta, (Hdelta, H2)).
clear H0.
exists delta.
split.
exact Hdelta.
intros.
case (Req_dec h 0) ; intro H3.
rewrite H3.
rewrite Rplus_0_r.
exact H.
generalize (H2 (x + h)%R). clear H2.
unfold R_met, R_dist, D_x, no_cond.
simpl.
intro.
apply Rplus_lt_reg_r with (- f x)%R.
apply Rle_lt_trans with (1 := RRle_abs (f (x + h) - f x)%R).
apply H2.
assert (x + h - x = h)%R. ring.
split.
split.
exact I.
intro H5.
elim H3.
rewrite <- H4.
rewrite <- H5.
exact (Rplus_opp_r _).
rewrite H4.
exact H0.
Qed.

Theorem continuity_pt_gt :
  forall f x y,
  (y < f x)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (y < f u)%R).
Proof.
intros.
generalize (Ropp_lt_contravar _ _ H).
clear H. intro H.
generalize (continuity_pt_opp _ _ H0).
clear H0. intro H0.
destruct (continuity_pt_lt (opp_fct f) _ _ H H0) as (delta, (Hdelta, H1)).
exists delta.
split.
exact Hdelta.
intros.
apply Ropp_lt_cancel.
exact (H1 _ H2).
Qed.

Theorem continuity_pt_ne :
  forall f x y,
  f x <> y ->
  continuity_pt f x ->
  locally_true x (fun u => f u <> y).
Proof.
intros.
destruct (Rdichotomy _ _ H) as [H1|H1].
destruct (continuity_pt_lt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rlt_not_eq.
exact (H2 _ H3).
destruct (continuity_pt_gt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rgt_not_eq.
exact (H2 _ H3).
Qed.

Theorem derivable_pt_lim_tan :
  forall x,
  (cos x <> 0)%R ->
  derivable_pt_lim tan x (1 + Rsqr (tan x))%R.
Proof.
intros x Hx.
change (derivable_pt_lim (sin/cos) x (1 + Rsqr (tan x))%R).
replace (1 + Rsqr (tan x))%R with ((cos x * cos x - (-sin x) * sin x) / Rsqr (cos x))%R.
apply derivable_pt_lim_div.
apply derivable_pt_lim_sin.
apply derivable_pt_lim_cos.
exact Hx.
unfold Rsqr, tan.
field.
exact Hx.
Qed.

Theorem derivable_pt_lim_atan :
  forall x,
  derivable_pt_lim atan x (Rinv (1 + Rsqr x)).
Proof.
intros x.
apply derive_pt_eq_1 with (pr := derivable_pt_atan x).
rewrite <- (Rmult_1_l (Rinv _)).
apply derive_pt_atan.
Qed.

Definition connected (P : R -> Prop) :=
  forall x y, P x -> P y ->
  forall z, (x <= z <= y)%R -> P z.

Lemma connected_and :
  forall d1 d2, connected d1 -> connected d2 -> connected (fun t => d1 t /\ d2 t).
Proof.
intros d1 d2 H1 H2 u v [D1u D2u] [D1v D2v] t Ht.
split.
now apply H1 with (3 := Ht).
now apply H2 with (3 := Ht).
Qed.

Lemma connected_ge :
  forall x, connected (Rle x).
Proof.
intros x u v Hu _ t [Ht _].
exact (Rle_trans _ _ _ Hu Ht).
Qed.

Lemma connected_le :
  forall x, connected (fun t => Rle t x).
Proof.
intros x u v _ Hv t [_ Ht].
exact (Rle_trans _ _ _ Ht Hv).
Qed.

Theorem derivable_pos_imp_increasing :
  forall f f' dom,
  connected dom ->
 (forall x, dom x -> derivable_pt_lim f x (f' x) /\ (0 <= f' x)%R) ->
  forall u v, dom u -> dom v -> (u <= v)%R -> (f u <= f v)%R.
Proof.
intros f f' dom Hdom Hd u v Hu Hv [Huv|Huv].
assert (forall w, (u <= w <= v)%R -> derivable_pt_lim f w (f' w)).
intros w Hw.
refine (proj1 (Hd _ _)).
exact (Hdom _ _ Hu Hv _ Hw).
destruct (MVT_cor2 _ _ _ _ Huv H) as (w, (Hw1, Hw2)).
replace (f v) with (f u + (f v - f u))%R by ring.
rewrite Hw1.
pattern (f u) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply Rmult_le_pos.
refine (proj2 (Hd _ _)).
refine (Hdom _ _ Hu Hv _ _).
exact (conj (Rlt_le _ _ (proj1 Hw2)) (Rlt_le _ _ (proj2 Hw2))).
rewrite <- (Rplus_opp_r u).
unfold Rminus.
apply Rplus_le_compat_r.
exact (Rlt_le _ _ Huv).
rewrite Huv.
apply Rle_refl.
Qed.

Theorem derivable_neg_imp_decreasing :
  forall f f' dom,
  connected dom ->
 (forall x, dom x -> derivable_pt_lim f x (f' x) /\ (f' x <= 0)%R) ->
  forall u v, dom u -> dom v -> (u <= v)%R -> (f v <= f u)%R.
Proof.
intros f f' dom Hdom Hd u v Hu Hv Huv.
apply Ropp_le_cancel.
refine (derivable_pos_imp_increasing (opp_fct f) (opp_fct f') _ Hdom _ _ _ Hu Hv Huv).
intros.
destruct (Hd x H) as (H1, H2).
split.
apply derivable_pt_lim_opp with (1 := H1).
rewrite <- Ropp_0.
apply Ropp_le_contravar with (1 := H2).
Qed.

Lemma even_or_odd :
  forall n : nat, exists k, n = 2 * k \/ n = S (2 * k).
Proof.
induction n.
exists 0.
now left.
destruct IHn as [k [Hk|Hk]].
exists k.
right.
now apply f_equal.
exists (S k).
left.
omega.
Qed.

Lemma alternated_series_ineq' :
  forall u l,
  Un_decreasing u ->
  Un_cv u 0 ->
  Un_cv (fun n => sum_f_R0 (tg_alt u) n) l ->
  forall n,
  (0 <= (-1)^(S n) * (l - sum_f_R0 (tg_alt u) n) <= u (S n))%R.
Proof.
intros u l Du Cu Cl n.
destruct (even_or_odd n) as [p [Hp|Hp]].
- destruct (alternated_series_ineq u l p Du Cu Cl) as [H1 H2].
  rewrite Hp, pow_1_odd.
  split.
  + lra.
  + apply Rplus_le_reg_r with (- sum_f_R0 (tg_alt u) (2 * p))%R.
    ring_simplify.
    replace (- sum_f_R0 (tg_alt u) (2 * p) + u (S (2 * p)))%R
      with (- (sum_f_R0 (tg_alt u) (2 * p) + (-1) * u (S (2 * p))))%R by ring.
    rewrite <- (pow_1_odd p).
    now apply Ropp_le_contravar.
- assert (H0: S (S (2 * p)) = 2 * (p + 1)) by ring.
  rewrite Hp.
  rewrite H0 at 1 2.
  rewrite pow_1_even, Rmult_1_l.
  split.
  + apply Rle_0_minus.
    now apply alternated_series_ineq.
  + apply Rplus_le_reg_l with (sum_f_R0 (tg_alt u) (S (2 * p))).
    ring_simplify.
    rewrite <- (Rmult_1_l (u (S (S (2 * p))))).
    rewrite <- (pow_1_even (p + 1)).
    rewrite <- H0.
    destruct (alternated_series_ineq u l (p + 1) Du Cu Cl) as [_ H1].
    now rewrite <- H0 in H1.
Qed.

Lemma Un_decreasing_exp :
  forall x : R,
  (0 <= x <= 1)%R ->
  Un_decreasing (fun n => / INR (fact n) * x ^ n)%R.
Proof.
intros x Hx n.
change (fact (S n)) with (S n * fact n).
rewrite mult_INR.
rewrite Rinv_mult_distr.
simpl pow.
rewrite <- (Rmult_1_r (/ _ * _ ^ n)).
replace (/ INR (S n) * / INR (fact n) * (x * x ^ n))%R
  with (/ INR (fact n) * x ^ n * (/ INR (S n) * x))%R by ring.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
now apply pow_le.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
apply Hx.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
apply Hx.
now apply not_0_INR.
apply INR_fact_neq_0.
Qed.

Lemma Un_decreasing_cos :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_decreasing (fun n => / INR (fact (2 * n)) * x ^ (2 * n))%R.
Proof.
intros x Hx n.
replace (2 * S n) with (2 + 2 * n) by ring.
rewrite pow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
change (fact (2 + 2 * n)) with ((2 + 2 * n) * ((1 + 2 * n) * fact (2 * n))).
rewrite  mult_assoc, mult_comm.
rewrite mult_INR.
rewrite <- (Rmult_1_r (/ INR (fact _))).
rewrite Rinv_mult_distr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
unfold pow.
rewrite Rmult_1_r.
apply Rle_0_sqr.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
replace 1%R with (1 * (1 * 1))%R by ring.
apply pow_maj_Rabs with (1 := Hx).
apply INR_fact_neq_0.
now apply not_0_INR.
Qed.

Lemma Un_cv_subseq :
  forall (u : nat -> R) (f : nat -> nat) (l : R),
  (forall n, f n < f (S n)) ->
  Un_cv u l -> Un_cv (fun n => u (f n)) l.
Proof.
intros u f l Hf Cu eps He.
destruct (Cu eps He) as [N HN].
exists N.
intros n Hn.
apply HN.
apply le_trans with (1 := Hn).
clear -Hf.
induction n.
apply le_0_n.
specialize (Hf n).
omega.
Qed.

Definition sinc (x : R) := proj1_sig (exist_sin (Rsqr x)).

Lemma sin_sinc :
  forall x,
  sin x = (x * sinc x)%R.
Proof.
intros x.
unfold sin, sinc.
now case exist_sin.
Qed.

Lemma sinc_0 :
  sinc 0 = 1%R.
Proof.
unfold sinc.
case exist_sin.
simpl.
unfold sin_in.
intros y Hy.
apply uniqueness_sum with (1 := Hy).
intros eps He.
exists 1.
intros n Hn.
rewrite (tech2 _ 0) by easy.
simpl sum_f_R0 at 1.
rewrite sum_eq_R0.
unfold R_dist, sin_n.
simpl.
replace (1 / 1 * 1 + 0 - 1)%R with 0%R by field.
now rewrite Rabs_R0.
clear.
intros m _.
rewrite Rsqr_0, pow_i.
apply Rmult_0_r.
apply lt_0_Sn.
Qed.

Lemma Un_decreasing_sinc :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_decreasing (fun n : nat => (/ INR (fact (2 * n + 1)) * x ^ (2 * n)))%R.
Proof.
intros x Hx n.
replace (2 * S n) with (2 + 2 * n) by ring.
rewrite pow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
change (fact (2 + 2 * n + 1)) with ((2 + 2 * n + 1) * ((1 + 2 * n + 1) * fact (2 * n + 1))).
rewrite mult_assoc, mult_comm.
rewrite mult_INR.
rewrite <- (Rmult_1_r (/ INR (fact _))).
rewrite Rinv_mult_distr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
unfold pow.
rewrite Rmult_1_r.
apply Rle_0_sqr.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
rewrite <- (pow1 2).
apply pow_maj_Rabs with (1 := Hx).
apply INR_fact_neq_0.
now apply not_0_INR.
Qed.

Lemma atan_plus_PI4 :
  forall x, (-1 < x)%R ->
  (atan ((x - 1) / (x + 1)) + PI / 4)%R = atan x.
Proof.
intros x Hx.
assert (H1: ((x - 1) / (x + 1) < 1)%R).
  apply Rmult_lt_reg_r with (x + 1)%R.
  Fourier.fourier.
  unfold Rdiv.
  rewrite Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r.
  Fourier.fourier.
  apply Rgt_not_eq.
  Fourier.fourier.
assert (H2: (- PI / 2 < atan ((x - 1) / (x + 1)) + PI / 4 < PI / 2)%R).
  split.
  rewrite <- (Rplus_0_r (- PI / 2)).
  apply Rplus_lt_compat.
  apply atan_bound.
  apply PI4_RGT_0.
  apply Rplus_lt_reg_r with (-(PI / 4))%R.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
  replace (PI/2 + - (PI/4))%R with (PI/4)%R by field.
  rewrite <- atan_1.
  now apply atan_increasing.
apply tan_is_inj.
exact H2.
apply atan_bound.
rewrite atan_right_inv.
rewrite tan_plus.
rewrite atan_right_inv.
rewrite tan_PI4.
field.
split.
apply Rgt_not_eq.
Fourier.fourier.
apply Rgt_not_eq.
ring_simplify.
apply Rlt_0_2.
apply Rgt_not_eq, cos_gt_0.
unfold Rdiv.
rewrite <- Ropp_mult_distr_l_reverse.
apply atan_bound.
apply atan_bound.
rewrite cos_PI4.
apply Rgt_not_eq.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
apply Rlt_0_2.
apply Rgt_not_eq, cos_gt_0.
unfold Rdiv.
now rewrite <- Ropp_mult_distr_l_reverse.
apply H2.
rewrite tan_PI4, Rmult_1_r.
rewrite atan_right_inv.
apply Rgt_not_eq.
now apply Rgt_minus.
Qed.

Lemma atan_inv :
  forall x, (0 < x)%R ->
  atan (/ x) = (PI / 2 - atan x)%R.
Proof.
intros x Hx.
apply tan_is_inj.
apply atan_bound.
split.
apply Rlt_trans with R0.
unfold Rdiv.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_gt_0_contravar.
apply PI2_RGT_0.
apply Rgt_minus.
apply atan_bound.
apply Rplus_lt_reg_r with (atan x - PI / 2)%R.
ring_simplify.
rewrite <- atan_0.
now apply atan_increasing.
rewrite atan_right_inv.
unfold tan.
rewrite sin_shift.
rewrite cos_shift.
rewrite <- Rinv_Rdiv.
apply f_equal, sym_eq, atan_right_inv.
apply Rgt_not_eq, sin_gt_0.
rewrite <- atan_0.
now apply atan_increasing.
apply Rlt_trans with (2 := PI2_Rlt_PI).
apply atan_bound.
apply Rgt_not_eq, cos_gt_0.
unfold Rdiv.
rewrite <- Ropp_mult_distr_l_reverse.
apply atan_bound.
apply atan_bound.
Qed.

Lemma Un_decreasing_atanc :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_decreasing (fun n : nat => (/ INR (2 * n + 1) * x ^ (2 * n)))%R.
Proof.
intros x Hx n.
replace (2 * S n) with (2 + 2 * n) by ring.
rewrite pow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
rewrite <- (Rmult_1_r (/ INR (2 * n + 1))).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
unfold pow.
rewrite Rmult_1_r.
apply Rle_0_sqr.
apply Rlt_le.
apply Rinv_lt.
apply (lt_INR 0).
rewrite plus_comm.
apply lt_O_Sn.
apply lt_INR.
rewrite <- plus_assoc.
apply (plus_lt_compat_r 0).
apply lt_O_Sn.
rewrite <- (pow1 2).
apply pow_maj_Rabs with (1 := Hx).
Qed.

Lemma Un_cv_atanc :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_cv (fun n : nat => (/ INR (2 * n + 1) * x ^ (2 * n)))%R 0.
Proof.
intros x Hx eps Heps.
unfold R_dist.
destruct (archimed_cor1 eps Heps) as [N [HN1 HN2]].
exists N.
intros n Hn.
assert (H: (0 < / INR (2 * n + 1))%R).
  apply Rinv_0_lt_compat.
  apply (lt_INR 0).
  rewrite plus_comm.
  apply lt_O_Sn.
rewrite Rminus_0_r, Rabs_pos_eq.
apply Rle_lt_trans with (/ INR (2 * n + 1) * 1)%R.
apply Rmult_le_compat_l.
now apply Rlt_le.
rewrite <- (pow1 (2 * n)).
apply pow_maj_Rabs with (1 := Hx).
rewrite Rmult_1_r.
apply Rlt_trans with (2 := HN1).
apply Rinv_lt.
now apply (lt_INR 0).
apply lt_INR.
apply le_lt_trans with (1 := Hn).
clear ; omega.
apply Rmult_le_pos.
now apply Rlt_le.
rewrite pow_Rsqr.
apply pow_le.
apply Rle_0_sqr.
Qed.

Lemma atanc_exists :
  forall x,
  (Rabs x <= 1)%R ->
  { l : R | Un_cv (sum_f_R0 (tg_alt (fun n => / INR (2 * n + 1) * x ^ (2 * n))%R)) l }.
Proof.
intros x Hx.
apply alternated_series.
now apply Un_decreasing_atanc.
now apply Un_cv_atanc.
Qed.

Definition atanc x :=
  match Ratan.in_int x with
  | left H => proj1_sig (atanc_exists x (Rabs_le _ _ H))
  | right _ => (atan x / x)%R
  end.

Lemma atanc_opp :
  forall x,
  atanc (- x) = atanc x.
Proof.
intros x.
unfold atanc.
destruct (Ratan.in_int x) as [Hx|Hx] ;
  case Ratan.in_int ; intros Hx'.
do 2 case atanc_exists ; simpl projT1.
intros l1 C1 l2 C2.
apply UL_sequence with (1 := C2).
apply Un_cv_ext with (2 := C1).
intros N.
apply sum_eq.
intros n _.
unfold tg_alt.
replace (-x)%R with ((-1) * x)%R by ring.
now rewrite Rpow_mult_distr, pow_1_even, Rmult_1_l.
elim Hx'.
split.
now apply Ropp_le_contravar.
rewrite <- (Ropp_involutive 1).
now apply Ropp_le_contravar.
elim Hx.
split.
rewrite <- (Ropp_involutive x).
now apply Ropp_le_contravar.
now apply Ropp_le_cancel.
rewrite atan_opp.
field.
contradict Hx.
rewrite Hx.
split.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rle_0_1.
apply Rle_0_1.
Qed.

Lemma atan_atanc :
  forall x,
  atan x = (x * atanc x)%R.
Proof.
assert (H1: forall x, (0 < x < 1 -> atan x = x * atanc x)%R).
  intros x Hx.
  rewrite atan_eq_ps_atan with (1 := Hx).
  unfold ps_atan, atanc.
  case Ratan.in_int ; intros H.
  destruct ps_atan_exists_1 as [l1 C1].
  destruct atanc_exists as [l2 C2].
  simpl.
  clear H.
  apply UL_sequence with (1 := C1).
  apply Un_cv_ext with (fun N => x * sum_f_R0 (tg_alt (fun n => (/ INR (2 * n + 1) * x ^ (2 * n)))) N)%R.
  intros N.
  rewrite scal_sum.
  apply sum_eq.
  intros n Hn.
  unfold tg_alt, Ratan_seq.
  rewrite pow_add.
  unfold Rdiv.
  ring.
  apply CV_mult with (2 := C2).
  intros eps Heps.
  exists 0.
  intros n _.
  now rewrite R_dist_eq.
  elim H.
  split.
  apply Rle_trans with 0%R.
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  apply Rle_0_1.
  now apply Rlt_le.
  now apply Rlt_le.
assert (H2: atan 1 = Rmult 1 (atanc 1)).
  rewrite Rmult_1_l.
  rewrite atan_1.
  rewrite <- Alt_PI_eq.
  unfold Alt_PI.
  destruct exist_PI as [pi C1].
  replace (4 * pi / 4)%R with pi by field.
  unfold atanc.
  case Ratan.in_int ; intros H'.
  destruct atanc_exists as [l C2].
  simpl.
  apply UL_sequence with (1 := C1).
  apply Un_cv_ext with (2 := C2).
  intros N.
  apply sum_eq.
  intros n _.
  unfold tg_alt, PI_tg.
  now rewrite pow1, Rmult_1_r.
  elim H'.
  split.
  apply Rle_trans with (2 := Rle_0_1).
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  apply Rle_0_1.
  apply Rle_refl.
assert (H3: forall x, (0 < x -> atan x = x * atanc x)%R).
  intros x Hx.
  destruct (Req_dec x 1) as [J1|J1].
  now rewrite J1.
  generalize (H1 x).
  unfold atanc.
  case Ratan.in_int ; intros H.
  destruct (proj2 H) as [J2|J2].
  case atanc_exists ; simpl ; intros l _.
  intros K.
  apply K.
  now split.
  now elim J1.
  intros _.
  field.
  now apply Rgt_not_eq.
intros x.
destruct (total_order_T 0 x) as [[J|J]|J].
now apply H3.
rewrite <- J.
now rewrite atan_0, Rmult_0_l.
rewrite <- (Ropp_involutive x).
rewrite atan_opp, atanc_opp.
rewrite H3.
apply sym_eq, Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
Qed.

Lemma Un_decreasing_ln1pc :
  forall x : R,
  (0 <= x <= 1)%R ->
  Un_decreasing (fun n : nat => (/ INR (n + 1) * x ^ n))%R.
Proof.
intros x Hx n.
change (S n) with (1 + n) at 2.
rewrite pow_add.
simpl (pow x 1).
rewrite Rmult_1_r, <- Rmult_assoc.
apply Rmult_le_compat_r.
now apply pow_le.
rewrite <- (Rmult_1_r (/ INR (n + 1))).
apply Rmult_le_compat ; try easy.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
apply Rlt_le.
apply Rinv_lt.
apply (lt_INR 0).
rewrite plus_comm.
apply lt_O_Sn.
apply lt_INR.
apply lt_n_Sn.
Qed.

Lemma Un_cv_ln1pc :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_cv (fun n : nat => (/ INR (n + 1) * x ^ n))%R 0.
Proof.
intros x Hx eps Heps.
unfold R_dist.
destruct (archimed_cor1 eps Heps) as [N [HN1 HN2]].
exists N.
intros n Hn.
assert (H: (0 < / INR (n + 1))%R).
  apply Rinv_0_lt_compat.
  apply (lt_INR 0).
  rewrite plus_comm.
  apply lt_O_Sn.
rewrite Rminus_0_r.
rewrite Rabs_mult, Rabs_pos_eq.
apply Rle_lt_trans with (/ INR (n + 1) * 1)%R.
apply Rmult_le_compat_l.
now apply Rlt_le.
rewrite <- (pow1 n).
rewrite <- RPow_abs.
apply pow_maj_Rabs.
now rewrite Rabs_Rabsolu.
rewrite Rmult_1_r.
apply Rlt_trans with (2 := HN1).
apply Rinv_lt.
now apply (lt_INR 0).
apply lt_INR.
apply le_lt_trans with (1 := Hn).
rewrite plus_comm.
apply lt_n_Sn.
now apply Rlt_le.
Qed.

Lemma ln1pc_exists :
  forall x,
  (0 <= x < 1)%R ->
  { l : R | Un_cv (sum_f_R0 (tg_alt (fun n => / INR (n + 1) * x ^ n)%R)) l }.
Proof.
intros x Hx.
apply alternated_series.
apply Un_decreasing_ln1pc.
apply (conj (proj1 Hx)).
now apply Rlt_le.
apply Un_cv_ln1pc.
rewrite Rabs_pos_eq by easy.
now apply Rlt_le.
Qed.

Lemma ln1pc_in_int :
  forall x,
  { (0 <= x < 1)%R } + { ~(0 <= x < 1)%R }.
Proof.
intros x.
destruct (Rle_dec 0 x) as [H1|H1].
destruct (Rlt_dec x 1) as [H2|H2].
left.
now split.
right.
now contradict H2.
right.
now contradict H1.
Qed.

Definition ln1pc x :=
  match ln1pc_in_int x with
  | left H => proj1_sig (ln1pc_exists x H)
  | right _ => (ln (1 + x) / x)%R
  end.

Require Import Coquelicot.Coquelicot.

Lemma ln1p_ln1pc :
  forall x,
  ln (1 + x) = (x * ln1pc x)%R.
Proof.
intros x.
unfold ln1pc.
destruct ln1pc_in_int as [Hx|Hx].
2: field ; contradict Hx ; rewrite Hx ; split ;
  [ apply Rle_refl | apply Rlt_0_1 ].
destruct ln1pc_exists as [y Hy].
simpl.
replace y with (PSeries (fun n => (-1)^n / INR (n + 1)) x).
rewrite <- PSeries_incr_1.
replace (ln (1 + x)) with (RInt (fun t => / (1 + t)) 0 x).
rewrite <- (PSeries_ext (PS_Int (fun n => (-1)^n))).
assert (Hc: Rbar_lt (Rabs x) (CV_radius (fun n : nat => (-1) ^ n))).
  rewrite (CV_radius_finite_DAlembert _ 1).
  now rewrite Rinv_1, Rabs_pos_eq.
  intros n.
  apply pow_nonzero.
  now apply IZR_neq.
  exact Rlt_0_1.
  apply is_lim_seq_ext with (fun _ => 1%R).
    intros n.
    change ((-1)^(S n) / (-1)^n)%R with (-(1) * (-1)^n */ (-1)^n)%R.
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r, Rabs_Ropp.
    apply eq_sym, Rabs_R1.
    apply pow_nonzero.
    now apply IZR_neq.
  apply is_lim_seq_const.
rewrite <- RInt_PSeries with (1 := Hc).
apply RInt_ext.
intros t.
rewrite Rmin_left, Rmax_right by easy.
intros Ht.
rewrite <- (Ropp_involutive t) at 1.
unfold PSeries.
rewrite <- (Series_ext (fun k => (-t)^k)).
apply eq_sym, Series_geom.
rewrite Rabs_Ropp, Rabs_pos_eq.
now apply Rlt_trans with x.
now apply Rlt_le.
intros n.
replace (-t)%R with (-1 * t)%R by ring.
apply Rpow_mult_distr.
intros [|n].
easy.
unfold PS_incr_1.
now rewrite Plus.plus_comm.
apply is_RInt_unique.
assert (H: forall t, -1 < t -> is_derive (fun t : R => ln (1 + t)) t (/ (1 + t))).
  intros t Ht.
  auto_derive.
  rewrite <- (Rplus_opp_r 1).
  now apply Rplus_lt_compat_l.
  apply Rmult_1_l.
apply (is_RInt_ext (Derive (fun t => ln (1 + t)))).
  intros t.
  rewrite Rmin_left by easy.
  intros [Ht _].
  apply is_derive_unique.
  apply H.
  apply Rlt_trans with (2 := Ht).
  now apply IZR_lt.
replace (ln (1 + x)) with (ln (1 + x) - ln (1 + 0))%R.
apply (is_RInt_derive (fun t => ln (1 + t))).
  intros t.
  rewrite Rmin_left by easy.
  intros [Ht _].
  apply Derive_correct.
  eexists.
  apply H.
  apply Rlt_le_trans with (2 := Ht).
  now apply IZR_lt.
intros t.
rewrite Rmin_left by easy.
intros [Ht _].
apply continuous_ext_loc with (fun t : R => /(1 + t)).
apply locally_interval with (-1)%R p_infty.
apply Rlt_le_trans with (2 := Ht).
now apply IZR_lt.
easy.
clear t Ht.
intros t Ht _.
apply sym_eq, is_derive_unique.
now apply H.
apply continuous_comp.
apply (continuous_plus (fun t : R => 1)).
apply filterlim_const.
apply filterlim_id.
apply (filterlim_Rbar_inv (1 + t)).
apply Rbar_finite_neq.
apply Rgt_not_eq.
rewrite <- (Rplus_0_l 0).
apply Rplus_lt_le_compat with (1 := Rlt_0_1) (2 := Ht).
rewrite Rplus_0_r, ln_1.
apply Rminus_0_r.
apply is_pseries_unique.
apply is_lim_seq_Reals.
apply Un_cv_ext with (2 := Hy).
intros n.
rewrite <- sum_n_Reals.
apply sum_n_ext.
intros m.
rewrite pow_n_pow.
unfold tg_alt.
rewrite <- Rmult_assoc.
apply Rmult_comm.
Qed.

(** Define a shorter name *)
Notation Rmult_neq0 := Rmult_integral_contrapositive_currified.

Lemma Rdiv_eq_reg a b c d :
  (a * d = b * c -> b <> 0%R -> d <> 0%R -> a / b = c / d)%R.
Proof.
intros Heq Hb Hd.
apply (Rmult_eq_reg_r (b * d)).
field_simplify; trivial.
now rewrite Heq.
now apply Rmult_neq0.
Qed.

Lemma Rlt_neq_sym (x y : R) :
  (x < y -> y <> x)%R.
Proof. now intros Hxy Keq; rewrite Keq in Hxy; apply (Rlt_irrefl _ Hxy). Qed.

Lemma Rdiv_pos_compat (x y : R) :
  (0 <= x -> 0 < y -> 0 <= x / y)%R.
Proof.
intros Hx Hy.
unfold Rdiv; rewrite <- (@Rmult_0_l (/ y)).
apply Rmult_le_compat_r; trivial.
now left; apply Rinv_0_lt_compat.
Qed.

Lemma Rdiv_pos_compat_rev (x y : R) :
  (0 <= x / y -> 0 < y -> 0 <= x)%R.
Proof.
intros Hx Hy.
unfold Rdiv; rewrite <-(@Rmult_0_l y), <-(@Rmult_1_r x).
rewrite <-(Rinv_r y); [|now apply Rlt_neq_sym].
rewrite (Rmult_comm y), <-Rmult_assoc.
now apply Rmult_le_compat_r; trivial; left.
Qed.

Lemma Rdiv_neg_compat (x y : R) :
  (x <= 0 -> 0 < y -> x / y <= 0)%R.
Proof.
intros Hx Hy.
unfold Rdiv; rewrite <-(@Rmult_0_l (/ y)).
apply Rmult_le_compat_r; trivial.
now left; apply Rinv_0_lt_compat.
Qed.

Lemma Rdiv_neg_compat_rev (x y : R) :
  (x / y <= 0 -> 0 < y -> x <= 0)%R.
Proof.
intros Hx Hy.
rewrite <-(@Rmult_0_l y), <-(@Rmult_1_r x).
rewrite <-(Rinv_r y); [|now apply Rlt_neq_sym].
rewrite (Rmult_comm y), <-Rmult_assoc.
apply Rmult_le_compat_r; trivial.
now left.
Qed.

(** The following definition can be used by doing [rewrite !Rsimpl] *)
Definition Rsimpl :=
  (Rplus_0_l, Rplus_0_r, Rmult_1_l, Rmult_1_r, Rmult_0_l, Rmult_0_r, Rdiv_1).

Section Integral.

Variables (f : R -> R) (ra rb : R).
Hypothesis Hab : ra < rb.
Hypothesis Hint : ex_RInt f ra rb.

Lemma RInt_le_r (u : R) :
 (forall x : R, ra <= x <= rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
intros Hf.
apply Rle_div_l.
now apply Rgt_minus.
rewrite Rmult_comm, <- (RInt_const (V := R_CompleteNormedModule)).
apply RInt_le with (2 := Hint).
now apply Rlt_le.
apply ex_RInt_const.
intros x [Hx1 Hx2].
apply Hf.
split; now apply Rlt_le.
Qed.

Lemma RInt_le_l (l : R) :
  (forall x : R, ra <= x <= rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
intros Hf.
apply Rle_div_r.
now apply Rgt_minus.
rewrite Rmult_comm, <- (RInt_const (V := R_CompleteNormedModule)).
apply RInt_le with (3 := Hint).
now apply Rlt_le.
apply ex_RInt_const.
intros x [Hx1 Hx2].
apply Hf.
split; now apply Rlt_le.
Qed.

End Integral.

