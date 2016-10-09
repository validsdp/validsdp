(** * Bounds on the rounding error of dotproduct $c - \sum_{i=0}^k a_i b_i$#c - \sum_{i=0}^k a_i b_i#

    Notations are similar to the one in [fsum]. *)

Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.

Section Fcmdotprod.

Variable fs : Float_spec.

(** Sum [c - \sum a_i b_i] computed in float from left to right. *)
Definition fcmdotprod_l2r n (c : FS fs) (a b : FS fs ^ n) : FS fs :=
  fsum_l2r_rec c [ffun i => fopp (fmult (a i) (b i))].

Lemma fcmdotprod_l2r_eq n
      (c1 : FS fs) (a1 b1 : FS fs ^ n) (c2 : FS fs) (a2 b2 : FS fs ^ n) :
  (c1 = c2 :> R) ->
  (forall i, a1 i = a2 i :> R) -> (forall i, b1 i = b2 i :> R) ->
  fcmdotprod_l2r c1 a1 b1 = fcmdotprod_l2r c2 a2 b2 :> R.
Proof.
move=> Hc Ha Hb.
by apply fsum_l2r_rec_eq => [//|i]; rewrite !ffunE /fmult Ha Hb.
Qed.

Lemma fcmdotprod_l2r_err_gamma n (Hn : 2 * (INR n.+1) * eps fs < 1)
      (c : FS fs) (a b : FS fs ^ n) :
  exists t : b_gamma fs n,
  exists ta : (b_gamma fs n.+1 * (b_gamma fs n * b_eta fs)) ^ n,
  (fcmdotprod_l2r c a b
   = (1 + t) * c + \sum_i (- (a i * b i) + (ta i).1 * (a i * b i)
                           + (1 + (ta i).2.1) * (ta i).2.2)%Re :> R)%Re.
Proof.
set (mamb := [ffun i : 'I_n => (fopp (fmult (a i) (b i)))]).
have [t [ta Htta]] := fsum_l2r_rec_err_gamma (bg_2S Hn) c mamb.
set (F := fun i : 'I_n => ((1 + ta i) * mamb i)%Re).
set (F' := fun (i : 'I_n) (tte : b_gamma fs n.+1 * (b_gamma fs n * b_eta fs)) =>
             (- (a i * b i) + tte.1 * (a i * b i)
              + (1 + tte.2.1) * tte.2.2)%Re).
suff H : forall i, exists e, F i = F' i e.
{ have [ea Hea] := big_exists 0%R +%R (b_gamma_0 (bg_2 Hn),
                                      (b_gamma_0 (bg_S (bg_2 Hn)), eta_0 fs)) H.
  by exists t, ea; rewrite -Hea -Htta. }
move=> i.
have [d [e Hde]] := fmult_spec (a i) (b i).
have [t' Ht'] := gammap1_mult_epsp1 Hn (ta i) d.
exists (bounded_opp t', (ta i, bounded_opp e)).
rewrite /F /F' /t ffunE /fopp /= Hde.
replace (_ * - _)%Re with ((1 + ta i) * (1 + d) * (- (a i * b i))
                           + (1 + ta i) * (- e))%Re by ring.
by rewrite Ht'; ring.
Qed.

Lemma fcmdotprod_l2r_err'_gamma n (Hn : 2 * (INR n.+1) * eps fs < 1)
      (c : FS fs) (a b : FS fs ^ n) :
  exists t : b_gamma fs n,
  exists ta : (b_gamma fs n.+1 * (b_gamma fs n * b_eta fs)) ^ n,
  (fcmdotprod_l2r c a b * (1 + t)
   = c + \sum_i (- (a i * b i) + (ta i).1 * (a i * b i)
                 + (1 + (ta i).2.1) * (ta i).2.2)%Re :> R)%Re.
Proof.
set (mamb := [ffun i : 'I_n => (fopp (fmult (a i) (b i)))%Re]).
have [t [ta Htta]] := fsum_l2r_rec_err'_gamma (bg_S (bg_2 Hn)) c mamb.
set (F := fun i : 'I_n => ((1 + ta i) * mamb i)%Re).
set (F' := fun (i : 'I_n) (tte : b_gamma fs n.+1 * (b_gamma fs n * b_eta fs)) =>
             (- (a i * b i) + tte.1 * (a i * b i)
              + (1 + tte.2.1) * tte.2.2)%Re).
suff H : forall i, exists e, F i = F' i e.
{ have [ea Hea] := big_exists 0%R +%R (b_gamma_0 (bg_2 Hn),
                                      (b_gamma_0 (bg_S (bg_2 Hn)), eta_0 fs)) H.
  by exists t, ea; rewrite -Hea -Htta. }
move=> i.
have [d [e Hde]] := fmult_spec (a i) (b i).
have [t' Ht'] := gammap1_mult_epsp1 Hn (ta i) d.
exists (bounded_opp t', (ta i, bounded_opp e)).
rewrite /F /F' /t ffunE /fopp /= Hde.
replace (_ * - _)%Re with ((1 + ta i) * (1 + d) * (- (a i * b i))
                           + (1 + ta i) * (- e))%Re by ring.
by rewrite Ht'; ring.
Qed.

Lemma fcmdotprod_l2r_err n (Hn : 2 * (INR n.+1) * eps fs < 1)
      (c : FS fs) (a b : FS fs ^ n) :
  exists (t : b_gamma fs n.+1) (e : b_eta fs),
  (fcmdotprod_l2r c a b
   = c - \sum_i (a i * b i)%Re + t * (Rabs c + \sum_i Rabs (a i * b i))
     + 2 * INR n * e :> R)%Re.
Proof.
have [t [ta Htta]] := fcmdotprod_l2r_err_gamma Hn c a b.
have [t' Ht'] := big_bounded_distrl (gamma_pos (bg_2 Hn)) [ffun i => (ta i).1]
                                    [ffun i => (a i * b i)%Re].
have [t'' Ht'']  := bounded_distrl (gamma_pos (bg_2 Hn))
                                   (widen_b_gamma (leqnSn n) (bg_2 Hn) t) t'
                                   c (\sum_i (Rabs (a i * b i))).
set (F := fun i : 'I_n => ((1 + (ta i).2.1) * (ta i).2.2)%Re).
set (F' := fun (i : 'I_n) (te : b_eta fs) => (te * 2)%Re).
have H : forall i, exists e, F i = F' i e.
{ move=> i.
  have H := b_gammap1_le_2_Rabs (bg_2pred Hn) (ta i).2.1.
  have [e He] := bounded_larger_factor (Rlt_le _ _ (eta_pos fs)) (ta i).2.2 H.
  by exists e; rewrite /F Rmult_comm. }
have [ea Hea] := big_exists 0%R +%R (eta_0 fs) H.
have [e He] := big_bounded_distrl (Rlt_le _ _ (eta_pos fs)) ea [ffun=> 2].
exists t'', e.
rewrite -(Rabs_pos_eq (\sum__ (Rabs _))); [|by apply big_sum_Rabs_pos].
rewrite -Ht'' /= -big_Rabs_ffunE -Ht' Htta !big_split /= -!Rplus_assoc.
apply f_equal2; [apply f_equal2|].
{ by rewrite /Rminus big_sum_Ropp; ring_simplify. }
{ by apply eq_bigr => i; rewrite !ffunE. }
rewrite Rmult_comm (Rmult_comm 2) -big_sum_const.
have H2 : 0 <= 2; [by lra|rewrite -(big_Rabs_pos_eq _ _ (fun _ => H2))].
by rewrite -big_Rabs_ffunE -He Hea; apply eq_bigr => i; rewrite ffunE.
Qed.

Lemma fcmdotprod_l2r_err' n (Hn : 2 * (INR n.+1) * eps fs < 1)
      (c : FS fs) (a b : FS fs ^ n) :
  exists (t : b_gamma fs n) (t' : b_gamma fs n.+1) (e : b_eta fs),
  (fcmdotprod_l2r c a b * (1 + t)
   = c - \sum_i (a i * b i)%Re + t' * (\sum_i Rabs (a i * b i))
     + 2 * INR n * e :> R)%Re.
Proof.
have [t [ta Htta]] := fcmdotprod_l2r_err'_gamma Hn c a b.
have [t' Ht'] := big_bounded_distrl (gamma_pos (bg_2 Hn)) [ffun i => (ta i).1]
                                    [ffun i => (a i * b i)%Re].
set (F := fun i : 'I_n => ((1 + (ta i).2.1) * (ta i).2.2)%Re).
set (F' := fun (i : 'I_n) (te : b_eta fs) => (te * 2)%Re).
have H : forall i, exists e, F i = F' i e.
{ move=> i.
  have H := b_gammap1_le_2_Rabs (bg_2pred Hn) (ta i).2.1.
  have [e He] := bounded_larger_factor (Rlt_le _ _ (eta_pos fs)) (ta i).2.2 H.
  by exists e; rewrite /F Rmult_comm. }
have [ea Hea] := big_exists 0%R +%R (eta_0 fs) H.
have [e He] := big_bounded_distrl (Rlt_le _ _ (eta_pos fs)) ea [ffun=> 2].
exists t, t', e.
rewrite Htta !big_split /= -!Rplus_assoc /Rminus.
apply f_equal2; [apply f_equal2; [by rewrite /Rminus big_sum_Ropp|]|].
{ by rewrite -big_Rabs_ffunE -Ht'; apply eq_bigr => i; rewrite !ffunE. }
rewrite Rmult_comm (Rmult_comm 2) -big_sum_const.
have H2 : 0 <= 2; [by lra|rewrite -(big_Rabs_pos_eq _ _ (fun _ => H2))].
by rewrite -big_Rabs_ffunE -He Hea; apply eq_bigr => i; rewrite ffunE.
Qed.

Lemma fcmdotprod_l2r_err_abs n (Hn : 2 * (INR n.+1) * eps fs < 1)
      (c : FS fs) (a b : FS fs ^ n) :
  (Rabs (fcmdotprod_l2r c a b - (c - \sum_i (a i * b i)%Re))
   <= gamma fs n.+1 * (Rabs c + \sum_i Rabs (a i * b i))
      + 2 * INR n * eta fs)%Re.
Proof.
have [t [e Hte]] := fcmdotprod_l2r_err Hn c a b.
rewrite Hte.
replace (_ - _)%Re with (t * (Rabs c + \sum_i Rabs (a i * b i)%Re)
                         + 2 * INR n * e)%Re by ring.
apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat; rewrite Rabs_mult.
{ have H : 0 <= Rabs c + \sum_i Rabs (a i * b i).
  { apply Rplus_le_le_0_compat; [apply Rabs_pos|apply big_sum_Rabs_pos]. }
  by rewrite (Rabs_pos_eq (_ + _)) //; apply Rmult_le_compat_r; [|case t]. }
have H : 0 <= 2 * INR n by apply Rmult_le_pos; [lra|apply pos_INR].
by rewrite Rabs_pos_eq; [apply Rmult_le_compat_l; [|case e]|].
Qed.

End Fcmdotprod.
