(** * Bounds on the rounding error of dotproduct $\sum_{i=0}^n a_i b_i$#\sum_{i=0}^n a_i b_i#

    Notations are similar to the one in [fsum]. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.

Section Fdotprod.

Variable fs : Float_spec.

(** Sum [\sum a_i b_i] computed in float from left to right. *)
Definition fdotprod_l2r n (a b : F fs ^ n) : F fs :=
  fsum_l2r [ffun i => fmult (a i) (b i)].

Lemma fdotprod_l2r_eq n (a1 b1 : F fs ^ n) (a2 b2 : F fs ^ n) :
  (forall i, a1 i = a2 i :> R) -> (forall i, b1 i = b2 i :> R) ->
  fdotprod_l2r a1 b1 = fdotprod_l2r a2 b2 :> R.
Proof.
by move=> Ha Hb; apply fsum_l2r_eq => i; rewrite !ffunE /fmult Ha Hb.
Qed.

Lemma fdotprod_l2r_r n (a b : F fs ^ n.+2) :
  fdotprod_l2r a b
  = fplus (fdotprod_l2r [ffun i : 'I_n.+1 => a (inord i)]
                        [ffun i : 'I_n.+1 => b (inord i)])
          (fmult (a (inord n.+1)) (b (inord n.+1))) :> R.
Proof.
rewrite /fdotprod_l2r fsum_l2r_r.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ by apply fsum_l2r_eq => i; rewrite !ffunE. }
by rewrite ffunE.
Qed.
  
Lemma fdotprod_l2r_err_gamma n (Hn : 2 * INR n * eps fs < 1) (a b : F fs ^ n) :
  exists ta : (b_gamma fs n * b_eta fs) ^ n,
  (fdotprod_l2r a b
   = \sum_i (a i * b i + (ta i).1 * (a i * b i) + 2 * (ta i).2)%Re :> R)%Re.
Proof.
case: n Hn a b => [|n] Hn a b.
{ exists [ffun=> (b_gamma_0 (bg_2 Hn), eta_0 fs)].
  by rewrite big_ord0 /fdotprod_l2r /fsum_l2r. }
set (amb := [ffun i : 'I_n.+1 => fmult (a i) (b i)]).
have [ta Hta] := fsum_l2r_err_gamma (bg_2pred Hn) amb.
set (F := fun i : 'I_n.+1 => ((1 + ta i) * amb i)%Re).
set (F' := fun (i : 'I_n.+1) (tte : b_gamma fs n.+1 * b_eta fs) =>
             (a i * b i + tte.1 * (a i * b i) + 2 * tte.2)%Re).
suff H : forall i, exists e, F i = F' i e.
{ have [ea Hea] := big_exists 0%R +%R (b_gamma_0 (bg_2 Hn), eta_0 fs) H.
  by exists ea; rewrite -Hea -Hta. }
move=> i.
have [d [e Hde]] := fmult_spec (a i) (b i).
have [t' Ht'] := gammap1_mult_epsp1 Hn (ta i) d.
have H := b_gammap1_le_2_Rabs (bg_2pred Hn) (ta i).
have [e' He'] := bounded_larger_factor (Rlt_le _ _ (eta_pos fs)) e H.
exists (t', e').
rewrite /F /F' /amb ffunE Hde /=.
by rewrite !Rmult_plus_distr_l (Rmult_comm _ e) He' -Rmult_assoc Ht'; ring.
Qed.

Lemma fdotprod_l2r_err n (Hn : 2 * INR n * eps fs < 1) (a b : F fs ^ n) :
  exists t : b_gamma fs n, exists e : b_eta fs,
  (fdotprod_l2r a b
   = \sum_i (a i * b i)%Re + t * (\sum_i Rabs (a i * b i)%Re)
     + 2 * INR n * e :> R)%Re.
Proof.
have [ta Hta] := fdotprod_l2r_err_gamma Hn a b.
have [t' Ht'] := big_bounded_distrl (gamma_pos (bg_2 Hn)) [ffun i => (ta i).1]
                                    [ffun i => (a i * b i)%Re].
have [e He] := big_bounded_distrl (Rlt_le _ _ (eta_pos fs))
                                  [ffun i => (ta i).2] [ffun=> 2].
exists t'; exists e.
rewrite -big_Rabs_ffunE -Ht' Hta !big_split /=; apply f_equal2.
{ by apply Rplus_eq_compat_l, eq_big; [|move=> i; rewrite !ffunE]. }
rewrite Rmult_comm (Rmult_comm 2) -big_sum_const.
have H : 0 <= 2; [by lra|rewrite -(big_Rabs_pos_eq _ _ (fun _ => H))].
rewrite -big_Rabs_ffunE -He.
by apply eq_bigr => i; rewrite !ffunE Rmult_comm.
Qed.

Lemma fdotprod_l2r_err_abs n (Hn : 2 * INR n * eps fs < 1) (a b : F fs ^ n) :
  Rabs (fdotprod_l2r a b - \sum_i (a i * b i)%Re)
  <= gamma fs n * (\sum_i Rabs (a i * b i)) + 2 * INR n * eta fs.
Proof.
have [t [e Hte]] := fdotprod_l2r_err Hn a b.
rewrite Hte.
replace (_ - _)%Re with (t * (\sum_i Rabs (a i * b i)%Re)
                         + 2 * INR n * e)%Re by ring.
apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat; rewrite Rabs_mult.
{ rewrite (Rabs_pos_eq (\sum__ _)); [|by apply big_sum_Rabs_pos].
  apply Rmult_le_compat_r; [by apply big_sum_Rabs_pos|].
  by case t. }
have H : 0 <= 2 * INR n by apply Rmult_le_pos; [lra|apply pos_INR].
by rewrite Rabs_pos_eq; [apply Rmult_le_compat_l; [|case e]|].
Qed.

End Fdotprod.
