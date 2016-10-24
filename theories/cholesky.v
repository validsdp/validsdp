(** * Application: Proof of a positive definiteness check. *)

(** This check is based on a floating-point Cholesky decomposition.
    The proof follows the paper:
    S.M. Rump: Verification of positive definiteness,
    BIT Numerical Mathematics, 46:433-452, 2006. *)

Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.algebra.matrix mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum fcmdotprod real_matrix.

Section Cholesky.

Variable fs : Float_spec.

(** ** Lemmas about error of basic blocks of cholesky decomposition.

    (Corresponds to lemmas 2.1 and 2.2 in the paper.) *)
Section Error_lemmas.

(** Sum [c - \sum a_i b_i] computed in float from left to right. *)
Definition stilde := fcmdotprod_l2r.

Lemma stilde_le_c k (c : FS fs) (a : FS fs ^ k) : (stilde c a a <= c)%Re.
Proof.
elim: k c a => [|k IHk] c a; [by right|].
rewrite /stilde /fcmdotprod_l2r /= ffunE.
replace (FS_val _)
with (FS_val (stilde (fplus c (fopp (fmult (a ord0) (a ord0))))
                    [ffun i => a (lift ord0 i)] [ffun i => a (lift ord0 i)])).
{ apply (Rle_trans _ _ _ (IHk _ _)).
  apply fplus_spec2; rewrite -Ropp_0; apply Ropp_le_contravar, fmult_spec2. }
by apply fsum_l2r_rec_eq => [//|i]; rewrite !ffunE.
Qed.

(** *** Lemma 2.1. *)
Section Lemma_2_1.

(** (2.2) *)
Definition ytilded (k : nat) (c : FS fs) (a b : FS fs ^ k) (bk : FS fs) :=
  fdiv (stilde c a b) bk.

Lemma ytilded_eq k
      (c1 : FS fs) (a1 b1 : FS fs ^ k) (bk1 : FS fs)
      (c2 : FS fs) (a2 b2 : FS fs ^ k) (bk2 : FS fs) :
  (c1 = c2 :> R) -> (forall i, a1 i = a2 i :> R) ->
  (forall i, b1 i = b2 i :> R) -> (bk1 = bk2 :> R) ->
  ytilded c1 a1 b1 bk1 = ytilded c2 a2 b2 bk2 :> R.
Proof.
by move=> Hc Ha Hb Hbk; rewrite /ytilded /fdiv (fcmdotprod_l2r_eq Hc Ha Hb) Hbk.
Qed.

(* begin hide *)
(** ~(2.5) *)
Lemma lemma_2_1_aux1 k (H2k : 2 * (INR k.+1) * eps fs < 1)
      (a b : FS fs ^ k) (c bk : FS fs) (Hbk : bk <> 0 :> R) :
  exists (t : b_gamma fs k) (d : b_eps fs) (t' : b_gamma fs k.+1)
         (e : b_eta fs) (e' : b_eta fs),
  (ytilded c a b bk * bk * (1 + t) / (1 + d)
   = c - \sum_i (a i * b i)%Re + t' * (\sum_i Rabs (a i * b i)%Re)
     + 2 * INR k * e + bk * (1 + t) * e' / (1 + d) :> R)%Re.
Proof.
have [t [t' [e Htt'e]]] := fcmdotprod_l2r_err' H2k c a b.
have [d [e' Hde]] := fdiv_spec (stilde c a b) bk.
exists t, d, t', e, e'; rewrite Hde.
by replace (_ / (1 + d))%Re
   with (stilde c a b * (1 + t) + bk * (1 + t) * e' / (1 + d))%Re;
  [rewrite Htt'e|by field; split; [|bounded_lra fs]].
Qed.

Lemma lemma_2_1_aux2 k (H2k : 2 * (INR k.+1) * eps fs < 1)
      (a b : FS fs ^ k) (c bk : FS fs) (Hbk : bk <> 0 :> R) :
  exists (t : b_gamma fs k.+1) (t' : b_gamma fs k.+1) (e : b_eta fs),
  (ytilded c a b bk * bk
   = t * ytilded c a b bk * bk
     + c - \sum_i (a i * b i)%Re + t' * (\sum_i Rabs (a i * b i)%Re)
     + 2 * e * (INR k + Rabs bk) :> R)%Re.
Proof.
have [t [d [t' [e [e' Htdt]]]]] := lemma_2_1_aux1 H2k a b c Hbk.
have [tn Htn] := (gammap1_div_epsp1 (bg_2 H2k) t d).
have H : (Rabs ((1 + t) / (1 + d) * bk) <= Rabs (2 * bk))%Re.
{ rewrite Htn !Rabs_mult.
  by apply Rmult_le_compat_r; [apply Rabs_pos|apply b_gammap1_le_2_Rabs]. }
have [e'n He'n] := bounded_larger_factor (Rlt_le 0 (eta fs) (eta_pos fs)) e' H.
have [en Hen] := bounded_distrl (Rlt_le 0 (eta fs) (eta_pos fs)) e e'n
                                (2 * INR k)%Re (2 * bk)%Re.
exists (bounded_opp tn), t', en; simpl.
apply (Rplus_eq_reg_r (tn * ytilded c a b bk * bk)%Re).
replace (_ * bk + _)%Re with (ytilded c a b bk * bk * (1 + tn))%Re by ring.
rewrite -Htn -Rmult_assoc -/(Rdiv _ _) Htdt.
apply (Rplus_eq_reg_l (- c + \sum_i (a i * b i)%Re
                             - t' * \sum_i Rabs (a i * b i)%Re)%Re);
  simpl; ring_simplify.
replace (_ + _)%Re with (e * (2 * INR k) + e' * ((1 + t) / (1 + d) * bk))%Re;
  [|by rewrite /Rdiv; ring].
rewrite He'n Hen !Rabs_mult.
rewrite Rabs_pos_eq; [|lra]; rewrite Rabs_pos_eq; [|by apply pos_INR].
ring.
Qed.

(* end hide *)
Lemma lemma_2_1 k (H2k : 2 * (INR k.+1) * eps fs < 1)
      (a b : FS fs ^ k) (c bk : FS fs) (Hbk : bk <> 0 :> R) :
  (Rabs (c - \sum_i (a i * b i)%Re - bk * ytilded c a b bk)
   < gamma fs k.+1 * ((\sum_i Rabs (a i * b i)%Re)
                      + Rabs (bk * ytilded c a b bk))
     + 2 * eta fs * (INR k.+1 + Rabs bk)).
Proof.
have [t [t' [e Htt'e]]] := lemma_2_1_aux2 H2k a b c Hbk.
rewrite Rabs_minus_sym (Rmult_comm bk) {1}Htt'e.
match goal with | |- context [(Rabs ?X)] => ring_simplify X end.
rewrite Rplus_assoc -Rmult_plus_distr_l Rmult_assoc (Rplus_comm (t * _)).
have [t'' Ht''] := bounded_distrl (gamma_pos (bg_2 H2k)) t' t
                                  (\sum_i Rabs (a i * b i)%Re)
                                  (ytilded c a b bk * bk)%Re.
rewrite Ht''.
apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)), Rplus_le_lt_compat.
{ rewrite Rabs_mult; apply Rmult_le_compat;
  [by apply Rabs_pos|by apply Rabs_pos|by case t''|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite !Rabs_Rabsolu.
  by rewrite Rabs_pos_eq; [by right|apply big_sum_Rabs_pos]. }
rewrite !Rabs_mult !Rmult_assoc; rewrite Rabs_right; [|lra].
apply Rmult_lt_compat_l; [lra|].
apply Rle_lt_trans with (eta fs * (INR k + Rabs bk))%Re.
{ apply Rmult_le_compat;
  [by apply Rabs_pos|by apply Rabs_pos|by case e|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_Rabsolu.
  by rewrite Rabs_pos_eq; [right|apply pos_INR]. }
rewrite S_INR; fs_lra fs.
Qed.

End Lemma_2_1.

(** *** Lemma 2.2. *)
Section Lemma_2_2.

Definition ytildes (k : nat) (c : FS fs) (a : FS fs ^ k) := fsqrt (stilde c a a).

Lemma ytildes_eq k (c1 : FS fs) (a1 : FS fs ^ k) (c2 : FS fs) (a2 : FS fs ^ k) :
  (c1 = c2 :> R) -> (forall i, a1 i = a2 i :> R) ->
  ytildes c1 a1 = ytildes c2 a2 :> R.
Proof.
by move=> Hc Ha; rewrite /ytildes /fsqrt (fcmdotprod_l2r_eq Hc Ha Ha).
Qed.

(* begin hide *)
Lemma lemma_2_2_aux1 k (H2k : 2 * (INR k.+1) * eps fs < 1)
      (a : FS fs ^ k) (c : FS fs) (Hst : 0 <= stilde c a a) :
  exists (t : b_gamma fs k) (d : b_eps fs)
         (t' : b_gamma fs k.+1) (e : b_eta fs),
  ((ytildes c a) ^ 2 * (1 + t) / (1 + d) ^ 2
   = c - \sum_i (a i * a i)%Re + t' * (\sum_i Rabs (a i * a i)%Re)
     + 2 * INR k * e :> R)%Re.
Proof.
have [t [t' [e Htt'e]]] := fcmdotprod_l2r_err' H2k c a a.
have [d Hd] := fsqrt_spec (stilde c a a).
exists t, d, t', e; rewrite Hd.
replace (_ / _ ^ 2)%Re with ((sqrt (stilde c a a)) ^ 2 * (1 + t))%Re;
  [|by field; bounded_lra fs].
by rewrite /= Rmult_1_r sqrt_def; [rewrite Htt'e|].
Qed.

Lemma lemma_2_2_aux2 k (H2k : 2 * (INR k.+2) * eps fs < 1)
      (a : FS fs ^ k) (c : FS fs) (Hst : 0 <= stilde c a a) :
  exists (t : b_gamma fs k.+2) (t' : b_gamma fs k.+1) (e : b_eta fs),
  ((ytildes c a) ^ 2
   = t * (ytildes c a) ^ 2
     + c - \sum_i (a i * a i)%Re + t' * (\sum_i (a i * a i)%Re)
     + 2 * INR k * e :> R)%Re.
Proof.
have [t [d [t' [e Htdt]]]] := lemma_2_2_aux1 (bg_2S H2k) Hst.
have [tn Htn] := gammap1_div_epsp1 (bg_S (bg_2 H2k)) t d.
have [tn' Htn'] := gammap1_div_epsp1 (bg_2 H2k) tn d.
exists (bounded_opp tn'), t', e; simpl.
have Hsa : (\sum_i (a i * a i)%Re = \sum_i Rabs (a i * a i)%Re :> R)%Re.
{ by apply /eq_bigr => i; rewrite Rabs_pos_eq; [|apply sqr_ge_0]. }
rewrite {2}Hsa; apply (Rplus_eq_reg_r (tn' * ytildes c a ^ 2)%Re).
replace (_ + _)%Re with (ytildes c a ^ 2 * (1 + tn'))%Re by ring.
rewrite -Htn' -Htn.
replace (_ * (_ / _))%Re with (ytildes c a ^ 2 * (1 + t) / (1 + d) ^ 2)%Re;
  [|by field; bounded_lra fs].
rewrite Htdt /=; ring.
Qed.

(* end hide *)
Lemma lemma_2_2_1 k (H2k : 2 * (INR k.+2) * eps fs < 1)
      (a : FS fs ^ k) (c : FS fs) (Hst : 0 <= stilde c a a) :
  (Rabs (c - \sum_i (a i * a i)%Re - ytildes c a ^ 2)
   < gamma fs k.+2 * ((\sum_i (a i * a i)%Re) + ytildes c a ^ 2)
     + 2 * eta fs * (INR k.+1)).
Proof.
have [t [t' [e Htt'e]]] := lemma_2_2_aux2 H2k Hst.
rewrite Rabs_minus_sym {1}Htt'e.
match goal with | |- context [(Rabs ?X)] => ring_simplify X end.
rewrite (Rmult_comm _ t') (Rplus_comm (t * _)).
have [t'' Ht''] := bounded_distrl (gamma_pos (bg_2 H2k))
                                  (widen_b_gamma (leqnSn k.+1) (bg_2 H2k) t') t
                                  (\sum_i (a i * a i)%Re)
                                  (ytildes c a ^ 2)%Re.
rewrite Ht''.
apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)), Rplus_le_lt_compat.
{ rewrite Rabs_mult; apply Rmult_le_compat;
  [by apply Rabs_pos|by apply Rabs_pos|by case t''|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite !Rabs_Rabsolu.
  rewrite (Rabs_pos_eq (_ ^ 2)); [|by apply pow2_ge_0].
  apply Rplus_le_compat_r; rewrite Rabs_pos_eq; [by right|].
  apply big_sum_sqr_pos. }
rewrite !Rabs_mult !Rmult_assoc; rewrite Rabs_right; [|lra].
apply Rmult_lt_compat_l; [lra|rewrite Rmult_comm].
apply Rle_lt_trans with (eta fs * INR k)%Re.
{ rewrite (Rabs_pos_eq (INR k)); [|by apply pos_INR].
  by apply Rmult_le_compat_r; [apply pos_INR|case e]. }
rewrite S_INR; fs_lra fs.
Qed.

Lemma lemma_2_2_2 k (H2k : 2 * (INR k.+2) * eps fs < 1)
      (a : FS fs ^ k) (c : FS fs) (Hst : 0 <= stilde c a a) :
  (ytildes c a ^ 2 + \sum_i (a i * a i)%Re
   <= / (1 - gamma fs k.+2) * (c + 2 * eta fs * INR k))%Re.
Proof.
have Hg := gamma_lt_1 H2k.
apply (Rmult_le_reg_l (1 - gamma fs k.+2)); [lra|].
replace (_ * (/ _ * _))%Re with (c + 2 * eta fs * INR k)%Re; [|field; lra].
have [t [t' [e Htt'e]]] := lemma_2_2_aux2 H2k Hst.
have H : ((1 - t) * ytildes c a ^ 2 + (1 - t') * (\sum_i (a i * a i)%Re)
          = c + 2 * INR k * e)%Re.
{ ring_simplify; rewrite {2}Htt'e; ring. }
apply Rle_trans with (c + 2 * INR k * e)%Re.
{ rewrite -H Rmult_plus_distr_l; apply Rplus_le_compat.
  { apply Rmult_le_compat_r; [apply pow2_ge_0|bounded_lra fs]. }
  apply Rmult_le_compat_r; [by apply big_sum_sqr_pos|].
  apply Rplus_le_compat_l, Ropp_le_contravar.
  apply Rle_trans with (gamma fs k.+1);
    [bounded_lra fs|by apply gamma_monotone; [|apply bg_2]]. }
apply Rplus_le_compat_l.
rewrite (Rmult_assoc _ (eta fs)) (Rmult_comm (eta fs)) -Rmult_assoc.
apply Rmult_le_compat_l; [by apply Rmult_le_pos; [lra|apply pos_INR]|].
bounded_lra fs.
Qed.

End Lemma_2_2.

End Error_lemmas.

(** ** Definition of Cholesky decomposition and main theorem (Theorem 2.3). *)
Section Cholesky_def.

(** It is sometime needed to explicitly cast the matrices to R. *)
Definition MF2R n m (M : 'M[FS fs]_(n, m)) : 'M[R]_(n, m) :=
  map_mx (@FS_val (format fs)) M.

Variable n : nat.

Hypothesis H2n : 2 * INR n.+2 * eps fs < 1.

(** The matrix we want to prove positive definite. *)
Variable A : 'M[FS fs]_n.+1.

(** Must be symmetric. *)
Hypothesis SymA : MF2R A^T = MF2R A.

(** [Rt] is meant to be the (floating point computed) Cholesky factor of [A]. *)
Variable Rt : 'M[FS fs]_n.+1.

(** [cholesky_spec] means that, in case floating point Cholesky
    decomposition runs to completion, [Rt] is the floating point Cholesky factor
    of [A] (i.e. [Rte^T * Rte] would be equal to [A] if there were
    no rounding errors). Note: this is (2.1) in paper. *)
Definition cholesky_spec : Prop :=
  (forall (j i : 'I_n.+1),
     (i < j)%N ->
     (Rt i j = ytilded (A i j)
                       [ffun k : 'I_i => Rt (inord k) i]
                       [ffun k : 'I_i => Rt (inord k) j]
                       (Rt i i) :> R))
  /\ (forall (j : 'I_n.+1),
        (Rt j j = ytildes (A j j) [ffun k : 'I_j => Rt (inord k) j] :> R)).

(** [cholesky_success] means [cholesky_spec] and floating point Cholesky
    decomposition runs to completion. *)
Definition cholesky_success : Prop :=
  cholesky_spec /\ forall i, (0 < Rt i i)%Re.

Hypothesis HAR : cholesky_success.

Variable maxdiag : R.

Hypothesis Hmaxdiag : forall i : 'I_n.+1, A i i <= maxdiag.

(** *** A bunch of definitions used in the following theorem and corollaries. *)

(** [Rt] casted to R plus filled with zeros in the bottom triangular part
    (the diagonal and upper triangular part of [Rt] are kept). *)
Let Rte := \matrix_(i, j) if (i <= j)%N then (Rt i j : R) else 0.

Let rt (j : 'I_n.+1) : 'cV[R]_n.+1 := col j Rte.

Let alpha (i j : nat) : R := gamma fs (min i j).+2.

Let d (j : 'I_n.+1) : R :=
  sqrt (/ (1 - alpha j j) * (A j j + 2 * INR j * eta fs))%Re.

Let delta : 'M[R]_n.+1 := (MF2R A) - (Rte^T *m Rte).

Definition Delta : 'M[R]_n.+1 :=
  \matrix_(i, j) (alpha i j * d i * d j
                  + 4 * eta fs * (INR n.+2 + maxdiag)).

(** A bunch of lemmas. *)
Lemma alpha_pos (i j : 'I_n.+1) : 0 <= alpha i j.
Proof.
apply gamma_pos, bg_2, (@bg_2_le _ _ n.+2); [|by []].
rewrite (ltn_add2l 1); apply Min.min_case; apply ltn_ord.
Qed.

Lemma alpha_gamma i j : (i <= j)%N -> alpha i j = gamma fs i.+2.
Proof. by move=> Hij; rewrite /alpha min_l //; apply /leP. Qed.

Lemma alpha_sym i j : alpha i j = alpha j i.
Proof. by rewrite /alpha; rewrite Min.min_comm. Qed.

Lemma delta_sym (i j : 'I_n.+1) : delta i j = delta j i.
Proof.
rewrite !mxE /GRing.add /GRing.opp /=.
apply f_equal2; [|apply f_equal].
{ by replace (FS_val _) with (MF2R A i j); [rewrite -SymA|]; rewrite !mxE. }
by apply /eq_bigr => k; rewrite /GRing.mul /= Rmult_comm !mxE.
Qed.

Lemma dotprod_rt_i_j (i j : 'I_n.+1) : (i <= j)%N ->
  dotprod (rt i) (rt j)
  = (Rt i i * Rt i j
     + \sum_(k < i)
        ([ffun k : 'I_i => Rt (inord k) i] k
         * [ffun k : 'I_i => Rt (inord k) j] k)%Re)%Re.
Proof.
move=> Hij; rewrite dotprod_sum.
have H : \sum_k (rt i k ord0 * rt j k ord0)%Re
         = \sum_(0 <= k < n.+1)
            (rt i (inord k) ord0 * rt j (inord k) ord0)%Re.
{ rewrite big_mkord; apply /eq_bigr => k _.
  by apply f_equal2; (apply f_equal2; [rewrite inord_val|]). }
rewrite H {H} (big_cat_nat _ _ _ (leq0n i.+1) (ltn_ord i)) /=.
have H : ((\sum_(i.+1 <= k < n.+1) (rt i (inord k) ord0
                                    * rt j (inord k) ord0)) = 0)%Re.
{ rewrite (@big_addn _ _ _ 0 n.+1 i.+1) big_mkord.
  apply big_rec => [//|k x _ ->]; rewrite GRing.addr0.
  rewrite !mxE ifF; [by rewrite GRing.mul0r|].
  rewrite inordK; [by rewrite /leq -addSnnS addnK|].
  move: k; case i => iv ip /=; case=> kv kp /=.
  by rewrite -(subnK ip) ltn_add2r. }
rewrite H {H} GRing.addr0 big_mkord big_ord_recr /= Rplus_comm; apply f_equal2.
{ apply eq_bigr => k _; rewrite !mxE !ffunE.
  suff H : (@inord n k <= i)%N.
  { by rewrite ifT; [rewrite ifT; [|apply (leq_trans H)]|]. }
  rewrite inordK; [apply ltnW|apply ltn_trans with i]; apply ltn_ord. }
have H : (@inord n i = i)%N by rewrite inord_val.
by rewrite !mxE ifT; [rewrite ifT|]; rewrite H.
Qed.

Lemma dotprod_Mabs_rt_i_j (i j : 'I_n.+1) : (i <= j)%N ->
  dotprod (Mabs (rt i)) (Mabs (rt j))
  = (Rabs (Rt i i * Rt i j)
     + \sum_k Rabs
        ([ffun k : 'I_i => Rt (inord k) i] k
         * [ffun k : 'I_i => Rt (inord k) j] k)%Re)%Re.
Proof.
move=> Hij; rewrite dotprod_sum.
have H : \sum_k ((Mabs (rt i)) k ord0 * (Mabs (rt j)) k ord0)%Re
         = \sum_(0 <= k < n.+1)
            ((Mabs (rt i)) (inord k) ord0 * (Mabs (rt j)) (inord k) ord0)%Re.
{ rewrite big_mkord; apply /eq_bigr => k _.
  by apply f_equal2; (apply f_equal2; [rewrite inord_val|]). }
rewrite H {H} (big_cat_nat _ _ _ (leq0n i.+1) (ltn_ord i)) /=.
have H : ((\sum_(i.+1 <= k < n.+1) ((Mabs (rt i)) (inord k) ord0
                                    * (Mabs (rt j)) (inord k) ord0)) = 0)%Re.
{ rewrite (@big_addn _ _ _ 0 n.+1 i.+1) big_mkord.
  apply big_rec => [//|k x _ ->]; rewrite GRing.addr0.
  rewrite !mxE ifF; [by rewrite Rabs_R0 GRing.mul0r|].
  rewrite inordK; [by rewrite /leq -addSnnS addnK|].
  move: k; case i => iv ip /=; case=> kv kp /=.
  by rewrite -(subnK ip) ltn_add2r. }
rewrite H {H} GRing.addr0 big_mkord big_ord_recr /= Rplus_comm; apply f_equal2.
{ apply eq_bigr => k _; rewrite !mxE !ffunE.
  suff H : (@inord n k <= i)%N.
  { by rewrite Rabs_mult ifT; [rewrite ifT; [|apply (leq_trans H)]|]. }
  rewrite inordK; [apply ltnW|apply ltn_trans with i]; apply ltn_ord. }
have H : (@inord n i = i)%N by rewrite inord_val.
by rewrite Rabs_mult !mxE ifT; [rewrite ifT|]; rewrite H.
Qed.

Lemma Mmul_abs_lr (x : 'cV_n.+1) (B C : 'M_n.+1) :
  B <=m: C -> (Mabs x)^T *m B *m Mabs x <=m: (Mabs x)^T *m C *m Mabs x.
Proof.
move=> H; apply Mmul_le_compat_r; [by apply Mabs_pos|].
by apply Mmul_le_compat_l; [by rewrite -(trmx0); apply Mle_tr, Mabs_pos|].
Qed.

(** (2.7) *)
Lemma th_2_3_aux1_aux (j : 'I_n.+1) : (||rt j||_2^2 <= (d j)^2)%Re.
Proof.
have H2j := bg_2_le (leq_add (leqnn 1) (ltn_ord j)) H2n.
rewrite norm2_sqr_dotprod dotprod_rt_i_j //.
set (c := A j j).
set (a := [ffun i : 'I_j => Rt (inord i) j]).
replace (Rt j j * Rt j j)%Re with (ytildes c a ^ 2)%Re;
  [|by rewrite (proj2 (proj1 HAR)) /= Rmult_1_r].
have Hsaa : (0 <= stilde c a a)%Re.
{ apply Rlt_le, fsqrt_spec2.
  rewrite -/(ytildes c a) -(proj2 (proj1 HAR)); apply HAR. }
apply (Rle_trans _ _ _ (lemma_2_2_2 H2j Hsaa)).
have H : (c + 2 * eta fs * INR j = A j j + 2 * INR j * eta fs)%Re.
{ by apply f_equal2; [|ring]. }
rewrite /d -H {H} alpha_gamma //= Rmult_1_r sqrt_def; [by right|].
apply Rmult_le_pos.
{ have H := @gamma_lt_1 _ j.+2 H2j.
  apply (Rmult_le_reg_r (1 - gamma fs j.+2)%Re); field_simplify; lra. }
apply Rplus_le_le_0_compat; [by apply (Rle_trans _ _ _ Hsaa), stilde_le_c|].
by apply Rmult_le_pos; [fs_lra fs|apply pos_INR].
Qed.

(** (2.7) *)
Lemma th_2_3_aux1 (j : 'I_n.+1) : (||rt j||_2 <= d j)%Re.
Proof.
move: (th_2_3_aux1_aux j).
rewrite /= !Rmult_1_r -!/(Rsqr _) => H.
by apply Rsqr_incr_0; [|apply norm2_pos|rewrite /d; apply sqrt_pos].
Qed.

(** (2.8) *)
Lemma th_2_3_aux2_aux1 (i j : 'I_n.+1) : (i < j)%N ->
  forall maxdiag', (forall i, (Rt i i <= maxdiag')%Re) ->
  (Rabs (delta i j)
   < alpha i j * dotprod (Mabs (rt i)) (Mabs (rt j))
     + 2 * eta fs * (INR n.+1 + maxdiag'))%Re.
Proof.
move=> Hij maxdiag' Hmaxdiag'.
rewrite 3!mxE mulmx_dotprod trmxK dotprod_rt_i_j; [|by apply ltnW].
set (c := A i j).
set (a := [ffun k : 'I_i => Rt (inord k) i]).
set (b := [ffun k : 'I_i => Rt (inord k) j]).
set (bk := Rt i i).
have Hrtij : Rt i j = ytilded c a b bk :> R.
{ by rewrite (proj1 (proj1 HAR) _ _ Hij). }
rewrite Hrtij.
have Hbk : (bk <> 0 :> R)%Re.
{ rewrite /bk; apply Rgt_not_eq, Rlt_gt, (proj2 HAR). }
replace (_ - _ : R) with (c - (\sum_k (a k * b k)%Re)
                          - bk * ytilded c a b bk)%Re;
  [|by rewrite /GRing.add /GRing.opp /c /=;
    change (FS_of (format fs)) with (FS fs); ring].
apply (Rlt_le_trans _ _ _
                    (lemma_2_1 (bg_2_le (ltn_ord i) (bg_2S H2n)) a b c Hbk)).
rewrite /bk -Hrtij.
apply Rplus_le_compat.
{ rewrite alpha_gamma; [|by apply ltnW].
  rewrite dotprod_Mabs_rt_i_j; [|by apply ltnW].
  rewrite Rplus_comm /a /b; apply Rmult_le_compat_r.
  { by apply Rplus_le_le_0_compat; [apply Rabs_pos|apply big_sum_Rabs_pos]. }
  by apply gamma_monotone; [|apply bg_2S2, (bg_2_le (ltn_ord i)), bg_2S]. }
apply Rmult_le_compat_l; [fs_lra fs|].
apply Rplus_le_compat; [by apply /le_INR /leP /ltn_ord|].
rewrite Rabs_pos_eq; [apply Hmaxdiag'|apply Rlt_le, (proj2 HAR)].
Qed.

Lemma th_2_3_aux2_aux2 (i : 'I_n.+1) :
  forall maxdiag', (forall i, (Rt i i <= maxdiag')%Re) ->
  (Rabs (delta i i)
   < alpha i i * dotprod (Mabs (rt i)) (Mabs (rt i))
     + 2 * eta fs * (INR n.+1 + maxdiag'))%Re.
Proof.
move=> maxdiag' Hmaxdiag'.
have H2i := bg_2_le (leq_add (leqnn 1) (ltn_ord i)) H2n.
rewrite 3!mxE mulmx_dotprod trmxK dotprod_rt_i_j; [|by apply leqnn].
set (c := A i i).
set (a := [ffun k : 'I_i => Rt (inord k) i]).
have Hrtij : Rt i i = ytildes c a :> R by rewrite (proj2 (proj1 HAR)).
rewrite Hrtij.
have Hst : (0 <= stilde c a a)%Re.
{ apply Rlt_le, fsqrt_spec2; rewrite -Hrtij; apply HAR. }
replace (_ - _ : R) with (c - (\sum_k (a k * a k)%Re) - ytildes c a ^ 2)%Re;
  [|by rewrite /GRing.add /GRing.opp /c /=;
    change (FS_of (format fs)) with (FS fs); ring_simplify].
apply (Rlt_le_trans _ _ _ (lemma_2_2_1 H2i Hst)).
apply Rplus_le_compat.
{ rewrite alpha_gamma //; apply Rmult_le_compat_l; [by apply gamma_pos, bg_2|].
  rewrite dotprod_Mabs_rt_i_j // Rplus_comm /= Rmult_1_r -Hrtij; right.
  rewrite Rabs_pos_eq; [|by apply sqr_ge_0]; apply Rplus_eq_compat_l.
  by apply eq_bigr => k; rewrite !ffunE Rabs_pos_eq; [|apply sqr_ge_0]. }
apply Rmult_le_compat_l; [fs_lra fs|rewrite -(Rplus_0_r (INR _))].
apply Rplus_le_compat; [by apply /le_INR /leP /ltn_ord|].
apply Rlt_le, (Rlt_le_trans _ _ _ ((proj2 (HAR)) ord0)), Hmaxdiag'.
Qed.

Lemma th_2_3_aux2 (i j : 'I_n.+1) :
  forall maxdiag', (forall i, (Rt i i <= maxdiag')%Re) ->
  (Rabs (delta i j)
   < alpha i j * dotprod (Mabs (rt i)) (Mabs (rt j))
     + 2 * eta fs * (INR n.+1 + maxdiag'))%Re.
Proof.
case (ltnP i j) => Hij; [by apply th_2_3_aux2_aux1|].
case (ltnP j i) => Hji.
{ move=> maxdiag' Hmaxdiag'.
  by rewrite delta_sym alpha_sym dotprod_sym; apply th_2_3_aux2_aux1. }
suff H : i = j by rewrite H; apply th_2_3_aux2_aux2.
by apply /ord_inj /anti_leq /andP.
Qed.

Lemma th_2_3_aux3_aux i : (Rt i i <= 2 * (maxdiag + 1))%Re.
Proof.
rewrite (proj2 (proj1 HAR)) /ytildes.
set (a := [ffun k : 'I_i => Rt (inord k) i]).
have Hst : (0 <= stilde (A i i) a a).
{ apply Rlt_le, fsqrt_spec2; rewrite -/(ytildes _ _).
  rewrite -(proj2 (proj1 HAR)); apply HAR. }
have [d' Hd'] := fsqrt_spec (stilde (A i i) a a); rewrite Hd'.
apply Rmult_le_compat; [bounded_lra fs|by apply sqrt_pos|bounded_lra fs|].
apply (Rle_trans _ _ _ (sqrtx_le_xp1 Hst)), Rplus_le_compat_r.
by apply (Rle_trans _ _ _ (stilde_le_c _ _)).
Qed.

Lemma th_2_3_aux3 (i j : 'I_n.+1) :
  (Rabs (delta i j)
   < alpha i j * ||rt i||_2 * ||rt j||_2
     + 4 * eta fs * (INR n.+2 + maxdiag))%Re.
Proof.
have Hmd : forall i0 : 'I_n.+1, Rt i0 i0 <= 2 * (maxdiag + 1);
  [by move=> k; apply th_2_3_aux3_aux|].
apply (Rlt_le_trans _ _ _ (th_2_3_aux2 _ _ Hmd)), Rplus_le_compat.
{ rewrite Rmult_assoc; apply Rmult_le_compat_l; [by apply alpha_pos|].
  rewrite -norm2_mabs -(norm2_mabs (rt j)); apply cauchy_schwarz. }
replace (4 * _ * _)%Re with (2 * eta fs * (2 * (INR n.+2 + maxdiag)))%Re
  by ring.
apply Rmult_le_compat_l; [fs_lra fs|].
rewrite (S_INR n.+1); move: (pos_INR n.+1); lra.
Qed.

(** (2.9) *)
Lemma th_2_3_aux4 : Mabs delta <m: Delta.
Proof.
move=> i j; rewrite mxE.
apply (Rlt_le_trans _ _ _ (th_2_3_aux3 i j)).
rewrite mxE; apply Rplus_le_compat_r; rewrite /GRing.mul /= 2!Rmult_assoc.
apply Rmult_le_compat_l; [by apply alpha_pos|].
apply Rmult_le_compat; try apply norm2_pos; apply th_2_3_aux1.
Qed.

(** Main theorem. *)
Lemma th_2_3 (x : 'cV_n.+1) : x <> 0 ->
  - ((Mabs x)^T *m Delta *m Mabs x) <m: x^T *m (MF2R A) *m x.
Proof.
move=> Nzx.
apply Mlt_le_trans with (- ((Mabs x)^T *m Mabs delta *m Mabs x)).
{ apply Mopp_lt_contravar.
  apply Mmulv_lt_compat_r; [by apply Mabs_pos|by apply Mabs_no_0|].
  apply Mmulv_lt_compat_l; [by apply Mabs_pos|by apply Mabs_no_0|].
  by apply th_2_3_aux4. }
apply Mle_trans with (- Mabs (x^T *m delta *m x)).
{ apply Mopp_le_contravar, (Mle_trans (Mabs_mul _ _)); rewrite map_trmx.
  apply Mmul_le_compat_r; [apply Mabs_pos|apply Mabs_mul]. }
apply (Mle_trans (Mge_opp_abs _)).
rewrite /delta mulmxBr mulmxBl -{2}(GRing.subr0 (_ *m _)).
apply Madd_le_compat_l, Mopp_le_contravar, mxtrmx_semipos.
Qed.

End Cholesky_def.

(** ** Corollaries of previous theorem. *)
Section Corollaries.

Variable n : nat.

Hypothesis H2n : 2 * INR n.+2 * eps fs < 1.

Variable A : 'M[FS fs]_n.+1.

Hypothesis SymA : MF2R A^T = MF2R A.

(** The diagonal must be non negative (this is easy to test,
    and otherwise the matrix is definitely not positive definite). *)
Hypothesis Pdiag : forall i : 'I_n.+1, (0 <= A i i)%Re.

Variable maxdiag : R.

Hypothesis Hmaxdiag : forall i : 'I_n.+1, A i i <= maxdiag.

Lemma Pmaxdiag : (0 <= maxdiag)%Re.
Proof. apply (Rle_trans _ _ _ (Pdiag ord0) (Hmaxdiag ord0)). Qed.

Variable c : R.

Hypothesis Hc :
  forall (x : 'cV[R]_n.+1),
  (||x||_2 = 1)%Re -> (Mabs x)^T *m Delta A maxdiag *m Mabs x <=m: c%:M.

Variable At : 'M[FS fs]_n.+1.

Definition At' : 'M[FS fs]_n.+1 :=
  \matrix_(i, j) if (i <= j)%N then At i j else At j i.

Lemma SymAt' : At'^T = At'.
Proof.
rewrite /At' /trmx -matrixP => i j; rewrite !mxE.
case (leqP i j); move=> Hij; case (leqP j i); move=> Hji; [|by[]|by[]|].
{ by suff H : i = j; [rewrite H|apply ord_inj, anti_leq; rewrite Hij Hji]. }
by suff H : (i < i)%N; [move: (ltnn i); rewrite H|move: Hij; apply ltn_trans].
Qed.

(*Hypothesis SymAt : At^T = At.*)

(** *** Corollary 2.4 : criterion for positive definiteness. *)
Section Corollary_2_4.

Hypothesis HAt :
  (forall (i j : 'I_n.+1), ((i < j)%N -> At i j = A i j))
  /\ (forall (i : 'I_n.+1), (At i i <= A i i - c)%Re).

Lemma HAt' :
  (forall (i j : 'I_n.+1), ((i < j)%N -> At' i j = A i j))
  /\ (forall (i : 'I_n.+1), (At' i i <= A i i - c)%Re).
Proof.
by split; [move=> i j Hij|move=> i]; rewrite /At' !mxE;
  [rewrite (ltnW Hij)|rewrite (leqnn i)]; apply HAt.
Qed.

Lemma Delta_pos : 0 <m: Delta A maxdiag.
Proof.
move=> i j; rewrite !mxE; apply Rplus_le_lt_0_compat.
{ apply Rmult_le_pos; [apply Rmult_le_pos; [by apply alpha_pos|]|];
  apply sqrt_pos. }
apply Rmult_lt_0_compat; [rewrite /GRing.mul /=; fs_lra fs|].
apply Rplus_lt_le_0_compat; [|exact Pmaxdiag].
rewrite !S_INR; move: (pos_INR n); lra.
Qed.

Lemma vconst_norm1 : ||\col_(k < n.+1) (/ sqrt (INR n.+1))%Re||_2 = 1.
Proof.
have H : (0 < sqrt (INR n.+1))%Re.
{ apply sqrt_lt_R0; rewrite S_INR; move: (pos_INR n); lra. }
apply (Rmult_eq_reg_l (sqrt (INR n.+1))); [rewrite Rmult_1_r|lra].
rewrite -{3}norm2_const -norm2_scale_pos; [|lra]; apply f_equal.
rewrite -matrixP => i j; rewrite !mxE; apply Rinv_r; lra.
Qed.

Lemma c_pos : 0 <= c.
Proof.
replace 0%Re with ((0 : 'M[R]_1) ord0 ord0); [|by rewrite mxE].
replace c with ((c%:M : 'M[R]_1) ord0 ord0); [|by rewrite mxE].
rewrite -Mle_scalar; move: (Hc vconst_norm1); apply Mle_trans.
{ apply Mmul_le_pos; [apply Mmul_le_pos|by apply Mabs_pos].
  { rewrite -trmx0; apply Mle_tr, Mabs_pos. }
  apply Mlt_le, Delta_pos. }
Qed.

Lemma Delta_At'_le_Delta_A : Delta At' maxdiag <=m: Delta A maxdiag.
Proof.
move=> i j; rewrite !mxE; apply Rplus_le_compat_r.
set (alpha := fun i j => gamma fs (min i j).+2).
set (d := fun (A : 'M[FS fs]_n.+1) (j : 'I_n.+1) =>
            sqrt (/ (1 - alpha j j) * (A j j + 2 * INR j * eta fs))%Re).
have HAtA : forall k : 'I_n.+1, (d At k <= d A k)%Re.
{ move=> k; apply sqrt_le_1_alt, Rmult_le_compat_l.
  { apply Rlt_le, Rinv_0_lt_compat, Rlt_Rminus.
    rewrite /alpha (alpha_gamma (leqnn k)); apply gamma_lt_1.
    by apply (@bg_2_le _ _ n.+2); [rewrite (ltn_add2l 1); apply ltn_ord|]. }
  apply Rplus_le_compat_r, (Rle_trans _ _ _ (proj2 HAt k)); move: c_pos; lra. }
rewrite /GRing.mul /= !(Rmult_assoc (gamma _ _)); apply Rmult_le_compat_l.
{ by apply alpha_pos. }
apply Rmult_le_compat; try apply sqrt_pos; rewrite leqnn; apply HAtA.
Qed.

Lemma cholesky_success_At_At' (Rt : 'M[FS fs]_n.+1) :
  cholesky_success At Rt -> cholesky_success At' Rt.
Proof.
rewrite /cholesky_success => HsAt.
destruct HsAt as (HsAt1, HsAt2); split; [split|by []].
{ by move=> j i Hij; rewrite /At' mxE (ltnW Hij); apply HsAt1. }
move=> j; rewrite /At' !mxE (leqnn j); apply HsAt1.
Qed.

(** Corollary 2.4. *)
Lemma corollary_2_4 (Rt : 'M[FS fs]_n.+1) :
  cholesky_success At Rt -> posdef (MF2R A).
Proof.
move=> HAtRt; apply posdef_norm_eq_1 => x Hx.
have HAt'Rt := cholesky_success_At_At' HAtRt.
have SymAt' := f_equal (@MF2R _ _) SymAt'.
apply (Mle_lt_trans (Mle_sub (Hc Hx))).
apply Mle_lt_trans with (c%:M - (Mabs x)^T *m Delta At' maxdiag *m Mabs x).
{ apply Madd_le_compat_l, Mopp_le_contravar, Mmul_abs_lr, Delta_At'_le_Delta_A. }
apply Mlt_le_trans with (c%:M + x^T *m (MF2R At') *m x).
{ apply Madd_lt_compat_l, (th_2_3 H2n SymAt' HAt'Rt) => [i|].
  { apply (Rle_trans _ _ _ (proj2 HAt' i)); move: c_pos (Hmaxdiag i); lra. }
  by move=> Hx'; rewrite Hx' norm2_0 in Hx; apply R1_neq_R0. }
apply Mle_trans with (c%:M + x^T *m (MF2R A - c *: 1) *m x).
{ apply Madd_le_compat_l; rewrite Mle_scalar !mxE.
  apply big_rec2 => [|j x1 x2 _ Hx12]; [by right|].
  apply Rplus_le_compat => //; rewrite !mxE !big_distrl /=.
  apply big_rec2 => [|i y1 y2 _ Hy12]; [by right|].
  apply Rplus_le_compat => //; rewrite !mxE.
  case (ltnP i j) => Hij; [rewrite (ltnW Hij)|case (ltnP j i) => Hji].
  { rewrite (proj1 HAt _ _ Hij) eqE /= (ltn_eqF Hij).
    by rewrite GRing.mulr0 GRing.subr0; right. }
  { rewrite (proj1 HAt _ _ Hji).
    replace (FS_val (A j i)) with ((MF2R A) j i); [|by rewrite mxE].
    rewrite -{1}SymA !mxE eqE /= eq_sym (ltn_eqF Hji).
    by rewrite GRing.mulr0 GRing.subr0; right. }
  have H : i = j; [by apply ord_inj, anti_leq; apply /andP|]; rewrite H.
  rewrite eq_refl /GRing.mul /= Rmult_1_r !(Rmult_comm _ (x j _)) -!Rmult_assoc.
  apply Rmult_le_compat_l; [apply sqr_ge_0|apply HAt]. }
rewrite mulmxDr mulmxDl mulmxN mulNmx -scalemxAr scalemxAl mulmx1 -scalemxAl.
apply Mle_scalar; right.
have H : (x^T *m x) ord0 ord0 = 1.
{ by rewrite -/(dotprod x x) -norm2_sqr_dotprod Hx /= !Rmult_1_r. }
rewrite 6!mxE H GRing.mulr1 /GRing.natmul /GRing.add /GRing.opp /=; ring.
Qed.

End Corollary_2_4.

(** *** Corollary 2.7 : interval matrices. *)
Section Corollary_2_7.

Variable Rad : 'M[FS fs]_n.+1.

Hypothesis PRad : 0 <=m: MF2R Rad.

Variable r : R.

Hypothesis Hr :
  forall (x : 'cV[R]_n.+1),
  (||x||_2 = 1)%Re -> (Mabs x)^T *m MF2R Rad *m Mabs x <=m: r%:M.

Hypothesis HAt :
  (forall (i j : 'I_n.+1), ((i < j)%N -> At i j = A i j))
  /\ (forall (i : 'I_n.+1), (At i i <= A i i - c - r)%Re).

Lemma HAt'' :
  (forall (i j : 'I_n.+1), ((i < j)%N -> At' i j = A i j))
  /\ (forall (i : 'I_n.+1), (At' i i <= A i i - c - r)%Re).
Proof.
by split; [move=> i j Hij|move=> i]; rewrite /At' !mxE;
  [rewrite (ltnW Hij)|rewrite (leqnn i)]; apply HAt.
Qed.

Lemma r_pos : 0 <= r.
Proof.
replace 0%Re with ((0 : 'M[R]_1) ord0 ord0); [|by rewrite mxE].
replace r with ((r%:M : 'M[R]_1) ord0 ord0); [|by rewrite mxE].
rewrite -Mle_scalar; move: (Hr vconst_norm1); apply Mle_trans.
{ apply Mmul_le_pos; [apply Mmul_le_pos|by apply Mabs_pos].
  { rewrite -trmx0; apply Mle_tr, Mabs_pos. }
  apply PRad. }
Qed.

(** Corollary 2.7. *)
Lemma corollary_2_7 (Rt : 'M[FS fs]_n.+1) : cholesky_success At Rt ->
  forall Xt : 'M[R]_n.+1, Mabs (Xt - MF2R A) <=m: MF2R Rad -> posdef Xt.
Proof.
move=> HAtRt Xt HXtAR; apply posdef_norm_eq_1 => x Hx.
have HAt'Rt := cholesky_success_At_At' HAtRt.
have SymAt' := f_equal (@MF2R _ _) SymAt'.
apply Mle_lt_trans with (c%:M + r%:M
                         - ((Mabs x)^T *m Delta A maxdiag *m Mabs x
                            + (Mabs x)^T *m MF2R Rad *m Mabs x)).
{ by apply Mle_sub, Madd_le_compat; [apply Hc|apply Hr]. }
apply Mle_lt_trans with (c%:M + r%:M
                         - ((Mabs x)^T *m Delta At' maxdiag *m Mabs x
                            + (Mabs x)^T *m MF2R Rad *m Mabs x)).
{ apply Madd_le_compat_l, Mopp_le_contravar, Madd_le_compat_r, Mmul_abs_lr.
  apply Delta_At'_le_Delta_A; split; [by apply (proj1 HAt)|]; move=> i.
  apply (Rle_trans _ _ _ (proj2 HAt i)); move: r_pos; lra. }
apply Mlt_le_trans with (c%:M + r%:M + (x^T *m (MF2R At') *m x
                                        + x^T *m (Xt - MF2R A) *m x)).
{ apply Madd_lt_compat_l; rewrite GRing.opprD; apply Madd_lt_le_compat.
  { apply (th_2_3 H2n SymAt' HAt'Rt) => [i|].
    { apply (Rle_trans _ _ _ (proj2 HAt'' i)).
      move: c_pos r_pos (Hmaxdiag i); lra. }
    by move=> Hx'; rewrite Hx' norm2_0 in Hx; apply R1_neq_R0. }
  rewrite -(GRing.opprK (_ *m x)); apply Mopp_le_contravar.
  apply (Mle_trans (Mle_abs _)); rewrite Mabs_opp map_trmx.
  apply (Mle_trans (Mabs_mul _ _)), Mmul_le_compat_r; [by apply Mabs_pos|].
  by apply (Mle_trans (Mabs_mul _ _)), Mmul_le_compat_l; [apply Mabs_pos|]. }
apply Mle_trans with (c%:M + r%:M + x^T *m (MF2R A - (c + r) *: 1) *m x
                      + x^T *m (Xt - MF2R A) *m x).
{ rewrite GRing.addrA; apply Madd_le_compat_r.
  apply Madd_le_compat_l; rewrite Mle_scalar !mxE.
  apply big_rec2 => [|j x1 x2 _ Hx12]; [by right|].
  apply Rplus_le_compat => //; rewrite !mxE !big_distrl /=.
  apply big_rec2 => [|i y1 y2 _ Hy12]; [by right|].
  apply Rplus_le_compat => //; rewrite !mxE.
  case (ltnP i j) => Hij; [rewrite (ltnW Hij)|case (ltnP j i) => Hji].
  { rewrite (proj1 HAt _ _ Hij) eqE /= (ltn_eqF Hij).
    by rewrite GRing.mulr0 GRing.subr0; right. }
  { rewrite (proj1 HAt _ _ Hji).
    replace (FS_val (A j i)) with ((MF2R A) j i); [|by rewrite mxE].
    rewrite -{1}SymA !mxE eqE /= eq_sym (ltn_eqF Hji).
    by rewrite GRing.mulr0 GRing.subr0; right. }
  have H : i = j; [by apply ord_inj, anti_leq; apply /andP|]; rewrite H.
  rewrite eq_refl /GRing.mul /= Rmult_1_r !(Rmult_comm _ (x j _)) -!Rmult_assoc.
  apply Rmult_le_compat_l; [by apply sqr_ge_0|].
  rewrite GRing.opprD GRing.addrA; apply HAt. }
rewrite !mulmxDr !mulmxDl !mulmxN !mulNmx -scalemxAr scalemxAl mulmx1 -scalemxAl.
apply Mle_scalar; right.
have H : (x^T *m x) ord0 ord0 = 1.
{ by rewrite -/(dotprod x x) -norm2_sqr_dotprod Hx /= !Rmult_1_r. }
rewrite 9!mxE H GRing.mulr1 !mxE /GRing.natmul /GRing.add /GRing.opp /=; ring.
Qed.

End Corollary_2_7.

End Corollaries.

(** *** A (practically computable) upper bound on the constant c.

    (bound I) *)
Section C_upper_bound.

Variable n : nat.

Variable H4n : 4 * INR n.+2 * eps fs < 1.

Lemma H2n : 2 * INR n.+2 * eps fs < 1.
Proof. move: H4n (neps_pos fs n.+2); rewrite !Rmult_assoc; lra. Qed.

Variable A : 'M[FS fs]_n.+1.

Hypothesis Pdiag : forall i : 'I_n.+1, (0 <= A i i)%Re.

Variable maxdiag : R.

Hypothesis Hmaxdiag : forall i : 'I_n.+1, A i i <= maxdiag.

Let alpha i j := gamma fs (min i j).+2.

Let d (A : 'M[FS fs]_n.+1) (j : 'I_n.+1) :=
  sqrt (/ (1 - alpha j j) * (A j j + 2 * INR j * eta fs))%Re.

Let dv : 'cV_n.+1 := \col_i (d A i).

(* begin hide *)
Lemma decompose_Delta :
  Delta A maxdiag <=m: gamma fs n.+2 *: (dv *m dv^T)
                       + (4 * eta fs * (INR n.+2 + maxdiag))
                         *: ((\col__ 1) *m (\col__ 1)^T).
Proof.
rewrite /Delta /Mle => i j; rewrite !mxE !big_ord_recl !big_ord0 !mxE.
apply Rplus_le_compat.
{ rewrite GRing.addr0 /GRing.mul /= Rmult_assoc; apply Rmult_le_compat_r.
  { apply Rmult_le_pos; apply sqrt_pos. }
  rewrite /alpha; apply Min.min_case; by apply gamma_monotone;
    [rewrite (leq_add2l 1); apply ltn_ord|apply bg_2, H2n]. }
by right; rewrite GRing.addr0 !GRing.mulr1.
Qed.

Lemma c_upper_bound_aux1 (x : 'cV_n.+1) : (||x||_2 = 1)%Re ->
  (Mabs x)^T *m Delta A maxdiag *m (Mabs x)
  <=m: gamma fs n.+2 *: (||dv||_2^2)%:M
       + (4 * eta fs * (INR n.+2 + maxdiag))%Re
           *: (||\col_(k < n.+1) 1||_2^2)%:M.
Proof.
move=> Hx; apply (Mle_trans (Mmul_abs_lr _ (Mle_abs _))).
set (eta_eps := (4 * eta fs * (INR n.+2 + maxdiag))%Re).
set (ub := (gamma fs n.+2 *: (dv *m dv^T)
            + eta_eps *: ((\col__ 1) *m (\col__ 1)^T))).
apply Mle_trans with ((Mabs x)^T *m ub *m Mabs x).
{ rewrite (Mabs_right (Mlt_le (Delta_pos H2n _ _))) //.
  apply Mmul_abs_lr, decompose_Delta. }
rewrite mulmxDr mulmxDl -!scalemxAr -!scalemxAl.
rewrite !mulmxA -(mulmxA _ dv^T) -(mulmxA _ (\col__ 1)^T).
rewrite -{1}(trmxK dv) -{1}(trmxK (\col__ 1)) -!trmx_mul.
have Peta_eps : (0 <= eta_eps)%Re.
{ apply Rmult_le_pos; [fs_lra fs|].
  move: (pos_INR n.+2) (Pmaxdiag Pdiag Hmaxdiag); lra. }
have H : forall y : 'cV_n.+1, (y^T *m Mabs x)^T *m (y^T *m Mabs x)
                              <=m: (||y||_2^2)%:M => [y|].
{ rewrite Mmul_scalar trmx_scalar Mle_scalar_mx /GRing.mul /= Rmult_1_r.
  apply Rsqr_le_abs_1; rewrite (Rabs_pos_eq (norm2 _)); [|by apply norm2_pos].
  rewrite -(Rmult_1_r (norm2 _)) -Hx -(norm2_mabs x).
  apply cauchy_schwarz_Rabs. }
apply Madd_le_compat.
{ by apply Mscale_le_compat; [apply gamma_pos, bg_2, H2n|apply H]. }
by apply Mscale_le_compat; [|apply H].
Qed.

Lemma c_upper_bound_aux2 (x : 'cV_n.+1) : (||x||_2 = 1)%Re ->
  gamma fs n.+2 *: ((||dv||_2^2)%:M : 'M_1)
  + (4 * eta fs * (INR n.+2 + maxdiag))%Re
    *: (||\col_(k < n.+1) 1||_2^2)%:M
  <=m: ((gamma fs n.+2 / (1 - gamma fs n.+2) * (\tr (MF2R A)
                                                + 2 * (INR n.+1)^2 * eta fs)
         + 4 * eta fs * INR n.+1 * (INR n.+2 + maxdiag))%Re)%:M.
Proof.
move=> Hx.
rewrite (Rmult_assoc _ (INR n.+1)) (Rmult_comm (INR n.+1)) -Rmult_assoc.
set (eta_eps := (4 * eta fs * (INR n.+2 + maxdiag))%Re).
set (In1 := INR n.+1); set (In2 := INR n.+2).
apply Mle_scalar.
rewrite norm2_sqr_dotprod dotprod_sum !mxE eqE /= /GRing.natmul /= Rmult_1_r.
apply Rplus_le_compat; [|right; apply Rmult_eq_compat_l].
{ rewrite /GRing.mul /GRing.add /Rdiv /= Rmult_assoc Rmult_1_r.
  apply Rmult_le_compat_l; [by apply gamma_pos, bg_2, H2n|].
  replace (_ * eta _)%Re
  with (INR n.+1 * (2 * In1 * eta fs))%Re; [|by rewrite /In1; ring].
  rewrite -big_sum_const -big_split big_distrr /=.
  apply big_rec2 => [|i x1 x2 _ Hx12]; [by right|].
  have H1 : (0 <= / (1 - alpha i i))%Re.
  { apply Rlt_le, Rinv_0_lt_compat, Rlt_Rminus.
    rewrite /alpha alpha_gamma; [|by apply leqnn]; apply gamma_lt_1.
    apply (@bg_2_le _ _ n.+2); [|by apply H2n].
    rewrite (ltn_add2l 1); apply ltn_ord. }
  have H2 : (0 <= A i i + 2 * INR i * eta fs)%Re.
  { move: (Rmult_le_pos _ _ (pos_INR i) (Rlt_le _ _ (eta_pos fs))) (Pdiag i).
    rewrite Rmult_assoc; lra. }
  apply Rplus_le_compat; [|by []].
  rewrite /dv !mxE /In1 /d sqrt_def; [|by apply Rmult_le_pos].
  apply Rmult_le_compat => //.
  { apply Rinv_le; [by apply Rlt_Rminus, gamma_lt_1, H2n|].
    apply Rminus_le; ring_simplify; rewrite Rplus_comm; apply Rle_minus.
    by rewrite /alpha (alpha_gamma (leqnn i)); apply gamma_monotone;
      [rewrite (ltn_add2l 1); apply ltn_ord|apply bg_2, H2n]. }
  apply Rplus_le_compat_l, Rmult_le_compat_r; [fs_lra fs|].
  apply Rmult_le_compat_l; [lra|apply /le_INR /leP /ltnW /ltn_ord]. }
by rewrite /In1 norm2_const sqrt_def; [|by apply pos_INR].
Qed.

Lemma c_upper_bound_aux3 (x : 'cV_n.+1) : (||x||_2 = 1)%Re ->
  (Mabs x)^T *m Delta A maxdiag *m (Mabs x)
  <=m: ((/2 * gamma fs (2 * n.+2) * (\tr (MF2R A) + 2 * (INR n.+1)^2 * eta fs)
         + 4 * eta fs * INR n.+1 * (INR n.+2 + maxdiag))%Re)%:M.
Proof.
move=> Hx; rewrite -(gamma_d_1mgamma H2n).
apply (Mle_trans (c_upper_bound_aux1 Hx) (c_upper_bound_aux2 Hx)).
Qed.
(* end hide *)

Lemma c_upper_bound (x : 'cV_n.+1) : (||x||_2 = 1)%Re ->
  (Mabs x)^T *m Delta A maxdiag *m (Mabs x)
  <=m: ((/2 * gamma fs (2 * n.+2) * (\tr (MF2R A))
         + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag))%Re)%:M.
Proof.
move=> Hx; apply (Mle_trans (c_upper_bound_aux3 Hx)); rewrite Mle_scalar_mx.
rewrite Rmult_plus_distr_l Rplus_assoc; apply Rplus_le_compat_l.
apply (Rplus_le_reg_r (- 4 * eta fs * INR n.+1 * (INR n.+2 + maxdiag))%Re);
  ring_simplify; rewrite Rinv_r; [rewrite Rmult_1_l|lra].
apply Rle_trans with (INR n.+1 ^ 2 * eta fs)%Re.
{ apply Rmult_le_compat_r; [fs_lra fs|]; rewrite -{2}(Rmult_1_l (_ ^ 2)).
  apply Rmult_le_compat_r; [by apply pow2_ge_0|].
  by apply Rlt_le, gamma_lt_1; rewrite mult_INR -Rmult_assoc. }
rewrite (S_INR n.+1); apply Rminus_le; ring_simplify; apply Rle_minus.
apply Rmult_le_compat_r; [fs_lra fs|].
rewrite /= Rmult_1_r -/(INR n.+1) -Rmult_assoc.
apply Rmult_le_compat_r; move: (pos_INR n.+1); lra.
Qed.

End C_upper_bound.

(** *** A (very rough but easy to compute) upper bound on the constant r. *)
Lemma r_upper_bound n (Rad : 'M[FS fs]_n.+1) (PRad : 0 <=m: MF2R Rad)
      r (Hr : forall i j, Rad i j <= r) (x : 'cV_n.+1) : (||x||_2 = 1)%Re ->
  (Mabs x)^T *m MF2R Rad *m (Mabs x) <=m: ((INR n.+1 * r)%Re)%:M.
Proof.
move=> Hx; apply Mle_trans with ((Mabs x)^T *m const_mx r *m (Mabs x)).
{ apply Mmul_abs_lr => i j; rewrite !mxE; apply Hr. }
have Pr : (0 <= r)%Re.
{ move: (Hr ord0 ord0); apply Rle_trans.
  by move: (PRad ord0 ord0); rewrite !mxE. }
have Hcr : @const_mx _ n.+1 n.+1 r = (\col__ sqrt r) *m (\col__ sqrt r)^T.
{ rewrite -matrixP; move=> i j; rewrite !mxE big_ord_recl big_ord0 GRing.addr0.
  by rewrite !mxE /GRing.mul /= sqrt_def. }
rewrite Hcr mulmxA -mulmxA -{1}(trmxK (\col__ _)) -trmx_mul.
apply Mle_trans with (||\col_(_ < n.+1) sqrt r||_2^2)%:M.
{ rewrite Mmul_scalar trmx_scalar Mle_scalar_mx /GRing.mul /= Rmult_1_r.
  apply Rsqr_le_abs_1; rewrite (Rabs_pos_eq (norm2 _)); [|by apply norm2_pos].
  rewrite -(Rmult_1_r (norm2 _)) -Hx -(norm2_mabs x).
  apply cauchy_schwarz_Rabs. }
apply Mle_scalar_mx; right; rewrite /= Rmult_1_r -/(INR n.+1) -/(Rsqr _).
rewrite -(sqrt_def _ (pos_INR _)) -{2}(sqrt_def _ Pr).
rewrite Rmult_assoc Rmult_comm -Rmult_assoc Rmult_assoc (Rmult_comm (sqrt _)).
rewrite -norm2_const -(norm2_scale_pos _ (sqrt_pos _)) -/(Rsqr _).
by do 2 f_equal; rewrite -matrixP => i j; rewrite !mxE GRing.mulr1.
Qed.

Lemma corollary_2_4_with_c_upper_bound n (H4n : 4 * INR n.+2 * eps fs < 1) :
  forall A : 'M[FS fs]_n.+1, MF2R A^T = MF2R A ->
  (forall i : 'I_n.+1, 0 <= A i i) ->
  forall maxdiag : R, (forall i : 'I_n.+1, A i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R A))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FS fs]_n.+1,
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, At i i <= A i i - c)) ->
  forall Rt : 'M[FS fs]_n.+1, cholesky_success At Rt ->
  posdef (MF2R A).
Proof.
move=> A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt Rt HARt.
have Pmaxdiag := Rle_trans _ _ _ (Pdiag ord0) (Hmaxdiag ord0).
have Hc' : forall x : 'cV_n.+1, ||x||_2 = 1 ->
           (Mabs x)^T *m Delta A maxdiag *m Mabs x <=m: c%:M.
{ move=> x Hx; apply (Mle_trans (c_upper_bound H4n Pdiag Hmaxdiag Hx)).
  by rewrite Mle_scalar_mx. }
apply (corollary_2_4 (H2n H4n) SymA Pdiag Hmaxdiag Hc' HAt HARt).
Qed.

Lemma corollary_2_7_with_c_r_upper_bounds n (H4n : 4 * INR n.+2 * eps fs < 1) :
  forall A : 'M[FS fs]_n.+1, MF2R A^T = MF2R A ->
  (forall i : 'I_n.+1, 0 <= A i i) ->
  forall Rad : 'M_n.+1, 0 <=m: MF2R Rad ->
  forall maxdiag : R, (forall i : 'I_n.+1, A i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R A))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall r : R, (forall (i j : 'I_n.+1), (Rad i j <= r)%Re) ->
  forall At : 'M[FS fs]_n.+1,
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, (At i i <= A i i - c - INR n.+1 * r)%Re)) ->
  forall Rt : 'M[FS fs]_n.+1, cholesky_success At Rt ->
  forall Xt : 'M_n.+1, Mabs (Xt - MF2R A) <=m: MF2R Rad -> posdef Xt.
Proof.
move=> A SymA Pdiag Rad PRad maxdiag Hmaxdiag c Hc r Hr At HAt
         Rt HARt Xt HXtARad.
have Pmaxdiag := Rle_trans _ _ _ (Pdiag ord0) (Hmaxdiag ord0).
have Hc' : forall x : 'cV_n.+1, ||x||_2 = 1 ->
           (Mabs x)^T *m Delta A maxdiag *m Mabs x <=m: c%:M.
{ move=> x Hx; apply (Mle_trans (c_upper_bound H4n Pdiag Hmaxdiag Hx)).
  by rewrite Mle_scalar_mx. }
apply (corollary_2_7 (H2n H4n) SymA Pdiag Hmaxdiag Hc' PRad
                     (r_upper_bound PRad Hr) HAt HARt HXtARad).
Qed.

End Cholesky.

Require Import binary64.

(** The result is valid for any tie-break rule. *)
Parameter choice : Z -> bool.

Definition corollary_2_4_with_c_upper_bound64 :=
  @corollary_2_4_with_c_upper_bound (binary64 choice).

Definition corollary_2_7_with_c_r_upper_bounds64 :=
  @corollary_2_7_with_c_r_upper_bounds (binary64 choice).
