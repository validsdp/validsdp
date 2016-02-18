(** * Various lemmas on the gamma n ($\gamma_n = \frac{n\epsilon}{1-n\epsilon}$#gamma n = n eps / (1 - n eps)#)

    These terms are tremendously useful for accumulating error bounds. *)

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

Import GRing.Theory.

Require Export float_spec.

(** ** Basic lemmas about the bound ([n eps < 1]) on n, used everywhere. *)
Section bounds.

Variable fs : Float_spec.

Lemma bg_eq n m : n = m -> INR n * eps fs < 1 -> INR m * eps fs < 1.
Proof. by move=> ->. Qed.

Lemma bg_2_eq n m : n = m -> 2 * INR n * eps fs < 1 -> 2 * INR m * eps fs < 1.
Proof. by move=> ->. Qed.

Lemma bg_le n m : (n <= m)%N -> INR m * eps fs < 1 -> INR n * eps fs < 1.
Proof.
move=> Hnm; apply Rle_lt_trans.
by apply Rmult_le_compat_r; [apply eps_pos|apply /le_INR /leP].
Qed.

Lemma bg_2_le n m :
  (n <= m)%N -> 2 * INR m * eps fs < 1 -> 2 * INR n * eps fs < 1.
Proof.
move=> Hnm; apply Rle_lt_trans.
apply Rmult_le_compat_r; [apply eps_pos|]; apply Rmult_le_compat_l; [lra|].
by apply /le_INR /leP.
Qed.

Lemma neps_pos n : 0 <= INR n * eps fs.
Proof. apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. Qed.

Lemma bg_2 n : 2 * INR n * eps fs < 1 -> INR n * eps fs < 1.
Proof. move: (pos_INR n) (eps_pos fs); lra. Qed.

Lemma bg_S n : INR n.+1 * eps fs < 1 -> INR n * eps fs < 1.
Proof. apply bg_le, leqnSn. Qed.

Lemma bg_2S n : 2 * INR n.+1 * eps fs < 1 -> 2 * INR n * eps fs < 1.
Proof. rewrite S_INR; have Pe := (eps_pos fs); lra. Qed.
  
Lemma bg_2S2 n : 2 * INR n.+1 * eps fs < 1 -> INR n.+2 * eps fs < 1.
Proof.
apply Rle_lt_trans.
rewrite !S_INR; ring_simplify; apply Rplus_le_compat_r.
rewrite Rmult_assoc; move: (neps_pos n); lra.
Qed.

Lemma bg_2pred n : 2 * INR n * eps fs < 1 -> 2 * INR n.-1 * eps fs < 1.
Proof.
apply Rle_lt_trans, Rmult_le_compat_r; [by apply eps_pos|];
apply Rmult_le_compat_l; [lra|apply le_INR, le_pred_n].
Qed.

End bounds.

(** ** Definition of the term [gamma n] and very basic properties. *)
Section Gamma.

Variable fs : Float_spec.

Definition gamma n := INR n * eps fs / (1 - INR n * eps fs).

Lemma gamma_pos n : INR n * eps fs < 1 -> 0 <= gamma n.
Proof.
move=> Hn.
apply (Rmult_le_reg_r (1 - INR n * eps fs)); [lra|].
rewrite Rmult_0_l /gamma Rmult_assoc Rinv_l; [|lra].
rewrite Rmult_1_r; apply neps_pos.
Qed.

Lemma gamma_lt_1 n : 2 * INR n * eps fs < 1 -> gamma n < 1.
Proof.
move=> Hn.
apply (Rmult_lt_reg_r (1 - INR n * eps fs)); [lra|].
rewrite /gamma Rmult_assoc Rinv_l; lra.
Qed.

Lemma gamma1_ge_eps : eps fs <= gamma 1.
Proof.
rewrite /gamma /= Rmult_1_l.
have H := eps_lt_1 fs.
apply (Rmult_le_reg_r (1 - eps fs)); [lra|].
rewrite Rmult_assoc Rinv_l; [|lra].
apply Rmult_le_compat_l; move: (eps_pos fs); lra.
Qed.

Lemma gamma_monotone n m :
  (n <= m)%N -> INR m * eps fs < 1 -> gamma n <= gamma m.
Proof.
move=> Hnm Hm.
have Hn := bg_le Hnm Hm.
have Hnmeps : (INR n * eps fs <= INR m * eps fs).
{ apply Rmult_le_compat_r; [by apply eps_pos|].
  by apply /le_INR /leP. }
rewrite /gamma; apply Rmult_le_compat.
{ apply neps_pos. }
{ apply Rlt_le, Rinv_0_lt_compat; lra. }
{ exact Hnmeps. }
apply Rinv_le; lra.
Qed.

(** A few, sometime useful, simple equalities. *)
Lemma gammap1 n : INR n * eps fs < 1 -> 1 + gamma n = / (1 - INR n * eps fs).
Proof. by move=> Hn; rewrite /gamma; field_simplify; try lra. Qed.

Lemma gamma_d_1mgamma n :
  2 * INR n * eps fs < 1 -> gamma n / (1 - gamma n) = /2 * gamma (2 * n).
Proof. move=> Hn; rewrite /gamma mult_INR /=; field; lra. Qed.

End Gamma.

(** ** Type of values bounded by [gamma n]. *)
Section Bounded.

Variable fs : Float_spec.

Definition b_gamma n := bounded (gamma fs n).

Definition b_gamma_0 n (Hn : INR n * eps fs < 1) : b_gamma n :=
  bounded_0 (gamma_pos Hn).

Definition widen_b_gamma n m (Hnm : (n <= m)%N) (Hm : INR m * eps fs < 1)
  (b : b_gamma n) : b_gamma m :=
  widen_bounded (gamma_monotone Hnm Hm) b.

Definition cast_b_gamma n m (Hnm : n = m) (b : b_gamma n) : b_gamma m :=
  cast_bounded (f_equal _ Hnm) b.

Lemma b_gammap1_le_2_Rabs n (Hn : 2 * INR n * eps fs < 1) (b : b_gamma n) :
  Rabs (1 + b) <= Rabs 2.
Proof.
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
rewrite Rabs_R1 (Rabs_right 2); [|lra]; apply Rplus_le_compat_l.
by apply Rle_trans with (gamma fs n); [case b|apply Rlt_le, gamma_lt_1].
Qed.
  
End Bounded.

(** Tactics to destruct bounded values before calling lra. *)
Ltac bounded_lra_with fs b :=
  move: (Rabs_le_inv _ _ (bounded_prop b)) (eps_lt_1 fs); lra.

Ltac bounded_lra fs :=
  match goal with
    | d : b_eps _ |- _ => bounded_lra_with fs d
    | e : b_eta _ |- _ => bounded_lra_with fs e
    | g : b_gamma _ _ |- _ => bounded_lra_with fs g
  end.

Ltac fs_lra fs := move: (eps_pos fs) (eta_pos fs); lra.

(** ** Main properties about [gamma]. *)
Section Gamma_props.

Variable fs : Float_spec.

(** *** Product and sum of [gamma]. *)

Lemma gamma_mult n m : (n <= m)%N -> 2 * INR m * eps fs < 1 ->
  gamma fs n * gamma fs m <= gamma fs n.
Proof.
move=> Hnm H2m.
have Hn := bg_2 (bg_2_le Hnm H2m).
rewrite -{2}(Rmult_1_r (gamma _ _)).
by apply Rmult_le_compat_l; [apply gamma_pos|apply Rlt_le, gamma_lt_1].
Qed.

Lemma gamma_mult_nat k n : INR (k * n) * eps fs < 1 ->
  INR k * gamma fs n <= gamma fs (k * n).
Proof.
move: k n; case=> [|k] n Hkn.
{ by rewrite Rmult_0_l; apply gamma_pos. }
rewrite /gamma -!Rmult_assoc -mult_INR.
apply Rmult_le_compat_l; [by apply neps_pos|].
suff Hn : (INR n * eps fs <= INR (k.+1 * n) * eps fs) by apply Rinv_le; lra.
apply Rmult_le_compat_r; [by apply eps_pos|].
rewrite mulSn plus_INR; move: (pos_INR (k * n)); lra.
Qed.

Lemma gamma_plus_mult_le n m : (m <= n)%N -> INR (n + m) * eps fs < 1 ->
  gamma fs n + gamma fs m + gamma fs (n + m) * gamma fs m <= gamma fs (n + m).
Proof.
move=> Hmlen Hnm.
have Hn := bg_le (leq_addr m n) Hnm.
have Hm := bg_le (leq_addl n m) Hnm.
apply (Rmult_le_reg_r (1 - INR n * eps fs)); [lra|].
apply (Rmult_le_reg_r (1 - INR m * eps fs)); [lra|].
apply (Rmult_le_reg_r (1 - INR (n + m) * eps fs)); [lra|].
rewrite /gamma; field_simplify; [|lra|lra]; rewrite /Rdiv Rinv_1 !Rmult_1_r.
apply (Rplus_le_reg_r
         (- INR n * eps fs ^ 3 * INR m * INR (n + m)
          + (INR n ^ 2 + INR m ^ 2) * eps fs ^ 2
          + 3 * INR n * eps fs ^ 2 * INR m
          - eps fs * INR m - eps fs * INR n)).
rewrite plus_INR; ring_simplify.
replace (_ * _) with (INR m * eps fs ^ 2 * INR m) by ring.
apply Rmult_le_compat_r; [by apply pos_INR|].
apply Rmult_le_compat_r; [by apply pow2_ge_0|].
by apply /le_INR /leP.
Qed.
  
Lemma gamma_plus_mult n m : INR (n + m) * eps fs < 1 ->
  gamma fs n + gamma fs m + gamma fs n * gamma fs m <= gamma fs (n + m).
Proof.
move=> Hnm.
have Hn := bg_le (leq_addr m n) Hnm.
have Hm := bg_le (leq_addl n m) Hnm.
case (Bool.orb_prop _ _ (leq_total n m)) => [Hnlem|Hmlen].
{ rewrite addnC in Hnm |- *.
  apply Rle_trans with (gamma fs m + gamma fs n + gamma fs (m + n) * gamma fs n);
    [|by apply gamma_plus_mult_le].
  rewrite (Rplus_comm (gamma _ _)); apply Rplus_le_compat_l.
  rewrite Rmult_comm; apply Rmult_le_compat_r; [by apply gamma_pos|].
  by apply gamma_monotone; [apply leq_addr|]. }
apply Rle_trans with (gamma fs n + gamma fs m + gamma fs (n + m) * gamma fs m);
  [|by apply gamma_plus_mult_le].
apply Rplus_le_compat_l, Rmult_le_compat_r; [by apply gamma_pos|].
by apply gamma_monotone; [apply leq_addr|].
Qed.

Lemma gamma_plus n m : INR (n + m) * eps fs < 1 ->
  gamma fs n + gamma fs m <= gamma fs (n + m).
Proof.
move=> Hnm.
have Hn := bg_le (leq_addr m n) Hnm.
have Hm := bg_le (leq_addl n m) Hnm.
apply Rle_trans with (gamma fs n + gamma fs m + gamma fs n * gamma fs m);
  [|by apply gamma_plus_mult].
rewrite -{1}(Rplus_0_r (_ + _)); apply Rplus_le_compat_l.
by apply Rmult_le_pos; apply gamma_pos.
Qed.

Lemma gamma_plus_eps n : INR n.+1 * eps fs < 1 ->
  gamma fs n + eps fs <= gamma fs n.+1.
Proof.
move=> Hnp1.
apply Rle_trans with (gamma fs 1 + gamma fs n); [|by apply gamma_plus].
rewrite Rplus_comm; apply Rplus_le_compat_r, gamma1_ge_eps.
Qed.

(** *** Product and quotient of terms [(1 + t)] with [|t| <= gamma]. *)

(** Things are nice for the product... *)
Lemma gammap1_mult n m : 2 * INR (n + m) * eps fs < 1 ->
  forall (t : b_gamma fs n) (t' : b_gamma fs m),
  exists t'' : b_gamma fs (n + m), (1 + t) * (1 + t') = 1 + t''.
Proof.
move=> H2nm t t'.
have Hnm := bg_2 H2nm.
suff H : (Rabs ((1 + t) * (1 + t') - 1) <= gamma fs (n + m)).
{ exists (Build_bounded H); simpl; ring. }
apply Rle_trans with (gamma fs n + gamma fs m + gamma fs n * gamma fs m);
  [|by apply gamma_plus_mult].
replace (_ - 1) with (t + t' + t * t') by ring.
apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat.
{ by apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat;
    [case t|case t']. }
by rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos;
  [case t| case t'].
Qed.

Lemma gammap1_mult_epsp1 n : 2 * (INR n.+1) * eps fs < 1 ->
  forall (t : b_gamma fs n) (d : b_eps fs),
  exists t' : b_gamma fs n.+1, (1 + t) * (1 + d) = 1 + t'.
Proof.
move=> H2n t d.
have [t'' Ht''] := @gammap1_mult 1 n H2n (widen_bounded (gamma1_ge_eps fs) d) t.
by exists t''; rewrite Rmult_comm.
Qed.

(** ...but a bit trickier for the quotient. The following is false for m > n.
    For instance (with n = 0):
    1 / (1 - gamma m) = (1 - m eps) / (1 - 2 m eps)
    = 1 + (m eps) / (1 - 2 m eps)
    > 1 + (m eps) / (1 - m eps) = 1 + gamma m *)
Lemma gammap1_div_le n m : (m <= n)%N -> 2 * INR (n + m) * eps fs < 1 ->
  forall (t : b_gamma fs n) (t' : b_gamma fs m),
  exists t'' : b_gamma fs (n + m), (1 + t) / (1 + t') = 1 + t''.
Proof.
move=> Hmlen H2nm t t'.
have Hnm := bg_2 H2nm.
have H2m := bg_2_le (leq_addl n m) H2nm.
have Glt1 := gamma_lt_1 H2m.
suff H : (Rabs ((1 + t) / (1 + t') - 1) <= gamma fs (n + m)).
{ exists (Build_bounded H); simpl; ring. }
have Nz1t' : 1 + t' <> 0 by bounded_lra fs.
replace (_ - 1) with ((t - t') / (1 + t')); [|by field].
rewrite Rabs_mult Rabs_Rinv; [|by []].
apply (Rmult_le_reg_r (Rabs (1 + t'))); [by apply Rabs_pos_lt|].
rewrite Rmult_assoc Rinv_l; [|by apply Rabs_no_R0]; rewrite Rmult_1_r.
apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_Ropp.
apply Rle_trans with (gamma fs n + gamma fs m).
{ by apply Rplus_le_compat; [case t|case t']. }
apply Rle_trans with (gamma fs (n + m) * (1 - gamma fs m)).
{ apply (Rplus_le_reg_r (gamma fs (n + m) * gamma fs m)).
  apply (Rle_trans _ _ _ (gamma_plus_mult_le Hmlen Hnm)); right; ring. }
apply Rmult_le_compat_l; [by apply gamma_pos|].
apply Rabs_ge; right; bounded_lra fs.
Qed.

(** There is a factor 2 on m in the general case. *)
Lemma gammap1_div n m : 2 * INR (n + 2 * m) * eps fs < 1 ->
  forall (t : b_gamma fs n) (t' : b_gamma fs m),
  exists t'' : b_gamma fs (n + 2 * m), (1 + t) / (1 + t') = 1 + t''.
Proof.
move=> H2nm2 t t'.
have Hnm2 := bg_2 H2nm2.
have Hm2 := bg_2 (bg_2_le (leq_addl n (2 * m)) H2nm2).
have H2m : 2 * INR m * eps fs < 1 by change 2 with (INR 2); rewrite -mult_INR.
have Glt1 := gamma_lt_1 H2m.
suff H : Rabs ((1 + t) / (1 + t') - 1) <= gamma fs (n + 2 * m).
{ exists (Build_bounded H); simpl; ring. }
have Nz1t' : 1 + t' <> 0 by bounded_lra fs.
replace (_ - 1) with ((t - t') / (1 + t')); [|by field].
rewrite Rabs_mult Rabs_Rinv; [|by []].
apply (Rmult_le_reg_r (Rabs (1 + t'))); [by apply Rabs_pos_lt|].
rewrite Rmult_assoc Rinv_l; [|by apply Rabs_no_R0]; rewrite Rmult_1_r.
apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_Ropp.
apply Rle_trans with (gamma fs n + gamma fs m).
{ by apply Rplus_le_compat; [case t|case t']. }
apply Rle_trans with (gamma fs (n + 2 * m) * (1 - gamma fs m)).
{ apply (Rplus_le_reg_r (gamma fs m * gamma fs (n + 2 * m))); ring_simplify.
  apply Rle_trans with (gamma fs n + gamma fs (2 * m)); [|by apply gamma_plus].
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  apply Rle_trans with (INR 2 * gamma fs m); [|by apply gamma_mult_nat].
  rewrite Rmult_plus_distr_r Rmult_1_l; apply Rplus_le_compat_r.
  by apply gamma_mult; [rewrite mul2n -addnn addnA; apply leq_addl|]. }
apply Rmult_le_compat_l; [by apply gamma_pos|].
apply Rabs_ge; right; bounded_lra fs.
Qed.

(** Although (1 + t_n) / (1 + t_m) = (1 + t_(n+m)) doesn't hold,
    \prod_n (1 + d) / \prod_m (1 + d) = 1 + t_(n+m)
    holds by recursive application of the following
    (c.f., Section Phi below). *)
Lemma gammap1_div_epsp1 n : (INR n.+1) * eps fs < 1 ->
  forall (t : b_gamma fs n) (d : b_eps fs),
  exists t' : b_gamma fs n.+1, (1 + t) / (1 + d) = 1 + t'.
Proof.
move=> Hn t d.
have Hn' := bg_S Hn.
suff H : Rabs ((1 + t) / (1 + d) - 1) <= gamma fs (n.+1).
{ exists (Build_bounded H); simpl; ring. }
have Nz1d : (1 + d)%Re <> 0 by bounded_lra fs.
replace (_ - 1) with ((t - d) / (1 + d)); [|by field].
rewrite Rabs_mult Rabs_Rinv; [|by []].
apply (Rmult_le_reg_r (Rabs (1 + d))); [by apply Rabs_pos_lt|].
rewrite Rmult_assoc Rinv_l; [|by apply Rabs_no_R0]; rewrite Rmult_1_r.
apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_Ropp.
apply Rle_trans with (gamma fs n + eps fs).
{ by apply Rplus_le_compat; [case t|case d]. }
apply Rle_trans with (gamma fs n.+1 * (1 - eps fs)).
{ rewrite /gamma; field_simplify; [|lra|lra].
  apply (Rmult_le_reg_r (- INR n * eps fs + 1)%Re); [lra|].
  apply (Rmult_le_reg_r (- eps fs * INR n.+1 + 1)%Re); [lra|].
  field_simplify; [|lra|lra].
  rewrite /Rdiv Rinv_1 !Rmult_1_r.
  have H : - INR n * eps fs ^ 2 <= 0.
  { rewrite -Ropp_0 Ropp_mult_distr_l_reverse; apply Ropp_le_contravar.
    by apply Rmult_le_pos; [apply pos_INR|apply pow2_ge_0]. }
  rewrite S_INR; lra. }    
apply Rmult_le_compat_l; [by apply gamma_pos|].
apply Rabs_ge; right; bounded_lra fs.
Qed.

End Gamma_props.

(** ** Properties of [phi i j d = \prod_{k = i}^{j-1} (1 + d_k)]
    with [|d_k| <= eps]. *)
Section Phi.

Variable fs : Float_spec.

Definition phi i j n (d : b_eps fs ^ n) : R :=
  \prod_(k < n | (i <= k < j)%N) (1 + d k)%Re.

Lemma phi_eq i j n (d1 d2 : b_eps fs ^ n) :
  (forall i, d1 i = d2 i :> R) -> phi i j d1 = phi i j d2.
Proof. by move=> Hd; rewrite /phi; apply /eq_bigr => i'; rewrite Hd. Qed.

Lemma phi_pos i j n d : 0 < @phi i j n d.
Proof.
move: n d; elim=> [|n IHn] d; rewrite /phi.
{ by rewrite big_ord0; apply Rlt_0_1. }
apply big_rec; [by rewrite /GRing.one /=; lra|move=> i' x _ Px].
rewrite /GRing.mul /=; apply Rmult_lt_0_compat; [|exact Px].
bounded_lra_with fs (d i').
Qed.

Lemma phi_split j i l (Hj : (i <= j <= l)%N) n d :
  @phi i l n d = phi i j d * phi j l d.
Proof.
rewrite /phi; destruct (andb_prop _ _ Hj) as (Hj1, Hj2); clear Hj.
rewrite (bigID (fun k : 'I_n => (k < j)%N)) /=.
apply f_equal2; apply eq_bigl; move=> k /=; case (leqP i k);
case (ltnP k j); case (ltnP k l) => H1 H2 H3 /= //; rewrite -(ltnn k).
{ by apply (leq_trans H2), (leq_trans Hj2). }
by apply (leq_trans H3), (leq_trans Hj1).
Qed.

Lemma phi_cut j i n d : (n <= j)%N -> @phi i j n d = phi i n d.
Proof.
move=> Hnj.
case (leqP i n) => Hi.
{ rewrite (@phi_split n); [|by apply /andP].
  rewrite {2}/phi big_pred0; [by rewrite Rmult_1_r|].
  case=> /= k Hk; apply /andP => H; destruct H as (H,_).
  by apply /(lt_irrefl n) /ltP /(leq_ltn_trans H). }
rewrite /phi big_pred0; [rewrite big_pred0 //|];
case=> /= k Hk; apply /andP => H; destruct H as (H, _);
by apply /(lt_irrefl n) /ltP /(leq_trans Hi) /(leq_trans H) /ltnW.
Qed.

Lemma phi_recl n (d : b_eps fs ^ n.+1) :
  (phi 0 n.+1 d = (1 + d ord0) * phi 0 n [ffun i => d (lift ord0 i)])%Re.
Proof.
rewrite /phi (eq_bigl xpredT); [|by case].
rewrite big_ord_recl; apply Rmult_eq_compat_l.
by apply eq_big; [by case|]; move=> i; rewrite ffunE.
Qed.

Lemma phi_lift0 n (i : 'I_n) (d : b_eps fs ^ n.+1) :
  phi (lift ord0 i) n.+1 d = phi i n [ffun i => d (lift ord0 i)].
Proof.
rewrite /phi big_mkcond big_ord_recl /= GRing.mul1r -big_mkcond /=.
by apply /eq_big => k /=; [case i; case k|rewrite ffunE].
Qed.
  
(* begin hide *)
Let phi_gamma_aux i j n (Hj : (j <= n.+1)%N)
                  (Hjmi : 2 * INR (j - i) * eps fs < 1) d :
  exists t : b_gamma fs (j - i), @phi i j n.+1 d = 1 + t.
Proof.
elim: j Hj Hjmi d => [|j IHj] Hj Hjmi d.
{ exists (b_gamma_0 (bg_2 Hjmi)); rewrite Rplus_0_r.
  by rewrite /phi big_pred0; [|move=> nu /=; case (leqP i nu)]. }
case (leqP j.+1 i) => Hij.
{ exists (b_gamma_0 (bg_2 Hjmi)); rewrite Rplus_0_r.
  rewrite /phi big_pred0 // => k /=.
  case (leqP i k); case (ltnP k j.+1) => H1 H2 //=.
  by rewrite -(ltnn k); apply sym_eq, (leq_trans H1), (leq_trans Hij). }
have Hj1mi := bg_2_le (leq_sub2r i (leqnSn j)) Hjmi.
have [t' Ht'] := IHj (ltnW Hj) Hj1mi d.
have Hij1 : (j.+1 - i = (j - i).+1)%N; [by rewrite subSn|].
have [t'' Ht''] := gammap1_mult_epsp1 (bg_2_eq Hij1 Hjmi) t' (d (inord j)).
exists (cast_b_gamma (sym_eq Hij1) t'').
rewrite -Ht'' -Ht' (@phi_split j); [apply Rmult_eq_compat_l|by apply /andP].
rewrite /phi (big_pred1 (inord j)) // => k /=.
by rewrite eqE /= eq_sym eqn_leq (inordK Hj).
Qed.

(* end hide *)
(** phi i j d = 1 + t with |t| <= gamma (j - i) *)
Lemma phi_gamma i j n (Hjmi : 2 * INR (j - i) * eps fs < 1) d :
  exists t : b_gamma fs (j - i), @phi i j n d = 1 + t.
Proof.
case: n Hjmi d => [|n] Hjmi d.
{ by exists (b_gamma_0 (bg_2 Hjmi)); rewrite Rplus_0_r /phi big_ord0. }
case (leqP j n.+1) => Hj; [by apply phi_gamma_aux|].
have Hjnmi := leq_sub2r i (ltnW Hj).
have [t Ht] := phi_gamma_aux (leqnn n.+1) (bg_2_le Hjnmi Hjmi) d.
exists (widen_b_gamma Hjnmi (bg_2 Hjmi) t).
by rewrite -Ht (phi_cut _ _ (ltnW Hj)).
Qed.

(** phi i j d = 1 + t with |t| <= gamma n *)
Lemma phi_gamman i j n (Hn : 2 * INR n * eps fs < 1) d :
  exists t : b_gamma fs n, @phi i j n d = 1 + t.
Proof.
case (leqP j n) => Hj.
{ have Hjmi : (j - i <= n)%N.
  { rewrite leq_subLR; apply (leq_trans Hj), leq_addl. }
  have [t Ht] := phi_gamma (bg_2_le Hjmi Hn) d.
  by exists (widen_b_gamma Hjmi (bg_2 Hn) t); rewrite Ht. }
have [t Ht] := phi_gamma (bg_2_le (leq_subr i n) Hn) d.
exists (widen_b_gamma (leq_subr i n) (bg_2 Hn) t).
by rewrite -Ht (phi_cut _ _ (ltnW Hj)).
Qed.  

(* begin hide *)
Let inv_phi_gamma_aux i j n (Hj: (j <= n.+1)%N)
                      (Hjmi : INR (j - i) * eps fs < 1 ) d :
  exists t : b_gamma fs (j - i), / @phi i j n.+1 d = 1 + t.
Proof.
elim: j Hj Hjmi d => [|j IHj] Hj Hjmi d.
{ exists (b_gamma_0 Hjmi); rewrite Rplus_0_r.
  by rewrite /phi big_pred0; [rewrite Rinv_1|move=> nu /=; case (leqP i nu)]. }
case (leqP j.+1 i) => Hij.
{ exists (b_gamma_0 Hjmi); rewrite Rplus_0_r.
  rewrite /phi big_pred0; [by rewrite Rinv_1|move=> nu /=].
  case (leqP i nu); case (ltnP nu j.+1) => H1 H2 //=.
  by rewrite -(ltnn nu); apply sym_eq, (leq_trans H1), (leq_trans Hij). }
have Hj1mi := bg_le (leq_sub2r i (leqnSn j)) Hjmi.
have [t' Ht'] := IHj (ltnW Hj) Hj1mi d.
have Hij1 : (j.+1 - i = (j - i).+1)%N; [by rewrite subSn|].
have [t'' Ht''] := gammap1_div_epsp1 (bg_eq Hij1 Hjmi) t' (d (inord j)).
exists (cast_b_gamma (sym_eq Hij1) t'').
rewrite -Ht'' -Ht' (@phi_split j); [|by apply /andP].
rewrite Rinv_mult_distr; try apply Rgt_not_eq, phi_pos; apply Rmult_eq_compat_l.
rewrite /phi (big_pred1 (inord j)) // => nu /=.
by rewrite eqE /= eq_sym eqn_leq (inordK Hj).
Qed.

(* end hide *)
(** 1 / phi i j d = 1 + t with |t| <= gamma (j - i) *)
Lemma inv_phi_gamma i j n (Hjmi : INR (j - i) * eps fs < 1) d :
  exists t : b_gamma fs (j - i), / @phi i j n d = 1 + t.
Proof.
case: n Hjmi d => [|n] Hjmi d.
{ by exists (b_gamma_0 Hjmi); rewrite Rplus_0_r /phi big_ord0 Rinv_1. }
case (leqP j n.+1) => Hj; [by apply inv_phi_gamma_aux|].
have Hjnmi := leq_sub2r i (ltnW Hj).
have [t Ht] := inv_phi_gamma_aux (leqnn n.+1) (bg_le Hjnmi Hjmi) d.
exists (widen_b_gamma Hjnmi Hjmi t).
by rewrite -Ht (phi_cut _ _ (ltnW Hj)).
Qed.

(** 1 / phi i j d = 1 + t with |t| <= gamma n *)
Lemma inv_phi_gamman i j n (Hn : INR n * eps fs < 1) d :
  exists t : b_gamma fs n, / @phi i j n d = 1 + t.
Proof.
case (leqP j n) => Hj.
{ have Hjmi : (j - i <= n)%N.
  { rewrite leq_subLR; apply (leq_trans Hj), leq_addl. }
  have [t Ht] := inv_phi_gamma (bg_le Hjmi Hn) d.
  by exists (widen_b_gamma Hjmi Hn t); rewrite Ht. }
have [t Ht] := inv_phi_gamma (bg_le (leq_subr i n) Hn) d.
exists (widen_b_gamma (leq_subr i n) Hn t).
by rewrite -Ht (phi_cut _ _ (ltnW Hj)).
Qed.

End Phi.
