(** * Application: corollary of [ellipsid_error] considering overflows. *)

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

Require Import real_matrix.

Require Import gamma fsum fdotprod ellipsoid_error float_infnan_spec.

Section Fellipsoid_error_infnan.

Variable fs : Float_infnan_spec.

(** Sum [c + \sum a_i] computed in float (with overflow) from left to right. *)
Fixpoint fisum_l2r_rec n (c : FI fs) : FI fs ^ n -> FI fs :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fisum_l2r_rec (fiplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i] computed in float (with overflow) from left to right. *)
Definition fisum_l2r n : FI fs ^ n -> FI fs :=
  match n with
    | 0%N => fun _ => FI0 fs
    | n'.+1 =>
      fun a => fisum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i b_i] computed in float (with overflow) from left to right. *)
Definition fidotprod_l2r n (a b : FI fs ^ n) : FI fs :=
  fisum_l2r [ffun i => fimult (a i) (b i)].

(** Sum [\sum a_i b_i] computed in float (with overflow) from left to right
    with a_i \in R, b_i \in F. *)
Definition fidotprod_l2r_fstr (k : nat) (a : R ^ k) (b : FI fs ^ k) : FI fs :=
  fidotprod_l2r [ffun i => firnd fs (a i)] b.

Lemma fisum_l2r_rec_eq n (c1 : FI fs) (a1 : FI fs ^ n)
      (c2 : FI fs) (a2 : FI fs ^ n) :
  c1 = c2 -> (forall i, a1 i = a2 i) ->
  fisum_l2r_rec c1 a1 = fisum_l2r_rec c2 a2.
Proof.
elim: n c1 a1 c2 a2 => [//|n IHn] c1 a1 c2 a2 Hc Ha.
by apply IHn; [rewrite /fplus Hc Ha|move=> i; rewrite !ffunE].
Qed.

Lemma fisum_l2r_eq n (a1 : FI fs ^ n) (a2 : FI fs ^ n) :
  (forall i, a1 i = a2 i) -> fisum_l2r a1 = fisum_l2r a2.
Proof.
case: n a1 a2 => [//|n] a1 a2 Ha.
by apply fisum_l2r_rec_eq; [|move=> i; rewrite !ffunE].
Qed.

Lemma fisum_l2r_rec_r n (c : FI fs) (a : FI fs ^ n.+1) :
  fisum_l2r_rec c a
  = fiplus (fisum_l2r_rec c [ffun i : 'I_n => a (inord i)]) (a (inord n)).
Proof.
elim: n c a => [|n IHn] c a; rewrite /fisum_l2r_rec.
{ by simpl; apply f_equal, f_equal2; [|apply ord_inj; rewrite inordK]. }
rewrite -/fisum_l2r_rec (IHn (fiplus _ _) _) ffunE; apply f_equal2.
{ apply fisum_l2r_rec_eq => [|i]; rewrite !ffunE; apply f_equal.
  { by apply f_equal, ord_inj; rewrite inordK. }
  apply ord_inj; rewrite inordK /=.
  { by apply f_equal2; [by []|apply inordK, (ltn_trans (ltn_ord i))]. }
    apply ltn_trans with i.+2; [by []|].
  rewrite -addn2 -(addn2 n) ltn_add2r; apply ltn_ord. }
apply f_equal; apply ord_inj; rewrite lift0 inordK // inordK //.
Qed.

Lemma fisum_l2r_r n (a : FI fs ^ n.+2) :
  fisum_l2r a
  = fiplus (fisum_l2r [ffun i : 'I_n.+1 => a (inord i)]) (a (inord n.+1)).
Proof.
rewrite /fisum_l2r fisum_l2r_rec_r; apply f_equal2.
{ apply fisum_l2r_rec_eq => [|i]; rewrite !ffunE; apply f_equal.
  { by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite !lift0 inordK.
  { rewrite inordK // -addn2 -(addn2 n) leq_add2r; apply ltnW, ltn_ord. }
  apply ltnW, ltn_ord. }
rewrite ffunE; apply f_equal, ord_inj; rewrite lift0 inordK // inordK //.
Qed.

Lemma fidotprod_l2r_r n (a b : FI fs ^ n.+2) :
  fidotprod_l2r a b
  = fiplus (fidotprod_l2r [ffun i : 'I_n.+1 => a (inord i)]
                          [ffun i : 'I_n.+1 => b (inord i)])
           (fimult (a (inord n.+1)) (b (inord n.+1))).
Proof.
rewrite /fidotprod_l2r fisum_l2r_r; apply f_equal2.
{ by apply fisum_l2r_eq => i; rewrite !ffunE. }
by rewrite ffunE.
Qed.

Lemma fidotprod_l2r_fstr_r n (a : R ^ n.+2) (b : FI fs ^ n.+2) :
  fidotprod_l2r_fstr a b
  = fiplus (fidotprod_l2r_fstr [ffun i : 'I_n.+1 => a (inord i)]
                               [ffun i : 'I_n.+1 => b (inord i)])
           (fimult (firnd fs (a (inord n.+1))) (b (inord n.+1))).
Proof.
rewrite /fidotprod_l2r_fstr fidotprod_l2r_r; apply f_equal2.
{ by apply fisum_l2r_eq => i; rewrite !ffunE. }
by rewrite ffunE.
Qed.

(** A bound such that if all arguments of [fidotprod_l2r_fstr]
    are less than it, then no overflow can occur. *)
Definition md2k k := sqrt (m fs / (2 * INR k.+1) - eta (fis fs)) - eta (fis fs).

Lemma md2k_contravar n m : (n <= m)%N -> md2k m <= md2k n.
Proof.
move=> Hnm.
rewrite /md2k; apply Rplus_le_compat_r, sqrt_le_1_alt, Rplus_le_compat_r.
apply (Rmult_le_compat_l _ _ _ (m_pos fs)), Rinv_le.
{ apply Rmult_lt_0_compat; [lra|].
  change 0 with (INR 0); apply lt_INR, lt_0_Sn. }
by apply Rmult_le_compat_l; [lra|]; apply /le_INR /le_n_S /leP.
Qed.

Lemma md2k_expr_lt_m_aux k (Hke : 2 * INR k.+1 * eta (fis fs) < 1) (x : R) :
  Rabs x < md2k k ->
  2 * INR k * x² + 2 * INR k * (1 + Rabs x) * eta (fis fs) < m fs.
Proof.
move=> Hx.
have H2k : 0 < 2 * INR k.+1.
{ apply Rmult_lt_0_compat; [lra|]; change 0 with (INR 0); apply lt_INR; omega. }
apply (Rmult_lt_reg_r (/ (2 * INR k.+1))); [by apply Rinv_0_lt_compat|].
apply Rle_lt_trans with (x² + (1 + Rabs x) * eta (fis fs)).
{ rewrite Rmult_comm; apply (Rmult_le_reg_l (2 * INR k.+1)); [by []|].
  rewrite -Rmult_assoc Rinv_r; [|lra]; rewrite Rmult_1_l.
  rewrite (Rmult_assoc _ (_ +_)) -Rmult_plus_distr_l; apply Rmult_le_compat_r.
  { apply Rplus_le_le_0_compat; [by apply Rle_0_sqr|]; apply Rmult_le_pos.
    { apply Rplus_le_le_0_compat; [lra|apply Rabs_pos]. }
    apply Rlt_le, eta_pos. }
  apply Rmult_le_compat_l; [lra|]; apply le_INR; omega. }
apply (Rplus_lt_reg_r (- eta (fis fs))); ring_simplify.
apply Rle_lt_trans with ((Rabs x + eta (fis fs) / 2)²).
{ rewrite /Rsqr; field_simplify; rewrite /Rdiv Rinv_1 Rmult_1_r.
  rewrite /Rdiv (Rmult_comm _ (/ 4)) 2!Rmult_plus_distr_l.
  rewrite -!(Rmult_assoc (/ 4)) !(Rmult_assoc (/ 4) 2) Rinv_l; [|lra].
  rewrite !Rmult_1_l -(Rplus_0_r (_ + _)) pow2_abs; apply Rplus_le_compat_l.
  unfold pow; rewrite Rmult_1_r.
  do 2 (apply Rmult_le_pos; [|by apply Rlt_le, eta_pos]); lra. }
rewrite (Rplus_comm (- _)) -(Rsqr_sqrt (_ + - _)).
{ apply Rsqr_lt_abs_1; rewrite Rabs_pos_eq.
  { rewrite (Rabs_pos_eq (sqrt _)); [|by apply sqrt_pos].
    apply (Rplus_lt_reg_r (- eta (fis fs))).
    apply (Rle_lt_trans _ (Rabs x)); [|by apply Hx].
    rewrite Rplus_assoc -{2}(Rplus_0_r (Rabs _)); apply Rplus_le_compat_l.
    apply (Rplus_le_reg_r (eta (fis fs))); ring_simplify.
    rewrite -{2}(Rmult_1_r (eta _)); apply Rmult_le_compat_l; [|lra].
    apply Rlt_le, eta_pos. }
  apply Rplus_le_le_0_compat; [by apply Rabs_pos|].
  by apply Rmult_le_pos; [apply Rlt_le, eta_pos|lra]. }
apply (Rplus_le_reg_r (eta (fis fs))); ring_simplify; rewrite Rmult_comm.
apply (Rmult_le_reg_l (2 * INR k.+1)); [by []|].
rewrite -Rmult_assoc Rinv_r; [|lra]; rewrite Rmult_1_l.
apply (Rle_trans _ _ _ (Rlt_le _ _ Hke)), (Rle_trans _ 2); [lra|]; apply m_ge_2.
Qed.

Lemma md2k_expr_lt_m k (Hke : 2 * INR k.+1 * eta (fis fs) < 1) (x y : R) :
  Rabs x < md2k k -> Rabs y < md2k k ->
  2 * INR k * (Rabs x * Rabs y)
  + 2 * INR k * (1 + Rabs y) * eta (fis fs) < m fs.
Proof.
move=> Hx Hy.
set (z := Rmax (Rabs x) (Rabs y)).
apply Rle_lt_trans
with (2 * INR k * z² + 2 * INR k * (1 + z) * eta (fis fs)).
{ apply Rplus_le_compat.
  { rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
    apply Rmult_le_compat_l; [by apply pos_INR|].
    apply Rmult_le_compat; try apply Rabs_pos; try apply Rmax_l; apply Rmax_r. }
  apply Rmult_le_compat_r; [by apply Rlt_le, eta_pos|].
  rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  apply Rmult_le_compat_l; [by apply pos_INR|].
  apply Rplus_le_compat_l, Rmax_r. }
have Pz : 0 <= z; [by apply (Rle_trans _ _ _ (Rabs_pos x)), Rmax_l|].
rewrite -{2}(Rabs_pos_eq _ Pz).
apply (md2k_expr_lt_m_aux Hke).
by rewrite (Rabs_pos_eq _ Pz); apply Rmax_lub_lt.
Qed.  

Lemma lemma_rnd_f k x : Rabs x < md2k k -> finite (firnd fs x).
Proof.
move=> Hx; apply firnd_spec_f.
have [d [e Hde]] := frnd_spec (fis fs) x.
rewrite Hde.
apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
apply Rle_lt_trans with (2 * Rabs x + eta (fis fs)).
{ apply Rplus_le_compat; [|by case e].
  rewrite Rabs_mult; apply Rmult_le_compat_r; [by apply Rabs_pos|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_pos_eq; [|lra].
  apply Rplus_le_compat_l; case d => d' Hd' /=.
  apply (Rle_trans _ _ _ Hd'), Rlt_le, eps_lt_1. }
apply (Rplus_lt_reg_r (- eta (fis fs))); ring_simplify.
apply (Rmult_lt_reg_l (/ 2)); [lra|].
rewrite -Rmult_assoc Rinv_l; [|lra]; rewrite Rmult_1_l.
apply (Rlt_le_trans _ _ _ Hx).
rewrite /md2k.
apply (Rplus_le_reg_r (eta (fis fs))); ring_simplify.
apply Rle_trans with (/ 2 * m fs).
{ apply Rle_trans with (sqrt (m fs / (2 * INR k.+1))).
  { apply sqrt_le_1_alt.
    rewrite -{2}(Rplus_0_r (_ / _)); apply Rplus_le_compat_l.
    rewrite -Ropp_0; apply Ropp_le_contravar, Rlt_le, eta_pos. }
  apply Rle_trans with (sqrt (/ 2 * m fs)).
  { apply sqrt_le_1_alt; rewrite /Rdiv Rmult_comm.
    apply Rmult_le_compat_r; [by apply m_pos|].
    apply Rinv_le; [lra|].
    rewrite -{1}(Rmult_1_r 2); apply Rmult_le_compat_l; [lra|].
    change 1 with (INR 1); apply le_INR; omega. }
  apply sqrtx_le_x, (Rmult_le_reg_l 2); [lra|].
  rewrite Rmult_1_r -Rmult_assoc Rinv_r; [|lra].
  rewrite Rmult_1_l; apply m_ge_2. }
rewrite -{1}(Rplus_0_l (_ * _)); apply Rplus_le_compat_r.
apply (Rmult_le_reg_l 2); [lra|]; rewrite Rmult_0_r; field_simplify.
rewrite /Rdiv Rmult_0_l Rinv_1 Rmult_1_r.
apply Rlt_le, eta_pos.
Qed.

Lemma lemma_rnd k x :
  Rabs x < md2k k -> FI2F (firnd fs x) = frnd (fis fs) x :> R.
Proof. move=> Hx; apply firnd_spec, (lemma_rnd_f Hx). Qed.

Lemma lemma_prod_f (H2 : 2 * INR 2 * eps (fis fs) < 1)
      (H2e : 2 * INR 2 * eta (fis fs) < 1)
      (x : R) (y : FI fs) :
  Rabs x < md2k 1 -> finite y -> Rabs (FI2F y) < md2k 1 ->
  finite (fimult (firnd fs x) y).
Proof.
move=> Hx Fx Hy.
apply fimult_spec_f; [by apply (lemma_rnd_f Hx)|by []|].
rewrite /fmult (lemma_rnd Hx).
replace (frnd _ _ : F (fis fs))
with (@fdotprod_l2r_fstr (fis fs) 1 [ffun _ => x] [ffun _ => FI2F y]);
  [|by rewrite /fdotprod_l2r_fstr /fdotprod_l2r /fsum_l2r /= !ffunE].
have [o [e [e' Hoee']]] :=
  fdotprod_l2r_fstr_err H2 [ffun _ => x] [ffun _ => FI2F y].
rewrite Hoee' !zmodp.big_ord1 !ffunE.
rewrite Rplus_assoc; apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
apply Rle_lt_trans
with (2 * Rabs x * Rabs (FI2F y) + 2 * (1 + Rabs (FI2F y)) * eta (fis fs)).
{ apply Rplus_le_compat.
  { apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite !Rabs_mult !Rabs_Rabsolu.
    rewrite -{1}(Rmult_1_l (_ * _)) -Rmult_plus_distr_r Rmult_assoc.
    apply Rmult_le_compat_r; [by apply Rmult_le_pos; apply Rabs_pos|].
    apply (Rplus_le_reg_r (- 1)); ring_simplify.
    by case o => o' Ho'; apply (Rle_trans _ _ _ Ho'), Rlt_le, gamma_lt_1. }
  simpl; replace (_ + _) with (2 * (1 * e + Rabs (FI2F y) * e')) by ring.
  rewrite Rmult_assoc Rabs_mult Rabs_pos_eq; [|lra].
  apply Rmult_le_compat_l; [lra|]; apply (Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite Rmult_plus_distr_r !Rabs_mult Rabs_Rabsolu; apply Rplus_le_compat.
  { by rewrite Rabs_R1 !Rmult_1_l; case e. }
  by apply Rmult_le_compat_l; [by apply Rabs_pos|]; case e'. }
apply Rle_lt_trans
with (2 * INR 1 * (Rabs x * Rabs (FI2F y))
      + 2 * INR 1 * (1 + Rabs (FI2F y)) * eta (fis fs));
  [by simpl; right; ring|].
by apply (md2k_expr_lt_m H2e).
Qed.

Lemma lemma_prod (H2 : 2 * INR 2 * eps (fis fs) < 1)
      (H2e : 2 * INR 2 * eta (fis fs) < 1)
      (x : R) (y : FI fs) :
  Rabs x < md2k 1 -> finite y -> Rabs (FI2F y) < md2k 1 ->
  FI2F (fimult (firnd fs x) y) = fmult (frnd (fis fs) x) (FI2F y) :> R.
Proof.
move=> Hx Fx Hy.
rewrite fimult_spec; [|by apply lemma_prod_f].
by rewrite /fmult (lemma_rnd Hx).
Qed.

(** If all arguments of [fidotprod_l2r_fstr] are less than [md2k],
    then no overflow occurs and the result is finite and the same than
    previously obtained from [fdotprod_l2r_fstr] when ignorign overflows. *)
Lemma fidotprod_l2r_fstr_bounded k (Hk : 2 * INR k.+1 * eps (fis fs) < 1)
      (Hke : 2 * INR k.+1 * eta (fis fs) < 1)
      (a : R ^ k) (b : FI fs ^ k) :
      (forall i, Rabs (a i) < md2k k) ->
      (forall i, finite (b i)) ->
      (forall i, Rabs (FI2F (b i)) < md2k k) ->
      finite (fidotprod_l2r_fstr a b) /\
      FI2F (fidotprod_l2r_fstr a b)
      = fdotprod_l2r_fstr a [ffun i => FI2F (b i)] :> R.
Proof.
case: k Hk Hke a b => [|k] Hk Hke a b Ha Fb Hb.
{ rewrite /fidotprod_l2r_fstr /fidotprod_l2r /fisum_l2r.
  rewrite /fdotprod_l2r_fstr /fdotprod_l2r /fsum_l2r.
  by split; [apply finite0|apply FI2F0]. }
elim: k Hk Hke a b Ha Fb Hb => [|k IHk] Hk Hke a b Ha Fb Hb.
{ rewrite /fidotprod_l2r_fstr /fidotprod_l2r /fisum_l2r /fisum_l2r_rec /=.
  rewrite /fdotprod_l2r_fstr /fdotprod_l2r /fsum_l2r /fsum_l2r_rec !ffunE.
  by split; [apply lemma_prod_f|apply lemma_prod]. }
have Hk' := bg_2S Hk.
have Hke' : 2 * INR k.+2 * eta (fis fs) < 1.
{ apply Rle_lt_trans with (2 * INR k.+3 * eta (fis fs)); [|by []].
  apply Rmult_le_compat_r; [by apply Rlt_le, eta_pos|].
  apply Rmult_le_compat_l; [lra|]; apply le_INR; omega. }
set (a' := [ffun i : 'I_k.+1 => a (inord i)]).
set (b' := [ffun i : 'I_k.+1 => b (inord i)]).
have Ha' : forall i, Rabs (a' i) < md2k k.+1.
{ move=> i; rewrite /a' ffunE.
  by apply Rlt_le_trans with (md2k k.+2); [|apply md2k_contravar]. }
have Fb' : forall i, finite (b' i); [by move=> i; rewrite /b' ffunE|].
have Hb' : forall i, Rabs (FI2F (b' i)) < md2k k.+1.
{ move=> i; rewrite /b' ffunE.
  by apply Rlt_le_trans with (md2k k.+2); [|apply md2k_contravar]. }
have H'' := (IHk Hk' Hke' a' b' Ha' Fb' Hb').
destruct H'' as (F', H'); clear IHk.
have H2 : 2 * INR 2 * eps (fis fs) < 1; [by apply (@ bg_2_le _ _ k.+2)|].
have H2e : 2 * INR 2 * eta (fis fs) < 1.
{ apply Rle_lt_trans with (2 * INR k.+2 * eta (fis fs)); [|by []].
  apply Rmult_le_compat_r; [by apply Rlt_le, eta_pos|].
  apply Rmult_le_compat_l; [lra|]; apply le_INR; omega. }
have Ha1 : Rabs (a (inord k.+1)) < md2k 1.
{ by apply Rlt_le_trans with (md2k k.+2); [|apply md2k_contravar]. }
have Fb1 := Fb (inord k.+1).
have Hb1 : Rabs (FI2F (b (inord k.+1))) < md2k 1.
{ by apply Rlt_le_trans with (md2k k.+2); [|apply md2k_contravar]. }
have F : finite (fidotprod_l2r_fstr a b); [|split; [by []|]].
{ rewrite fidotprod_l2r_fstr_r.
  apply fiplus_spec_f; [by []|by apply lemma_prod_f|].
  rewrite /fplus H' lemma_prod //.
  replace (frnd _ _ : R) with (fdotprod_l2r_fstr a [ffun i => FI2F (b i)] : R).
  { have [o [e [e' Hoee']]] :=
      fdotprod_l2r_fstr_err Hk a [ffun i => FI2F (b i)]; rewrite Hoee'.
    set (aa := [ffun i => Rabs (a i)]); set (ma := max_tuple aa).
    set (ab := [ffun i => Rabs (FI2F (b i))]); set (mb := max_tuple ab).
    apply Rle_lt_trans with (2 * INR k.+2 * (Rabs ma * Rabs mb)
                             + 2 * INR k.+2 * (1 + Rabs mb) * eta (fis fs)).
    { rewrite Rplus_assoc; apply (Rle_trans _ _ _ (Rabs_triang _ _)).
      apply Rplus_le_compat.
      { apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_mult.
        set (s := \sum__ Rabs _).
        apply Rle_trans with (s + Rabs o * Rabs s).
        { apply Rplus_le_compat_r, (Rle_trans _ _ _ (big_Rabs_triang _)).
          by right; apply eq_bigr => i _. }
        rewrite (Rabs_pos_eq s); [|by apply big_sum_Rabs_pos].
        rewrite -{1}(Rmult_1_l s) -Rmult_plus_distr_r.
        apply Rle_trans with (2 * s).
        { apply Rmult_le_compat_r; [by apply big_sum_Rabs_pos|].
          apply (Rplus_le_reg_r (- 1)); ring_simplify; case o => o' Ho'.
          by apply (Rle_trans _ _ _ Ho'), Rlt_le, gamma_lt_1. }
        rewrite Rmult_assoc; apply Rmult_le_compat_l; [lra|].
        replace s with ((\sum_i ([ffun i => Rabs (a i * FI2F (b i))] i))).
        { apply (Rle_trans _ _ _ (max_tuple_sum _)).
          apply Rmult_le_compat_l; [by apply pos_INR|].
          apply Rle_trans with (max_tuple [ffun i => aa i * ab i]).
          { by right; apply max_tuple_eq => i; rewrite !ffunE Rabs_mult. }
          rewrite Rabs_pos_eq; [rewrite Rabs_pos_eq|].
          { apply max_tuple_prod => i; rewrite ffunE; apply Rabs_pos. }
          { apply Rle_trans with (ab ord0); [rewrite ffunE; apply Rabs_pos|].
            apply max_tuple_i. }
          apply Rle_trans with (aa ord0); [rewrite ffunE; apply Rabs_pos|].
          apply max_tuple_i. }
        by apply eq_bigr => i _; rewrite !ffunE Rabs_mult. }
      rewrite !Rmult_assoc -Rmult_plus_distr_l Rabs_mult Rabs_pos_eq; [|lra].
      apply Rmult_le_compat_l; [lra|].
      rewrite Rmult_plus_distr_r Rmult_plus_distr_l.
      apply (Rle_trans _ _ _ (Rabs_triang _ _)); apply Rplus_le_compat.
      { rewrite Rabs_mult Rmult_1_l Rabs_pos_eq; [|by apply pos_INR].
        by apply Rmult_le_compat_l; [apply pos_INR|case e]. }
      rewrite Rmult_comm Rabs_mult -Rmult_assoc.
      apply Rmult_le_compat; try apply Rabs_pos; [|by case e'].
      rewrite Rabs_pos_eq; [|by apply big_sum_Rabs_pos].
      replace (\sum__ _ : R) with (\sum_i ab i).
      { apply (Rle_trans _ _ _ (max_tuple_sum _)).
        apply Rmult_le_compat_l; [apply pos_INR|].
        by apply Rabs_ge; right; right. }
      by apply eq_bigr => i _; rewrite !ffunE. }
    apply (md2k_expr_lt_m Hke).
    { rewrite Rabs_pos_eq.
      { by apply max_tuple_lub_lt => i; rewrite ffunE. }
      apply Rle_trans with (aa ord0); [rewrite ffunE; apply Rabs_pos|].
      apply max_tuple_i. }
    rewrite Rabs_pos_eq.
    { by apply max_tuple_lub_lt => i; rewrite ffunE. }
    apply Rle_trans with (ab ord0); [rewrite ffunE; apply Rabs_pos|].
    apply max_tuple_i. }
  rewrite fdotprod_l2r_fstr_r /fplus; do 2 apply f_equal; apply f_equal2.
  { by apply fdotprod_l2r_fstr_eq => i; rewrite !ffunE. }
  by rewrite /fmult; do 2 apply f_equal; apply f_equal2; try rewrite ffunE. }
rewrite fidotprod_l2r_fstr_r fiplus_spec; [|by rewrite -fidotprod_l2r_fstr_r].
rewrite fdotprod_l2r_fstr_r /fplus; do 2 apply f_equal; apply f_equal2.
{ by rewrite H'; apply fdotprod_l2r_fstr_eq => i; rewrite !ffunE. }
rewrite lemma_prod // /fmult; do 2 apply f_equal; apply f_equal2 => //.
by rewrite ffunE.
Qed.

(** A x + B u computed in float (with overflows, from left to right). *)
Definition fiAxBu (n p : nat)
           (A : 'M[R]_n) (x : 'cV[FI fs]_n)
           (B : 'M[R]_(n, p)) (u : 'cV[FI fs]_p) :=
  \col_i (fidotprod_l2r_fstr
            [ffun k => row_mx A B i k] [ffun k => col_mx x u k ord0]).

Definition MFI2F := map_mx (@FI2F fs).

Lemma fiAxBu_bounded_aux n p (Hnp : 2 * INR (n + p).+1 * eps (fis fs) < 1)
      (Hnpe : 2 * INR (n + p).+1 * eta (fis fs) < 1)
      (A : 'M[R]_n) (x : 'cV[FI fs]_n) (B : 'M[R]_(n, p)) (u : 'cV[FI fs]_p) :
  (forall i j, Rabs (A i j) < md2k (n + p)) ->
  (forall i j, Rabs (B i j) < md2k (n + p)) ->
  (forall i, finite (x i ord0)) -> (forall i, finite (u i ord0)) ->
  (forall i, Rabs (FI2F (x i ord0)) < md2k (n + p)) ->
  (forall i, Rabs (FI2F (u i ord0)) < md2k (n + p)) ->
  (forall i, finite ((fiAxBu A x B u) i ord0)) /\
  MF2R (MFI2F (fiAxBu A x B u)) = MF2R (fAxBu A (MFI2F x) B (MFI2F u)).
Proof.
move=> HA HB Fx Fu Hx Hu.
cut (forall i,
       finite (fidotprod_l2r_fstr
                 [ffun k => row_mx A B i k] [ffun k => col_mx x u k ord0]) /\
       FI2F (fidotprod_l2r_fstr
               [ffun k => row_mx A B i k] [ffun k => col_mx x u k ord0])
       = fdotprod_l2r_fstr
           [ffun k => row_mx A B i k]
           [ffun i => FI2F ([ffun k => col_mx x u k ord0] i)] :> R).
{ move=> H; split.
  { by move=> i; rewrite /fiAxBu mxE; apply H. }
  rewrite -matrixP => i j; rewrite !mxE (proj2 (H i)).
  apply fdotprod_l2r_fstr_eq => k; rewrite !ffunE //.
  by rewrite !mxE; case (split k) => k'; rewrite !mxE. }
by move=> i; apply fidotprod_l2r_fstr_bounded => // k;
  rewrite ffunE mxE; case splitP => j _.
Qed.

Lemma fiAxBu_bounded n p (Hnp : 2 * INR (n + p).+1 * eps (fis fs) < 1)
      (Hnpe : 2 * INR (n + p).+1 * eta (fis fs) < 1) (Hnpm : 1 < md2k (n + p))
      (P : 'M[R]_n) (PP : posdef P)
      (A : 'M[R]_n) (B : 'M[R]_(n, p)) (x : 'cV[FI fs]_n) (u : 'cV[FI fs]_p)
      (s lambda : R) :
  (forall i j, Rabs (A i j) < md2k (n + p)) ->
  (forall i j, Rabs (B i j) < md2k (n + p)) ->
  (forall i, finite (x i ord0)) -> (forall i, finite (u i ord0)) ->
  ((MF2R (MFI2F x))^T *m P *m (MF2R (MFI2F x)) <=m: lambda%:M)%Re ->
  1%:M <=m s *: P -> sqrt (s * lambda) < md2k (n + p) ->
  Mabs (MF2R (MFI2F u)) <=m: \col__ 1%Re ->
  (forall i, finite ((fiAxBu A x B u) i ord0)) /\
  MF2R (MFI2F (fiAxBu A x B u)) = MF2R (fAxBu A (MFI2F x) B (MFI2F u)).
Proof.
move=> HA HB Fx Fu Hx Hs Hlambda Hu; apply fiAxBu_bounded_aux => // i.
{ replace (FI2F _ : R) with ((MF2R (MFI2F x)) i ord0); [|by rewrite !mxE].
  by apply (Rle_lt_trans _ _ _ (lemma_2 PP Hs Hx _)). }
apply Rle_lt_trans with 1; [|by []].
by move: (Hu i ord0); rewrite !mxE.
Qed.
    
End Fellipsoid_error_infnan.
