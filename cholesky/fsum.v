(** * Bounds on the rounding error of summation $\sum_{i=0}^n a_i$#\sum_{i=0}^n a_i#

    The lemmas [*_err_gamma] are of the form
    \exists \theta_i, fl(\sum_i a_i) = \sum_i (1 + \theta_i) a_i /\ \forall i, |\theta_i| <= \gamma_n (sometime required).

    The lemmas [*_err] are of the form
    \exists \theta, |\theta| <= fl(\sum_i a_i) = \sum_i a_i + \theta \sum_i |a_i| /\ |\theta| <= \gamma_n (probably the most useful one).

    The lemmas [*_err_abs] are of the form
    |fl(\sum_i a_i) - \sum_i a_i| <= \gamma_n \sum_i |a_i| (compact but not very convenient).

    The primed versions are for c + \sum_i a_i with no error term on c but rather on fl(\sum_i a_i). *)

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

Require Import gamma.

Section Fsum.

Variable fs : Float_spec.

(** Sum [c + \sum a_i] computed in float from left to right. *)
Fixpoint fsum_l2r_rec n (c : F fs) : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (fplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i] computed in float from left to right. *)
Definition fsum_l2r n : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => F0 fs
    | n'.+1 =>
      fun a => fsum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.

Lemma fsum_l2r_rec_eq n (c1 : F fs) (a1 : F fs ^ n)
      (c2 : F fs) (a2 : F fs ^ n) :
  (c1 = c2 :> R) -> (forall i, a1 i = a2 i :> R) ->
  fsum_l2r_rec c1 a1 = fsum_l2r_rec c2 a2 :> R.
Proof.
elim: n c1 a1 c2 a2 => [//|n IHn] c1 a1 c2 a2 Hc Ha.
by apply IHn; [rewrite /fplus Hc Ha|move=> i; rewrite !ffunE].
Qed.

Lemma fsum_l2r_eq n (a1 : F fs ^ n) (a2 : F fs ^ n) :
  (forall i, a1 i = a2 i :> R) -> fsum_l2r a1 = fsum_l2r a2 :> R.
Proof.
case: n a1 a2 => [//|n] a1 a2 Ha.
by apply fsum_l2r_rec_eq; [|move=> i; rewrite !ffunE].
Qed.

Lemma fsum_l2r_rec_r n (c : F fs) (a : F fs ^ n.+1) :
  fsum_l2r_rec c a
  = fplus (fsum_l2r_rec c [ffun i : 'I_n => a (inord i)]) (a (inord n)) :> R.
Proof.
elim: n c a => [|n IHn] c a; rewrite /fsum_l2r_rec.
{ simpl; apply f_equal, f_equal2; [by []|].
  by apply f_equal, ord_inj; rewrite inordK. }
rewrite -/fsum_l2r_rec (IHn (fplus _ _) _) ffunE.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE; do 2 apply f_equal.
  { apply Rplus_eq_compat_l; do 2 apply f_equal.
    by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite inordK /=.
  { by apply f_equal2; [by []|apply inordK, (ltn_trans (ltn_ord i))]. }
    apply ltn_trans with i.+2; [by []|].
  rewrite -addn2 -(addn2 n) ltn_add2r; apply ltn_ord. }
do 2 apply f_equal; apply ord_inj; rewrite lift0 inordK // inordK //.
Qed.

Lemma fsum_l2r_r n (a : F fs ^ n.+2) :
  fsum_l2r a
  = fplus (fsum_l2r [ffun i : 'I_n.+1 => a (inord i)]) (a (inord n.+1)) :> R.
Proof.
rewrite /fsum_l2r fsum_l2r_rec_r.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE; do 2 apply f_equal.
  { by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite !lift0 inordK.
  { rewrite inordK // -addn2 -(addn2 n) leq_add2r; apply ltnW, ltn_ord. }
  apply ltnW, ltn_ord. }
rewrite ffunE; do 2 apply f_equal.
apply ord_inj; rewrite lift0 inordK // inordK //.
Qed.

Lemma fsum_l2r_rec_err_phi n c (a : F fs ^ n) :
  exists d : b_eps fs ^ n,
    (fsum_l2r_rec c a
     = phi 0 n d * c + \sum_i (phi (nat_of_ord i) n d * a i)%Re :> R)%Re.
Proof.
elim: n c a => [|n IHn] c a.
{ by exists [ffun => eps_0 fs]; rewrite /phi !big_ord0 Rmult_1_l Rplus_0_r. }
set (a' := [ffun i => a (lift ord0 i)]).
have [d' Hd'] := IHn (fplus c (a ord0)) a'; clear IHn.
have [d0 Hd0] := fplus_spec c (a ord0).
exists [ffun i => if unlift ord0 i is Some j then d' j else d0].
rewrite big_ord_recl -Rplus_assoc -Rmult_plus_distr_l Hd' Hd0.
apply f_equal2.
{ rewrite -Rmult_assoc; apply Rmult_eq_compat_r.
  rewrite phi_recl Rmult_comm ffunE unlift_none.
  by apply /Rmult_eq_compat_l /phi_eq => i; rewrite !ffunE liftK. }
apply eq_bigr => i _.
apply f_equal2; [|by rewrite /a' ffunE].
by rewrite phi_lift0; apply /phi_eq => k; rewrite !ffunE liftK.
Qed.

Lemma fsum_l2r_rec_err'_phi n c (a : F fs ^ n) :
  exists d : b_eps fs ^ n,
  (fsum_l2r_rec c a / phi 0 n d = c + \sum_i (a i / phi 0 i d)%Re :> R)%Re.
Proof.
have [d Hd] := fsum_l2r_rec_err_phi c a.
exists d.
rewrite Hd.
rewrite /Rdiv Rmult_plus_distr_r Rmult_comm -Rmult_assoc.
rewrite Rinv_l; [rewrite Rmult_1_l|by apply Rgt_not_eq; apply phi_pos].
rewrite big_distrl /=.
apply /Rplus_eq_compat_l /eq_bigr => i _.
rewrite (Rmult_comm (phi i n d)) (@phi_split fs i 0 n); [|by apply ltnW].
rewrite Rinv_mult_distr; [field; split| |]; apply Rgt_not_eq, phi_pos.
Qed.

Lemma fsum_l2r_rec_err_gamma n (Hn : 2 * INR n * eps fs < 1) c (a : F fs ^ n) :
  exists (t : b_gamma fs n) (ta : b_gamma fs n ^ n),
  (fsum_l2r_rec c a
   = (1 + t) * c + \sum_i ((1 + ta i) * a i)%Re :> R)%Re.
Proof.
have [d Hd] := fsum_l2r_rec_err_phi c a.
have [t Ht] := phi_gamman 0 n Hn d.
set (F := fun i : 'I_n => (phi i n d * a i)%Re).
set (F' := fun (i : 'I_n) (t : b_gamma fs n) => ((1 + t) * a i)%Re).
have HFF' : forall i : 'I_n, exists t : b_gamma fs n, F i = F' i t.
{ move=> i.
  have [t' Ht'] := phi_gamman i n Hn d.
  by exists t'; rewrite /F /F' Ht'. }
have [ta Hta] := big_exists R0 Rplus (b_gamma_0 (bg_2 Hn)) HFF'.
by exists t, ta; rewrite Hd Ht Hta.
Qed.

Lemma fsum_l2r_rec_err'_gamma n (Hn : INR n * eps fs < 1) c (a : F fs ^ n) :
  exists (t : b_gamma fs n) (ta : b_gamma fs n ^ n),
  (fsum_l2r_rec c a * (1 + t)
   = c + \sum_i ((1 + ta i) * a i)%Re :> R)%Re.
Proof.
have [d Hd] := fsum_l2r_rec_err'_phi c a.
have [t Ht] := inv_phi_gamman 0 n Hn d.
set (F := fun i : 'I_n => (a i / phi 0 i d)%Re).
set (F' := fun (i : 'I_n) (t : b_gamma fs n) => ((1 + t) * a i)%Re).
have HFF' : forall i : 'I_n, exists t : b_gamma fs n, F i = F' i t.
{ move=> i.
  have [t' Ht'] := inv_phi_gamman 0 i Hn d.
  by exists t'; rewrite /F /F' /Rdiv Ht' Rmult_comm. }
have [ta Hta] := big_exists R0 Rplus (b_gamma_0 Hn) HFF'.
by exists t, ta; rewrite /Rdiv Ht in Hd; rewrite Hd Hta.
Qed.

Lemma fsum_l2r_rec_err n (Hn : 2 * INR n * eps fs < 1) c (a : F fs ^ n) :
  exists t : b_gamma fs n,
  (fsum_l2r_rec c a = (c + \sum_i (a i : R))
                      + t * (Rabs c + \sum_i (Rabs (a i))) :> R)%Re.
Proof.
have Hn' := bg_2 Hn.
have [t [ta Htta]] := fsum_l2r_rec_err_gamma Hn c a.
have [t' Ht'] := big_bounded_distrl (gamma_pos Hn') ta [ffun i => a i : R].
have [t'' Ht''] := bounded_distrl (gamma_pos Hn') t t' c (\sum_i (Rabs (a i))).
exists t''.
rewrite -(Rabs_pos_eq (\sum_i (Rabs _))); [|by apply big_sum_Rabs_pos].
rewrite -Ht'' -big_Rabs_ffunE -Ht'.
ring_simplify; rewrite Rplus_assoc -big_split /= Htta; apply f_equal2; [ring|].
by apply /eq_bigr => i _; rewrite ffunE; ring_simplify; rewrite Rmult_comm.
Qed.

Lemma fsum_l2r_rec_err' n (Hn : INR n * eps fs < 1) c (a : F fs ^ n) :
  exists (t : b_gamma fs n) (t' : b_gamma fs n),
  (fsum_l2r_rec c a * (1 + t) = (c + \sum_i (a i : R))
                                + t' * (\sum_i (Rabs (a i))) :> R)%Re.
Proof.
have [t [ta Htta]] := fsum_l2r_rec_err'_gamma Hn c a.
have [t' Ht'] := big_bounded_distrl (gamma_pos Hn) ta [ffun i => a i : R].
exists t, t'.
rewrite -big_Rabs_ffunE -Ht' Rplus_assoc -big_split /= Htta.
apply /Rplus_eq_compat_l /eq_bigr => i _.
by rewrite ffunE; ring_simplify; rewrite Rmult_comm.
Qed.

Lemma fsum_l2r_err_gamma n (Hn : 2 * INR n.-1 * eps fs < 1) (a : F fs ^ n) :
  exists ta : b_gamma fs n.-1 ^ n,
  (fsum_l2r a = \sum_i ((1 + ta i) * a i)%Re :> R)%Re.
Proof.
case: n Hn a => [|n] Hn a.
{ by exists ([ffun=> b_gamma_0 (bg_2 Hn)]); rewrite /fsum_l2r !big_ord0. }
set (c := a ord0).
set (a' := [ffun i => a (lift ord0 i)]).
have [t [t' Htt']] := fsum_l2r_rec_err_gamma Hn c a'.
exists [ffun i => if unlift ord0 i is Some j then t' j else t].
rewrite big_ord_recl Htt'; apply f_equal2; [by rewrite ffunE unlift_none|].
by apply /eq_bigr => i _; rewrite /a' !ffunE liftK.
Qed.

Lemma fsum_l2r_err n (Hn : 2 * INR n.-1 * eps fs < 1) (a : F fs ^ n) :
  exists t : b_gamma fs n.-1,
  (fsum_l2r a = (\sum_i (a i : R)) + t * (\sum_i (Rabs (a i))) :> R)%Re.
Proof.
have [ta Hta] := fsum_l2r_err_gamma Hn a.
have [t Ht] := big_bounded_distrl (gamma_pos (bg_2 Hn)) ta [ffun i => a i : R].
exists t.
rewrite -big_Rabs_ffunE -Ht -big_split /= Hta.
by apply eq_bigr => i _; rewrite ffunE; ring_simplify; rewrite Rmult_comm.
Qed.

Lemma fsum_l2r_err_abs n (Hn : 2 * INR n.-1 * eps fs < 1) (a : F fs ^ n) :
  (Rabs (fsum_l2r a - \sum_i (a i : R))
   <= gamma fs n.-1 * \sum_i (Rabs (a i)))%Re.
Proof.
have [t Ht] := fsum_l2r_err Hn a.
rewrite Ht.
replace (_ - _)%Re with (t * \sum_i (Rabs (a i)))%Re by ring.
rewrite Rabs_mult (Rabs_pos_eq (\sum__ _)); [|by apply big_sum_Rabs_pos];
by apply Rmult_le_compat_r; [apply big_sum_Rabs_pos|case t].
Qed.

End Fsum.
