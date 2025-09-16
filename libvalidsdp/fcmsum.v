(** * Error bounds on $c - \sum_{i=0}^n x_i$#c - \sum_{i=0}^n x_i#
    With $c \in F$#c : F# and $x \in R^n$#x : R^n#. *)

(** Bounds from:
    Siegfried M. Rump, Claude-Pierre Jeannerod:
    Improved Backward Error Bounds for LU and Cholesky Factorizations,
    SIAM J. Matrix Analysis Applications, 35(2):684-698, 2014. *)

From Stdlib Require Import Reals Psatz.
From Flocq Require Import Core.Raux.

Require Import misc.

From mathcomp Require Import ssreflect ssrfun ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop.

From mathcomp Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import fsum_l2r.

Section Fcmsum.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).

(** Sum [c - \sum x_i] computed in float from left to right. *)
Definition fcmsum_l2r n (c : F) (x : R^n) : F :=
  fsum_l2r_rec c [ffun i => fopp (frnd (x i))].

(** Theorem 3.1 in the paper. *)
Theorem fcmsum_l2r_err_no_underflow n (c : F) (x : R^n) (rho : R) (l : nat) :
  (forall i, Rabs (frnd (x i) - x i) <= eps * Rabs (x i)) ->  (** no underflow *)
  Rabs (rho - fcmsum_l2r c x) <= INR l * eps * Rabs rho ->
  let Delta := (rho - (c - \sum_i (x i : R)))%Re in
  Rabs Delta <= INR (n + l) * eps * (Rabs rho + \sum_i Rabs (x i)).
Proof.
elim: n c x => [|n IHn] c x Hnounder Hl Delta.
{ rewrite /Delta !big_ord0 /Rminus Ropp_0 !Rplus_0_r add0n.
  by move: Hl; rewrite /fcmsum_l2r /fsum_l2r_rec. }
set shat := fcmsum_l2r c x in Hl |- *.
set s1 := (c - frnd (x ord0))%Re.
set s1hat := fminus c (frnd (x ord0)).
set delta1 := (Rabs rho + \sum_i Rabs (x (lift ord0 i)))%Re.
set delta2 := Rabs (x ord0).
set Delta1 := (rho - (s1hat - \sum_i (x (lift ord0 i) : R)))%Re.
set Delta2 := (x ord0 - frnd (x ord0))%Re.
have Hshat :
  shat = fcmsum_l2r s1hat [ffun i => x (lift ord0 i)] :> R.
{ rewrite /shat /fcmsum_l2r /= ffunE.
  by do 2 f_equal; apply ffunP=> i; rewrite !ffunE. }
have HDelta_decomp :
  (Rabs Delta <= Rabs Delta1 + Rabs (s1hat - s1) + Rabs Delta2)%Re.
{ apply (Rle_trans _ (Rabs (Delta1 + s1hat - s1 + Delta2))); [right|].
  { f_equal; rewrite /Delta /Delta1 /s1hat /s1 /Delta2.
    rewrite big_ord_recl /GRing.add /=; ring. }
  rewrite /Rminus (Rplus_assoc Delta1).
  apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat_r, Rabs_triang. }
have HDelta1 : (Rabs Delta1 <= INR (n + l) * eps * delta1)%Re.
{ rewrite /Delta1 (eq_bigr (fun i => [ffun i => x (lift ord0 i)] i : R));
    [|by move=> i _; rewrite ffunE].
  set Delta' := (rho - _)%Re.
  rewrite /delta1 (eq_bigr (fun i => Rabs ([ffun i => x (lift ord0 i)] i)));
    [|by move=> i _; rewrite ffunE].
  by apply IHn => [i|]; [rewrite ffunE; apply Hnounder|rewrite -Hshat]. }
have HDelta2 : (Rabs Delta2 <= eps * delta2)%Re.
{ rewrite /Delta2 /delta2 Rabs_minus_sym; apply Hnounder. }
have Herrs1 : (Rabs (s1hat - s1) <= eps * (Rabs Delta1 + delta1))%Re.
{ apply (Rle_trans _ (eps * Rabs s1hat)).
  { move: (fplus_spec_round c (fopp (frnd (x ord0)))) => [] d.
    rewrite /s1hat /s1 /fminus {1}/fopp /= /Rminus => ->; set fp := fplus _ _.
    replace (_ + - _)%Re with (-d * fp)%Re by ring.
    by rewrite Rabs_mult Rabs_Ropp; apply Rmult_le_compat_r;
      [apply Rabs_pos|apply bounded_prop]. }
  apply Rmult_le_compat_l; [by apply eps_pos|].
  replace (s1hat : R) with (rho + (\sum_i x (lift ord0 i)) - Delta1)%Re
    by (rewrite /Delta1; ring).
  rewrite Rabs_minus_sym /delta1.
  apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat_l.
  rewrite Rabs_Ropp.
  apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat_l.
  apply big_Rabs_triang. }
have Herrs1' : (Rabs (s1hat - s1) <= Rabs Delta2 + delta2)%Re.
{ apply (Rle_trans _ (Rabs (frnd (x ord0)))).
  { apply (Rle_trans _ _ _ (fplus_spec_r _ (fopp (frnd (x ord0))))).
    by rewrite Rabs_Ropp; right. }
  replace (frnd _ : R) with (- Delta2 + x ord0)%Re by (rewrite /Delta2; ring).
  by apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat;
    rewrite ?Rabs_Ropp /delta2; right. }
have HDelta : (Rabs Delta <= INR (n + l + 1) * eps * delta1
                             + eps * INR (n + l) * eps * delta1
                             + eps * delta2)%Re.
{ apply (Rle_trans _ _ _ HDelta_decomp), Rplus_le_compat; [|by []].
  apply (Rle_trans _ _ _ (Rplus_le_compat _ _ _ _ HDelta1 Herrs1)).
  rewrite addn1 S_INR !Rmult_plus_distr_r Rmult_1_l Rplus_assoc.
  apply Rplus_le_compat_l; rewrite Rmult_plus_distr_l Rplus_comm !Rmult_assoc.
  by apply Rplus_le_compat_l, Rmult_le_compat_l; [apply eps_pos|lra]. }
have HDelta' :
  (Rabs Delta <= INR (n + l) * eps * delta1 + 2 * eps * delta2 + delta2)%Re.
{ apply (Rle_trans _ _ _ HDelta_decomp).
  by rewrite !Rplus_assoc; apply Rplus_le_compat; [|lra]. }
rewrite addSn S_INR big_ord_recl /GRing.add /= -/delta2.
rewrite (Rplus_comm delta2) -Rplus_assoc -/delta1.
case_eq (n + l)%N => [|npl'] Hnl.
{ apply (Rle_trans _ _ _ HDelta); rewrite Hnl /=; lra. }
case (Rle_or_lt (eps * delta1)%Re delta2) => Hdelta12.
{ apply (Rle_trans _ _ _ HDelta).
  rewrite -Hnl addnS addn0 S_INR (Rmult_comm eps) (Rmult_assoc (_ * _)%Re).
  have H : (0 <= INR (n + l) * eps)%Re.
  { by apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
  rewrite Rmult_plus_distr_l Rplus_assoc; apply Rplus_le_compat_l.
  rewrite !Rmult_plus_distr_r Rmult_1_l; apply Rplus_le_compat_r.
  by apply Rmult_le_compat_l. }
apply (Rle_trans _ _ _ HDelta').
rewrite -Hnl !Rmult_plus_distr_r Rmult_1_l Rmult_plus_distr_l 3!Rplus_assoc.
apply Rplus_le_compat_l, Rplus_le_compat; [|lra].
rewrite -(Rmult_1_l (_ * _)%Re) Rmult_assoc; apply Rmult_le_compat_r.
{ apply Rmult_le_pos; [apply eps_pos|apply Rabs_pos]. }
rewrite Hnl S_INR; move: (pos_INR npl'); lra.
Qed.

Lemma fcmsum_l2r_err_aux n (c : F) (x : R^n) (rho : R) (l : nat) :
  Rabs (rho - fcmsum_l2r c x) <= INR l * eps * Rabs rho ->
  let Delta := (rho - (c - \sum_i (x i : R)))%Re in
  Rabs Delta <= INR (n + l) * eps * (Rabs rho + \sum_i Rabs (x i))
                + (1 + INR (n + l) * eps) * (INR n * eta).
Proof.
move=> Hl Delta.
have [x' Hx'] := ffun_exists (fun i => frnd_spec_separate fs (x i)).
apply (Rle_trans _ (Rabs (rho - (c - \sum_i (x' i : R)))
                    + \sum_i Rabs (x i - x' i))).
{ have -> : Rabs Delta = Rabs (rho - (c - \sum_i (x' i + (x i - x' i)))).
  { rewrite /Delta; do 3 f_equal; apply eq_bigr => i _.
    rewrite /GRing.add /GRing.opp /=; lra. }
  rewrite big_split /=.
  replace (rho - _)%Re with (rho - (c - \sum_i x' i) + \sum_i (x i - x' i))%Re;
    [|rewrite /GRing.add /=; ring].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat_l.
  apply big_Rabs_triang. }
have HDelta' := @fcmsum_l2r_err_no_underflow n c x' rho l.
set dxx' := \sum__ Rabs _.
have Hdxx' : dxx' <= INR n * eta.
{ rewrite /dxx' -big_sum_const; apply Rle_big_compat => i.
  have [e He] := proj1 (proj2 (Hx' i)); rewrite He.
  move: (bounded_prop e); apply Rle_trans; right.
  rewrite -Rabs_Ropp; f_equal; ring. }
apply (Rle_trans _ (INR (n + l) * eps * (Rabs rho + \big[+%R/0]_i Rabs (x' i))
                    + dxx')).
{ apply Rplus_le_compat_r, fcmsum_l2r_err_no_underflow.
  { move=> i; have [d Hd] := proj2 (proj2 (Hx' i)); rewrite Hd.
    replace (_ - _)%Re with (d * x' i)%Re by ring.
    rewrite Rabs_mult; apply Rmult_le_compat_r; [apply Rabs_pos|].
    by apply (Rle_trans _ _ _ (bounded_prop _)), epsd1peps_le_eps, eps_pos. }
  move: Hl; apply Rle_trans; right; do 2 f_equal.
  rewrite /fcmsum_l2r; do 2 f_equal; apply ffunP=> i; rewrite !ffunE.
  f_equal; apply Hx'. }
rewrite (Rplus_comm 1) (Rmult_plus_distr_r _ 1) Rmult_1_l -Rplus_assoc.
apply Rplus_le_compat; [|exact Hdxx'].
rewrite -Rmult_plus_distr_l; apply Rmult_le_compat_l.
{ by apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
rewrite Rplus_assoc; apply Rplus_le_compat_l.
apply (Rle_trans _ (\sum_i Rabs (x i) + dxx')); [|by apply Rplus_le_compat_l].
rewrite /dxx' -big_split; apply Rle_big_compat => i /=.
have {1}->: x' i = (x i + (x' i - x i))%Re;
  [by rewrite Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r|].
rewrite Rabs_minus_sym.
apply Rabs_triang.
Qed.

Corollary fcmsum_l2r_err n (c : F) (x : R^n) (rho alpha : R) (l : nat) :
  0 <= alpha ->
  Rabs (rho - fcmsum_l2r c x) <= Rmax (INR l * eps * Rabs rho) alpha ->
  let Delta := (rho - (c - \sum_i (x i : R)))%Re in
  Rabs Delta <= INR (n + l) * eps * (Rabs rho + \sum_i Rabs (x i))
                + (1 + INR (n + l) * eps) * (INR n * eta + alpha).
Proof.
move=> Halpha Hl Delta.
case (Rle_or_lt alpha (INR l * eps * Rabs rho)) => Hmax.
{ apply (Rle_trans _ (INR (n + l) * eps * (Rabs rho + \big[+%R/0]_i Rabs (x i))
                      + (1 + INR (n + l) * eps) * (INR n * eta))).
  { apply fcmsum_l2r_err_aux, (Rle_trans _ _ _ Hl).
    by rewrite Rmax_left; [right|]. }
  apply Rplus_le_compat_l, Rmult_le_compat_l.
  { apply Rplus_le_le_0_compat; [lra|].
    apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
  by rewrite -{1}(Rplus_0_r (_ * _)); apply Rplus_le_compat_l. }
set shat := fcmsum_l2r c x.
apply (Rle_trans _ (Rabs (rho - shat) + Rabs (shat - (c - \sum_i x i)))).
{ by have ->: Delta = ((rho - shat) + (shat - (c - \sum_i x i)))%Re;
    [rewrite /Delta; ring|apply Rabs_triang]. }
have Hrhomshat : Rabs (rho - shat) <= alpha.
{ by apply (Rle_trans _ _ _ Hl); rewrite Rmax_right; [right|apply Rlt_le]. }
apply (Rle_trans _ (alpha + (INR (n + l) * eps * (Rabs shat + \sum_i Rabs (x i))
                             + (1 + INR (n + l) * eps) * (INR n * eta)))).
{ apply (Rplus_le_compat _ _ _ _ Hrhomshat), fcmsum_l2r_err_aux.
  rewrite {1}/shat Rcomplements.Rminus_eq_0 Rabs_R0.
  apply Rmult_le_pos; [|by apply Rabs_pos].
  by apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
apply (Rle_trans _ (alpha + (INR (n + l) * eps
                             * (Rabs rho + alpha + \sum_i Rabs (x i))
                             + (1 + INR (n + l) * eps) * (INR n * eta)))).
{ apply Rplus_le_compat_l, Rplus_le_compat_r, Rmult_le_compat_l.
  { apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
  apply Rplus_le_compat_r.
  have ->: shat = (rho + (shat - rho))%Re :> R; [ring|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)), Rplus_le_compat_l.
  by rewrite Rabs_minus_sym. }
right; ring.
Qed.

End Fcmsum.
