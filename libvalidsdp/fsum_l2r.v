(** * Bounds on the rounding error of summation $\sum_{i=0}^n a_i$#\sum_{i=0}^n x_i# from left to right *)

(** These bounds are a particular case of the ones in [fsum]. *)

Require Import Reals Flocq.Core.Raux.

Require Import misc.

Require Import Psatz.

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop eqtype seq path.

Require Import mathcomp.analysis.Rstruct fsum.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Export float_spec.

Section Fsum_l2r.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).

(** Sum [c + \sum x_i] computed in float from left to right. *)
Fixpoint fsum_l2r_rec n (c : F) : F^n -> F :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (fplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum x_i] computed in float from left to right. *)
Definition fsum_l2r n : F^n -> F :=
  match n with
    | 0%N => fun _ => F0 fs
    | n'.+1 =>
      fun a => fsum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.

Lemma fsum_l2r_rec_r n (c : F) (x : F^n.+1) :
  fsum_l2r_rec c x
  = fplus (fsum_l2r_rec c [ffun i : 'I_n => x (inord i)]) (x ord_max) :> R.
Proof.
elim: n c x => [|n IHn] c x; rewrite /fsum_l2r_rec.
{ by simpl; apply f_equal, f_equal2; [by []|]; apply f_equal, ord_inj. }
rewrite -/fsum_l2r_rec (IHn (fplus _ _) _) ffunE.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ do 2 f_equal; [|apply ffunP=> i]; rewrite !ffunE; apply f_equal.
  { apply Rplus_eq_compat_l; do 2 apply f_equal.
    by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite inordK /=.
  { by apply f_equal2; [by []|apply inordK, (ltn_trans (ltn_ord i))]. }
    apply ltn_trans with i.+2; [by []|].
  rewrite -addn2 -(addn2 n) ltn_add2r; apply ltn_ord. }
by do 2 apply f_equal; apply ord_inj.
Qed.

Lemma fsum_l2r_r n (x : F^n.+1) :
  fsum_l2r x
  = fplus (fsum_l2r [ffun i : 'I_n => x (inord i)]) (x ord_max) :> R.
Proof.
case: n x => [|n] x.
{ by rewrite /fplus /F0 /= Rplus_0_l frnd_F; apply f_equal, f_equal, ord_inj. }
rewrite /fsum_l2r fsum_l2r_rec_r.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ do 2 f_equal; [|apply ffunP=> i]; rewrite !ffunE; apply f_equal.
  { by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite !lift0 inordK.
  { rewrite inordK // -addn2 -(addn2 n) leq_add2r; apply ltnW, ltn_ord. }
  apply ltnW, ltn_ord. }
by rewrite ffunE; do 2 apply f_equal; apply ord_inj.
Qed.

(** Express [fsum_l2r] as [fsum] for a particular evaluation order. *)

Definition iota_finset n m := Build_nat_finset (iota_ltn_sorted n m).

Fixpoint binary_tree_l2r n :=
  match n with
  | 0%N => Leaf 0%N
  | n'.+1 => Node (binary_tree_l2r n') (Leaf n)
  end.

Program Definition order_l2r n : order (iota_finset 0 n.+1) :=
  @Build_order _ (binary_tree_l2r n) _.
Next Obligation.
elim: n => //= n /eqP  ->.
apply /eqP /(eq_sorted_irr ltn_trans ltnn).
{ rewrite -[_ :: _]/(iota 0%N n.+1).
  rewrite ltn_sorted_uniq_leq merge_uniq cat_uniq; apply/andP=> []; split.
  { rewrite iota_uniq Bool.andb_true_r /= Bool.orb_false_r.
    by rewrite -[_ :: _]/(iota 0%N n.+1) mem_iota add0n ltnn. }
  apply (merge_sorted leq_total) => //; apply iota_sorted. }
{ rewrite -[_ :: _]/(iota 0%N n.+2); apply iota_ltn_sorted. }
move=> i; rewrite mem_merge mem_cat mem_seq1.
rewrite -[_ :: _]/(iota 0%N n.+1) -[_ :: _]/(iota 0%N n.+2) !mem_iota !add0n.
case_eq (0 <= i < n.+2)%N.
{ case_eq (i < n.+1)%N => //= H1 H2; apply /eqP /anti_leq /andP; split.
  { by []. }
  by move: H1 => /negbT; rewrite -leqNgt. }
move=> /negbT; rewrite negb_and => /orP []; [by rewrite leq0n|].
rewrite -leqNgt ltn_neqAle => /andP [] Hi1 Hi2.
apply/negbTE; rewrite negb_or negb_and -leqNgt Hi2 Bool.orb_true_r /=.
by apply/eqP; move: Hi1 => /eqP H1 H2; apply H1.
Qed.

Lemma fsum_order_l2r n (a : F^n.+1) : fsum (order_l2r n) a = fsum_l2r a :> R.
Proof.
elim: n a => [|n Hind] a.
{ by rewrite /=; apply /f_equal /f_equal /val_inj => /=; rewrite inordK. }
rewrite fsum_l2r_r.
set a' := [ffun i : 'I_n.+1 => a (inord i)].
set f := fsum_l2r a'; rewrite /= {}/f.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ rewrite -[binary_tree_l2r n]/(order_l2r n : binary_tree).
  rewrite -(@fsum_eq _ _ _ a'); [by apply Hind|].
  move=> i Hi; rewrite /a' ffunE; do 2 apply f_equal.
  by rewrite inordK; [|move: Hi; rewrite mem_iota]. }
by apply /f_equal /f_equal /val_inj => /=; rewrite inordK.
Qed.

Lemma big_seq_l2r n T (x : T^n.+1) (h : T -> R) :
  \sum_(i <- iota_finset 0 n.+1) h (x (inord i)) =
  \sum_(i < n.+1) h (x i).
Proof.
elim: n x => [|n IHn] x.
{ by rewrite big_ord_recl big_cons big_ord0 big_nil inord0E. }
rewrite big_ord_recl big_cons !inord0E -/iota; apply: congr1.
have->: 1%N :: iota 2 n = map (fun n => addn 1 n) (iota_finset 0 n.+1).
{ by rewrite /= -iota_addl. }
rewrite big_map.
have->: \sum_(j <- iota_finset 0 n.+1) h (x (inord (1 + j))) =
        \sum_(i <- iota_finset 0 n.+1) h ([ffun j : 'I_n.+1 => x (inord (1 + j))] (inord i)).
{ rewrite big_seq [in RHS]big_seq.
  apply: eq_bigr => i Hi.
  congr h; rewrite /= ffunE inordK //.
  by rewrite mem_iota in Hi. }
rewrite (IHn [ffun j : 'I_n.+1 => x (inord (1 + j))]).
apply: eq_bigr => i Hi.
rewrite ffunE; congr (h (x _)).
apply: val_inj; rewrite /= inordK //.
by rewrite add1n ltnS.
Qed.

(** Theorem 4.1 in the paper. *)
Theorem fsum_l2r_err n (x : F^n) :
  (Rabs (\sum_i (x i : R) - fsum_l2r x)
   <= INR n.-1 * (eps / (1 + eps)) * \sum_i Rabs (x i))%Re.
Proof.
case: n x => [|n] x.
{ rewrite !big_ord0 Rmult_0_r /= Rminus_diag_eq //; apply: Rabs_le; lra. }
have H := @fsum_err fs n x (iota_finset 0 n.+1) (order_l2r n).
rewrite fsum_order_l2r in H.
rewrite (big_seq_l2r _ (fun t : F => Rabs t)) big_seq_l2r in H.
rewrite [INR n.+1.-1]/=.
rewrite [INR _]/= size_iota in H.
exact: H.
Qed.

(** Theorem 4.2 in the paper (plus underflows). *)
Theorem fsum_l2r_reals_err n (x : R^n) :
  let zeta := ((INR n * eps + INR (2 * n - 1) * eps²) / (1 + eps)²)%Re in
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= zeta * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
case: n x => [|n] x.
{ rewrite !big_ord0 Rmult_0_r /= Rminus_diag_eq //; apply: Rabs_le; lra. }
move: (@fsum_reals_err fs n x (iota_finset 0 n.+1) (order_l2r n)).
rewrite fsum_order_l2r.
rewrite size_iota.
set z := (_ / (1 + eps)²); cbv zeta.
by rewrite (big_seq_l2r _ (fun t => t)) big_seq_l2r.
Qed.

Corollary fsum_l2r_reals_err' n (x : R^n) :
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= INR n * eps * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
case: n x => [|n] x.
{ rewrite !big_ord0 Rmult_0_r /= Rminus_diag_eq //; apply: Rabs_le; lra. }
move: (@fsum_reals_err' fs n x (iota_finset 0 n.+1) (order_l2r n)).
rewrite fsum_order_l2r.
rewrite size_iota.
by rewrite (big_seq_l2r _ (fun t => t)) big_seq_l2r.
Qed.

End Fsum_l2r.
