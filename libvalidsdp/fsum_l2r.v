(** * Bounds on the rounding error of summation $\sum_{i=0}^n a_i$#\sum_{i=0}^n x_i# from left to right *)

(** These bounds are a particular case of the ones in [fsum]. *)

Require Import Reals Flocq.Core.Raux.

Require Import misc.

Require Import Psatz.

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop eqtype seq path.

Require Import Rstruct fsum.

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

(* TODO: base proofs of following theorems on the ones in fsum.v *)

(** Theorem 4.1 in the paper. *)
Theorem fsum_l2r_err n (x : F^n) :
  (Rabs (\sum_i (x i : R) - fsum_l2r x)
   <= INR n.-1 * eps / (1 + eps) * \sum_i Rabs (x i))%Re.
Proof.
elim: n x => [|n IHn] x.
{ rewrite !big_ord0 Rmult_0_r /fsum_l2r /Rminus Rplus_0_l Rabs_Ropp Rabs_R0.
  by right. }
case: n IHn x => [|n] IHn x.
{ rewrite big_ord_recl big_ord0 GRing.addr0 /fsum_l2r /= /Rdiv !Rmult_0_l.
  by rewrite Rminus_diag_eq // Rabs_R0; right. }
set s := \sum_i (x i : R).
set shat := fsum_l2r x.
set s1hat := fsum_l2r [ffun i : 'I_n.+1 => x (inord i)].
set s2hat := x ord_max.
set delta := s1hat + s2hat - fplus s1hat s2hat.
set s1 := \sum_(i < n.+1) (x (inord i) : R).
set delta1 := s1 - s1hat.
apply (Rle_trans _ (Rabs (delta + delta1))).
{ right; f_equal.
  rewrite /s /shat fsum_l2r_r -/s1hat big_ord_recr /= /GRing.add /= -/s2hat.
  rewrite /delta /delta1.
  apply (Rplus_eq_reg_r (fplus s1hat s2hat - s2hat)); ring_simplify.
  by apply eq_bigr => i _; do 2 f_equal; apply ord_inj; rewrite inordK /=;
    [|apply (ltn_trans (ltn_ord i))]. }
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
set s1t := \sum_(i < n.+1) Rabs (x (inord i)).
set s2t := Rabs (x ord_max).
have Hdelta1 : Rabs delta1 <= INR n * eps / (1 + eps) * s1t.
{ rewrite /delta1.
  have->: s1 = \sum_i ([ffun i : 'I_n.+1 => x (inord i)] i : R).
  { by apply eq_bigr=> i _; rewrite ffunE. }
  apply (Rle_trans _ _ _ (IHn _)).
  by right; f_equal; apply eq_bigr=> i _; rewrite ffunE. }
have Hs1hat : Rabs s1hat <= Rabs delta1 + s1t.
{ have->: (s1hat = s1hat - s1 + s1 :> R)%Re; [ring|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite Rabs_minus_sym; apply Rplus_le_compat_l, big_Rabs_triang. }
apply (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ Hdelta1)).
apply (Rplus_le_reg_r (- (INR n * eps / (1 + eps) * s1t))); ring_simplify.
apply (Rle_trans _ (eps / (1 + eps) * (s1t + INR n.+1 * s2t))); last first.
{ right; rewrite !Ropp_mult_distr_l !Rmult_assoc.
  rewrite (Rmult_comm (- _)) (Rmult_comm (INR n.+2.-1)) !Rmult_assoc.
  rewrite -!Rmult_plus_distr_l; do 2 f_equal.
  rewrite Nat.pred_succ S_INR big_ord_recr /= /GRing.add /=.
  replace (\sum_(i < n.+1) Rabs _) with s1t; last first.
  { by apply eq_bigr=> i _; do 3 f_equal; apply ord_inj; rewrite inordK;
      [|apply (ltn_trans (ltn_ord i))]. }
  have->:Rabs (x ord_max) = s2t; [|ring].
  by rewrite /s2t; do 3 f_equal; apply ord_inj; rewrite inordK. }
destruct (Rle_or_lt s2t (eps / (1 + eps) * s1t)) as [Hs12t|Hs12t].
{ apply (Rle_trans _ s2t).
  { rewrite /delta /s2t Rabs_minus_sym; apply fplus_spec_r. }
  apply (Rle_trans _ _ _ Hs12t).
  apply (Rplus_le_reg_r (- (eps / (1 + eps) * s1t))); ring_simplify.
  apply Rmult_le_pos; [|by apply Rabs_pos].
  apply Rmult_le_pos; [apply epsd1peps_pos, eps_pos|apply pos_INR]. }
destruct (Rle_or_lt s1t (eps / (1 + eps) * s2t)) as [Hs21t|Hs21t].
{ apply (Rle_trans _ (Rabs s1hat)).
  { rewrite /delta Rabs_minus_sym; apply fplus_spec_l. }
  apply (Rle_trans _ _ _ Hs1hat).
  apply (Rle_trans _ _ _ (Rplus_le_compat _ _ _ _ Hdelta1 Hs21t)).  
  rewrite S_INR; apply (Rplus_le_reg_r (- (eps / (1 + eps) * s2t))); ring_simplify.
  rewrite -(Rplus_0_l (_ * _)); apply Rplus_le_compat.
  { apply Rmult_le_pos; [apply big_sum_Rabs_pos|apply epsd1peps_pos, eps_pos]. }
  rewrite (Rmult_comm _ (INR _)) -!Rmult_assoc; apply Rmult_le_compat_l.
  { rewrite Rmult_assoc; apply Rmult_le_pos; [apply pos_INR|].
    apply epsd1peps_pos, eps_pos. }
  apply (Rle_trans _ _ _ Hs21t).
  rewrite -{2}(Rmult_1_l s2t); apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply (Rle_trans _ _ _ (epsd1peps_le_eps (eps_pos fs))), Rlt_le, eps_lt_1. }
apply (Rle_trans _ (eps / (1 + eps) * Rabs (s1hat + s2hat))).
{ have [d Hd] := fplus_spec s1hat s2hat.
  rewrite /delta Hd.
  replace (_ - _)%Re with (-d * (s1hat + s2hat))%Re; [|ring].
  rewrite Rabs_mult Rabs_Ropp; apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply bounded_prop. }
apply Rmult_le_compat_l; [by apply epsd1peps_pos, eps_pos|].
apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite -/s2t.
rewrite S_INR; apply (Rplus_le_reg_r (- s2t)); ring_simplify.
apply (Rle_trans _ _ _ Hs1hat).
apply (Rplus_le_reg_r (- s1t)); ring_simplify.
apply (Rle_trans _ _ _ Hdelta1).
rewrite (Rmult_comm _ (INR n)) !Rmult_assoc.
apply Rmult_le_compat_l; [apply pos_INR|].
by rewrite -!Rmult_assoc; apply Rlt_le.
Qed.

(** Theorem 4.2 in the paper (plus underflows). *)
Theorem fsum_l2r_reals_err n (x : R^n) :
  let zeta := ((INR n * eps + INR (2 * n - 1) * eps²) / (1 + eps)²)%Re in
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= zeta * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
have Peps := eps_pos fs.
case: n x => [|n] x.
{ rewrite !big_ord0 /fsum_l2r /F0 /= !Rmult_0_r Rmult_0_l /Rminus !Rplus_0_l.
  by rewrite Rabs_Ropp Rabs_R0; right. }
move=> zeta.
set rx := [ffun _ => _].
replace (_ - _)%Re
  with (\sum_i (rx i : R) - fsum_l2r rx + (\sum_i x i - \sum_i (rx i : R)))%Re;
  [|ring].
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ (fsum_l2r_err rx))).
set INRnp1 := INR n.+1.
rewrite Nat.pred_succ /Rminus big_sum_Ropp -big_split /=.
apply (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ (big_Rabs_triang _ _))).
have H : \sum_i Rabs (rx i) <= \sum_i Rabs (x i) + \sum_i Rabs (x i - rx i).
{ rewrite -big_split; apply Rle_big_compat=> i /=.
  have{1}->: (rx i = x i + (rx i - x i) :> R); [ring|].
  by apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_minus_sym; right. }
have H' : \sum_i Rabs (x i - rx i)
          <= eps / (1 + eps) * (\sum_i Rabs (x i)) + INR n.+1 * eta.
{ apply (Rle_trans _ (\sum_i (eps / (1 + eps) * Rabs (x i) + eta)%Re)).
  { apply Rle_big_compat=> i.
    have [d [e [Hde _]]] := frnd_spec fs (x i).
    rewrite Rabs_minus_sym /rx ffunE Hde.
    replace (_ - _)%Re with (d * x i + e)%Re; [|ring].
    apply (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_mult.
    apply Rplus_le_compat; [apply Rmult_le_compat_r; [apply Rabs_pos|]|];
      apply bounded_prop. }
  by rewrite big_split /= /GRing.add /= -big_distrr /= big_sum_const; right. }
have H'' : \sum_i Rabs (rx i)
           <= (1 + eps / (1 + eps)) * (\sum_i Rabs (x i)) + INR n.+1 * eta.
{ rewrite Rmult_plus_distr_r Rmult_1_l Rplus_assoc.
  by apply (Rle_trans _ _ _ H), Rplus_le_compat_l. }
apply (Rle_trans _ ((INR n * eps / (1 + eps) * (1 + eps / (1 + eps))
                     + eps / (1 + eps))
                    * (\sum_i Rabs (x i))
                    + (INR n * eps / (1 + eps) + 1) * INR n.+1 * eta)).
{
  rewrite !Rmult_plus_distr_r Rmult_1_l.
  rewrite -Rplus_assoc (Rplus_comm _ (_ * _ * eta)) -Rplus_assoc Rplus_assoc.
  apply Rplus_le_compat; [|apply H'].
  rewrite (Rplus_comm (_ * _ * eta)) 2!Rmult_assoc -Rmult_plus_distr_l.
  apply Rmult_le_compat_l; [|apply H''].
  rewrite /Rdiv Rmult_assoc; apply Rmult_le_pos; [apply pos_INR|].
  by apply epsd1peps_pos. }
apply Rplus_le_compat.
{ apply Rmult_le_compat_r; [apply big_sum_Rabs_pos|].
  apply (Rmult_le_reg_r (1 + eps)²); [apply Rlt_0_sqr; lra|].
  rewrite /zeta /Rsqr; field_simplify; [|lra|lra].
  rewrite /Rdiv Rinv_1 !Rmult_1_r.
  rewrite mul2n doubleS subn1 Nat.pred_succ !S_INR -mul2n mult_INR /=.
  right; ring. }
apply Rmult_le_compat_r; [apply eta_pos|].
apply Rmult_le_compat_r; [apply pos_INR|].
rewrite Rplus_comm /Rdiv Rmult_assoc; apply Rplus_le_compat_l, Rmult_le_compat.
{ apply pos_INR. }
{ by apply epsd1peps_pos. }
{ by apply /le_INR /leP. }
by apply epsd1peps_le_eps.
Qed.  

Corollary fsum_l2r_reals_err' n (x : R^n) :
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= INR n * eps * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
have Peps := eps_pos fs.
move: (fsum_l2r_reals_err x) => /= H.
apply (Rle_trans _ _ _ H), Rplus_le_compat_r.
apply Rmult_le_compat_r; [apply big_sum_Rabs_pos|].
apply (Rmult_le_reg_r (1 + eps)²); [apply Rlt_0_sqr; lra|].
rewrite /Rsqr; field_simplify; [rewrite /Rdiv Rinv_1 !Rmult_1_r|lra].
apply (Rplus_le_reg_r (- (INR n * eps))); ring_simplify.
rewrite -(Rplus_0_l (_ ^ 2 * _)); apply Rplus_le_compat.
{ apply Rmult_le_pos; [apply pos_INR|apply pow_le, eps_pos]. }
rewrite Rmult_comm; apply Rmult_le_compat_r; [apply pow2_ge_0|].
by rewrite -[2]/(INR 2) -mult_INR; apply /le_INR /leP; rewrite multE leq_subr.
Qed.

End Fsum_l2r.
