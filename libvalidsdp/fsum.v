(** * Bounds on the rounding error of summation $\sum_{i=0}^n x_i$#\sum_{i=0}^n x_i# in any order *)

(** Improved bounds from:
    Claude-Pierre Jeannerod, Siegfried M. Rump:
    On relative errors of floating-point operations: Optimal bounds and applications,
    Math. Comput., 87(310):803-819, 2018. *)

Require Import Reals Flocq.Core.Raux.

Require Import misc.

Require Import Psatz.

From Coquelicot Require Import Rcomplements.

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop eqtype seq path.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Export float_spec.

Import GRing.Theory.

Lemma inord0E n : inord 0 = ord0 :> 'I_n.+1.
Proof. by apply: ord_inj; rewrite inordK. Qed.

Section order.

Record nat_finset := {
  nat_finset_seq :> seq nat ;
  _ : sorted ltn nat_finset_seq
}.

Canonical nat_finset_subType := [subType for nat_finset_seq].
(* Definition nat_finset_eqMixin := Eval hnf in [eqMixin of nat_finset by <:]. *)
(* Canonical nat_finset_eqType := Eval hnf in EqType nat_finset nat_finset_eqMixin. *)

Definition disjoint (s1 s2 : nat_finset) := uniq (s1 ++ s2).

Program Definition nat_finset_disjoint_merge s1 s2 (H : disjoint s1 s2) :=
  @Build_nat_finset (merge leq s1 s2) _.
Next Obligation.
move: H; rewrite ltn_sorted_uniq_leq merge_uniq /disjoint => -> /=.
apply (merge_sorted leq_total).
{ by move: s1 => [] s1 /=; rewrite ltn_sorted_uniq_leq=> /andP []. }
by move: s2 => [] s2 /=; rewrite ltn_sorted_uniq_leq=> /andP [].
Qed.

Lemma size_nat_finset_disjoint_merge s1 s2 (H : disjoint s1 s2) :
  (size (nat_finset_disjoint_merge H) = size s1 + size s2)%N.
Proof. by rewrite size_merge size_cat. Qed.

Inductive binary_tree :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

Fixpoint leaves b :=
  match b with
  | Leaf n => [:: n]
  | Node l r => merge leq (leaves l) (leaves r)
  end.

Lemma leaves_sorted t : sorted leq (leaves t).
Proof. by elim: t => //= l Hl r Hr; apply (merge_sorted leq_total). Qed.

Section OrderRecord.

Variable s : nat_finset.

Record order := {
  order_tree :> binary_tree ;
  _ : leaves order_tree == s
}.

Canonical order_subType := [subType for order_tree].

End OrderRecord.

Program Definition order_leaf n : order (@Build_nat_finset [:: n] _) :=
  @Build_order _ (Leaf n) _.

Program Definition order_node sl sr (H : disjoint sl sr)
        (l : order sl) (r : order sr) : order (nat_finset_disjoint_merge H) :=
  @Build_order _ (Node l r) _.
Next Obligation. by move: l r => [] l /= /eqP -> [] r /= /eqP ->. Qed.

Theorem order_ind (P : forall s, order s -> Prop) :
  (forall i, P _ (order_leaf i)) ->
  (forall sl sr (H : disjoint sl sr) (l : order sl) (r : order sr),
      P _ l -> P _ r -> P _ (order_node H l r)) ->
  forall s (o : order s), P _ o.
Proof.
move=> H0 Hind s [] t.
elim: t s=> [i s Hi|l Hl r Hr s Hlr].
{ move: (H0 i).
  set s' := Build_nat_finset _.
  have Hs' : s' = s.
  { by apply val_inj; move: Hi => /eqP /= <-. }
  move: Hi; rewrite -Hs' => Hi.
  have -> : order_leaf i = Build_order Hi; [|by []].
  by apply val_inj. }
have Hus : uniq s.
{ by move: s {Hlr} => [] s /=; rewrite ltn_sorted_uniq_leq=> /andP []. }
have Hsl : sorted ltn (leaves l).
{ rewrite ltn_sorted_uniq_leq leaves_sorted Bool.andb_true_r.
  by move: Hlr Hus=> /eqP <-; rewrite merge_uniq cat_uniq; move/andP=> []. }
have Hsr : sorted ltn (leaves r).
{ rewrite ltn_sorted_uniq_leq leaves_sorted Bool.andb_true_r.
  move: Hlr Hus=> /eqP <-.
  by rewrite merge_uniq cat_uniq; move/andP=> [] _ /andP [] _. }
set sl := Build_nat_finset Hsl.
set sr := Build_nat_finset Hsr.
have Hdisj : disjoint sl sr.
{ by move: Hlr Hus => /eqP <- /=; rewrite merge_uniq. }
set ol := @Build_order sl l (eq_refl _).
set or := @Build_order sr r (eq_refl _).
move: (Hind sl sr Hdisj ol or (Hl sl (eq_refl _)) (Hr sr (eq_refl _))).
have Hs : nat_finset_disjoint_merge Hdisj = s.
{ by apply val_inj; move: Hlr => /eqP. }
move: Hlr; rewrite -Hs => Hlr.
by have -> : order_node Hdisj ol or = Build_order Hlr; [apply val_inj|].
Qed.

Lemma size_order (sn : nat_finset) (o : order sn) : (0 < size sn)%N.
Proof.
elim: o =>// sl sr ? ?? Hsl ?.
by rewrite size_nat_finset_disjoint_merge addn_gt0 Hsl.
Qed.

End order.

Section Fsum.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).

(** Sum [\sum x_i] computed in float according to a given evaluation [order]. *)
Fixpoint fsum n (order : binary_tree) (x : F^n.+1) : F :=
  match order with
  | Leaf i => x (inord i)
  | Node l r => fplus (fsum l x) (fsum r x)
  end.

Lemma fsum_eq n1 n2 (x1 : F^n1.+1) (x2 : F^n2.+1) s (o : order s) :
  (forall i, i \in (s : seq nat) -> x1 (inord i) = x2 (inord i) :> R) ->
  fsum o x1 = fsum o x2 :> R.
Proof.
elim/order_ind: o n1 n2 x1 x2 => [i|sl sr Hslr l r IHl IHr] n1 n2 x1 x2 Hx12 /=.
{ by apply Hx12; rewrite inE. }
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ by apply IHl => i Hi; apply Hx12; rewrite mem_merge mem_cat Hi. }
by apply IHr => i Hi; apply Hx12; rewrite mem_merge mem_cat Hi orbC.
Qed.

Lemma size_leaves t : (0 < size (leaves t))%N.
Proof.
elim: t =>[//=| t1 IHt1 t2 IHt2]; rewrite size_merge size_cat.
by rewrite addn_gt0 IHt1.
Qed.

Lemma size_merge_leq_leaves t1 t2 :
  (1 < size (merge leq (leaves t1) (leaves t2)))%N.
Proof.
rewrite size_merge size_cat.
have H1 := size_leaves t1.
have H2 := size_leaves t2.
rewrite -addn1.
exact: leq_add.
Qed.

Ltac fold_eps1 :=
  rewrite ?[INR _ * _ / _]Rmult_assoc ?[(INR _ + INR _) * _ / _]Rmult_assoc;
  fold (Rdiv eps (1 + eps)); set eps1 := (Rdiv eps (1 + eps)).

(** Theorem 4.1 in the paper. *)
Theorem fsum_err m (x : F^m.+1) (sn : nat_finset) (o : order sn) :
  (Rabs (\sum_(i <- sn) (x (inord i) : R) - fsum o x)
   <= INR (size sn).-1 * (eps / (1 + eps)) * \sum_(i <- sn) Rabs (x (inord i)))%Re.
Proof.
(* The discussion "n = 1" / "n >= 2" followed in the paper is unneeded
   as we can directly reason by structural induction: *)
elim/order_ind: o m x.
(* Leaf case *)
{ move=> i n x.
  rewrite !big_seq1 /= /Rminus Rplus_opp_r Rabs_R0.
  have Habs := Rabs_pos (x (inord i)).
  have Heps := eps_pos fs.
  have Heps1 := Rplus_lt_le_0_compat _ _ Rlt_0_1 Heps.
  apply: Rmult_le_pos =>//.
  by rewrite Rmult_0_l; apply: Req_le. }
(* Node case *)
move=> sl sr Hslr l r IHl IHr n x /=.
set s := \sum_i (x i : R).
set s1hat := fsum l x.
set s2hat := fsum r x.
set delta := s1hat + s2hat - fplus s1hat s2hat.
set s1 := \sum_(i <- sl) (x (inord i) : R).
set s2 := \sum_(i <- sr) (x (inord i) : R).
set delta1 := s1 - s1hat.
set delta2 := s2 - s2hat.
apply (Rle_trans _ (Rabs (delta + (delta1 + delta2)))).
{ right; f_equal.
  rewrite /s /delta /delta1 /delta2 /s1hat /s2hat /s1 /s2.
  apply (Rplus_eq_reg_r (fplus (fsum l x) (fsum r x))); ring_simplify.
  by rewrite -big_cat; apply: eq_big_perm; rewrite perm_merge. }
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
apply (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ (Rabs_triang _ _))).
set s1t := \sum_(i <- sl) Rabs (x (inord i)).
set s2t := \sum_(i <- sr) Rabs (x (inord i)).
rewrite size_merge size_cat.
set n1 := size sl.
set n2 := size sr.
have Hdelta1 : Rabs delta1 <= INR n1.-1 * (eps / (1 + eps)) * s1t by exact: IHl.
have Hdelta2 : Rabs delta2 <= INR n2.-1 * (eps / (1 + eps)) * s2t by exact: IHr.
have Hs1hat : Rabs s1hat <= Rabs delta1 + s1t.
{ have->: (s1hat = s1hat - s1 + s1 :> R)%Re; [ring|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite Rabs_minus_sym /delta1 /s1 /s1t; apply: Rplus_le_compat_l.
  exact: big_Rabs_triang. }
have Hs2hat : Rabs s2hat <= Rabs delta2 + s2t.
{ have->: (s2hat = s2hat - s2 + s2 :> R)%Re; [ring|].
  apply (Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite Rabs_minus_sym /delta1 /s2 /s2t; apply: Rplus_le_compat_l.
  exact: big_Rabs_triang. }
have Hdelta12 := Rplus_le_compat _ _ _ _ Hdelta1 Hdelta2.
apply (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ Hdelta12)).
have n1_pos : (0 < size sl)%N by case: (l) => o /eqP<-; rewrite size_leaves.
have n2_pos : (0 < size sr)%N by case: (r) => o /eqP<-; rewrite size_leaves.
have n1n2_pos : (0 < size sl + size sr)%N by rewrite addn_gt0 n1_pos.
suff B1: Rabs delta <= eps / (1 + eps) * (INR n1 * s2t + INR n2 * s1t).
{ apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ B1)).
  have->: \sum_(i <- merge leq sl sr) Rabs (x (inord i)) = s1t + s2t.
    by rewrite -big_cat; apply: eq_big_perm; rewrite perm_merge.
  fold_eps1; rewrite -!subn1 !minus_INR ?plus_INR; first 1 [idtac] || exact/ltP.
  apply: Req_le; ring. }

have s1t_pos : 0 <= s1t by exact: big_sum_Rabs_pos.
have s2t_pos : 0 <= s2t by exact: big_sum_Rabs_pos.

have [Hs21t|Hs21t] := Rle_or_lt s2t (eps / (1 + eps) * s1t).

(* Hs21t : s2t <= eps / (1 + eps) * s1t *)
{ have Hs21t': s2t <= s1t.
  { apply (Rle_trans _ _ _ Hs21t).
    apply (Rle_trans _ (1 * s1t)).
    apply Rmult_le_compat_r =>//.
    apply (Rle_trans _ eps).
    { exact: epsd1peps_le_eps (eps_pos fs). }
    { exact: Rlt_le _ _ (eps_lt_1 fs). }
    by rewrite Rmult_1_l; exact: Req_le. }
  rewrite /delta Rabs_minus_sym.
  apply: (Rle_trans _ _ _ (fplus_spec_r _ _)).
  apply: (Rle_trans _ _ _ Hs2hat).
  apply: (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hdelta2)).
  apply: (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ Hs21t)).
  fold_eps1.
  apply (Rle_trans _ (INR n2 * eps1 * s1t)).
  { have Heps := epsd1peps_pos  (eps_pos fs).
    fold eps1 in Heps.
    have Hn2 := pos_INR n2.-1.
    fold eps1 in Hs21t.
    ring_simplify.
    have Hn2e : 0 <= INR n2.-1 * eps1.
    { exact: Rmult_le_pos. }
    apply: (Rle_trans _ (INR n2.-1 * eps1 * s1t + eps1 * s1t)).
    { apply: Rplus_le_compat_r =>//.
      exact: Rmult_le_compat_l. }
    rewrite -subn1 minus_INR ?[INR 1]/=; first lra.
    exact/leP. }
  { ring_simplify.
    rewrite -[X in X <= _]Rplus_0_r.
    apply: Rplus_le_compat_l.
    do 2![apply: Rmult_le_pos =>//].
    { rewrite /eps1; apply: epsd1peps_pos; exact: eps_pos. }
    { exact: pos_INR. } } }

(* Hs21t : eps / (1 + eps) * s1t < s2t *)

have [Hs12t|Hs12t] := Rle_or_lt s1t (eps / (1 + eps) * s2t).

(* Hs12t : s1t <= eps / (1 + eps) * s2t *)

{ have Hs12t': s1t <= s2t.
  { apply (Rle_trans _ _ _ Hs12t).
    apply (Rle_trans _ (1 * s2t)).
    apply Rmult_le_compat_r =>//.
    apply (Rle_trans _ eps).
    { exact: epsd1peps_le_eps (eps_pos fs). }
    { exact: Rlt_le _ _ (eps_lt_1 fs). }
    by rewrite Rmult_1_l; exact: Req_le. }
  rewrite /delta Rabs_minus_sym.
  apply: (Rle_trans _ _ _ (fplus_spec_l _ _)).
  apply: (Rle_trans _ _ _ Hs1hat).
  apply: (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hdelta1)).
  apply: (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ Hs12t)).
  fold_eps1.
  apply (Rle_trans _ (INR n1 * eps1 * s2t)).
  { have Heps := epsd1peps_pos  (eps_pos fs).
    fold eps1 in Heps.
    have Hn2 := pos_INR n1.-1.
    fold eps1 in Hs12t.
    ring_simplify.
    have Hn2e : 0 <= INR n1.-1 * eps1.
    { exact: Rmult_le_pos. }
    apply: (Rle_trans _ (INR n1.-1 * eps1 * s2t + eps1 * s2t)).
    { apply: Rplus_le_compat_r =>//.
      exact: Rmult_le_compat_l. }
    rewrite -subn1 minus_INR ?[INR 1]/=; first lra.
    exact/leP. }
  { ring_simplify.
    rewrite -[X in X <= _]Rplus_0_r.
    apply: Rplus_le_compat_l.
    do 2![apply: Rmult_le_pos =>//].
    { rewrite /eps1; apply: epsd1peps_pos; exact: eps_pos. }
    { exact: pos_INR. } } }

(* Hs12t : eps / (1 + eps) * s2t < s1t *)

rewrite /delta Rabs_minus_sym.
have [[d Hd] ->] := fplus_spec s1hat s2hat.
rewrite [X in X <= _]/=.
rewrite (_: ?[a] - ?[b] = d * ?b); last ring.
rewrite Rabs_mult.
apply: (Rle_trans _ (eps / (1 + eps) * Rabs (s1hat + s2hat))).
apply: Rmult_le_compat_r; [exact: Rabs_pos|done].
apply: Rmult_le_compat_l; first apply epsd1peps_pos, eps_pos.
have Tri: Rabs (s1hat + s2hat) <= Rabs (s1hat - s1) + s1t + (Rabs (s2hat - s2) + s2t).
{ have->: s1hat + s2hat = (s1hat - s1 + s1) + (s2hat - s2 + s2) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply: Rplus_le_compat.
  { apply Rle_trans with (1 := Rabs_triang _ _).
    apply: Rplus_le_compat_l.
    exact: big_Rabs_triang. }
  { apply Rle_trans with (1 := Rabs_triang _ _).
    apply: Rplus_le_compat_l.
    exact: big_Rabs_triang. } }

apply/(Rle_trans _ _ _ Tri).
rewrite Rabs_minus_sym -[_ - _]/delta1.
rewrite Rabs_minus_sym -[_ - _]/delta2.
rewrite (_: ?[d1] + s1t + (?[d2] + s2t) = ?d1 + s2t + (?d2 + s1t)); last ring.
apply: Rplus_le_compat.
{ apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hdelta1)).
  have Ha := Rmult_le_compat_l _ _ _ (pos_INR n1.-1) (Rlt_le _ _ Hs21t).
  apply (Rle_trans _ (INR n1.-1 * s2t + s2t)).
  { apply Rplus_le_compat_r =>//; lra. }
  { rewrite -[n1 in X in _ <= X]prednK // -addn1 plus_INR [INR 1]/=; lra. } }
{ apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hdelta2)).
  have Ha := Rmult_le_compat_l _ _ _ (pos_INR n2.-1) (Rlt_le _ _ Hs12t).
  apply (Rle_trans _ (INR n2.-1 * s1t + s1t)).
  { apply Rplus_le_compat_r =>//; lra. }
  { rewrite -[n2 in X in _ <= X]prednK // -addn1 plus_INR [INR 1]/=; lra. } }
Qed.

(** Theorem 4.2 in the paper (plus underflows).

Note that the type of [x] is [R^_] (not [F^_]), so the theorem can be
applied to scalar products, beyond mere sums of floating-point numbers.
*)
Theorem fsum_reals_err m (x : R^m.+1) (sn : nat_finset) (o : order sn) :
  let: n := size sn in
  let zeta := ((INR n * eps + INR (2 * n - 1) * eps²) / (1 + eps)²)%Re in
  (Rabs (\sum_(i <- sn) (x (inord i) : R) - fsum o [ffun i => frnd (x i)])
   <= zeta * (\sum_(i <- sn) (Rabs (x (inord i)))) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
move=> zeta.
have Peps := eps_pos fs.
pose v := eps / (1 + eps).
case En: (size sn) o @zeta => [|n'] o zeta.
{ have Ko := size_order o.
  by exfalso; rewrite En in Ko. }
set rx := [ffun _ => _].
pose srx := \sum_(i <- sn) (rx (inord i) : R).
rewrite (_: ?[x] - ?[o] = srx - ?o + (?x - srx)); last by ring.
apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
apply: (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ (fsum_err rx o))).
fold v.
rewrite /srx /Rminus big_sum_Ropp -big_split.
apply: (Rle_trans _ _ _ (Rplus_le_compat_l _ _ _ (big_Rabs_triang _ _))).
set INRnp1 := INR n'.+1; simpl.
have H : \sum_(i <- sn) Rabs (rx (inord i)) <= \sum_(i <- sn) Rabs (x (inord i)) + \sum_(i <- sn) Rabs (x (inord i) - rx (inord i)).
{ rewrite -big_split; apply: Rle_big_compat=> i /=.
  have{1}->: (rx (inord i) = x (inord i) + (rx (inord i) - x (inord i)) :> R); [ring|].
  by apply: (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_minus_sym; right. }
have H' : \sum_(i <- sn) Rabs (x (inord i) - rx (inord i))
          <= eps / (1 + eps) * (\sum_(i <- sn) Rabs (x (inord i))) + INR n'.+1 * eta.
{ apply (Rle_trans _ (\sum_(i <- sn) (eps / (1 + eps) * Rabs (x (inord i)) + eta)%Re)).
  { apply: Rle_big_compat => i.
    have [d [e [Hde _]]] := frnd_spec fs (x (inord i)).
    rewrite Rabs_minus_sym /rx ffunE Hde.
    rewrite (_: _ - _ = d * x (inord i) + e)%Re; [|ring].
    apply: (Rle_trans _ _ _ (Rabs_triang _ _)); rewrite Rabs_mult.
    apply: Rplus_le_compat; [apply Rmult_le_compat_r; [apply Rabs_pos|]|];
    exact: bounded_prop. }
  by rewrite big_split /= /GRing.add /= -big_distrr /= big_sum_const_seq En; right. }
have H'' : \sum_(i <- sn) Rabs (rx (inord i))
           <= (1 + eps / (1 + eps)) * (\sum_(i <- sn) Rabs (x (inord i))) + INR n'.+1 * eta.
{ rewrite Rmult_plus_distr_r Rmult_1_l Rplus_assoc.
  by apply (Rle_trans _ _ _ H), Rplus_le_compat_l. }
apply: (Rle_trans _ ((INR n' * v * (1 + v) + v) * (\sum_(i <- sn) Rabs (x (inord i)))
                    + (INR n' * v + 1) * INR n'.+1 * eta)).
{
  rewrite !Rmult_plus_distr_r Rmult_1_l.
  rewrite -Rplus_assoc (Rplus_comm _ (_ * _ * eta)) -Rplus_assoc Rplus_assoc.
  apply Rplus_le_compat; [|exact: H'].
  rewrite (Rplus_comm (_ * _ * eta)).
  rewrite ![INR n' * v * _ * _]Rmult_assoc -Rmult_plus_distr_l En.
  apply: Rmult_le_compat_l; [|exact: H''].
  apply: Rmult_le_pos; [exact: pos_INR|].
  by apply epsd1peps_pos. }
apply: Rplus_le_compat.
{ apply: Rmult_le_compat_r; [exact: big_sum_Rabs_pos|].
  apply: (Rmult_le_reg_r (1 + eps)²); [apply: Rlt_0_sqr; lra|].
  rewrite /zeta /Rsqr /v; field_simplify; [|lra|lra].
  rewrite /Rdiv Rinv_1 !Rmult_1_r.
  rewrite mul2n doubleS subn1 Nat.pred_succ !S_INR -mul2n mult_INR /=.
  apply: Req_le; ring. }
apply: Rmult_le_compat_r; [exact: eta_pos|].
apply: Rmult_le_compat_r; [exact: pos_INR|].
rewrite Rplus_comm /v /Rdiv; apply: Rplus_le_compat_l; apply: Rmult_le_compat.
{ apply: pos_INR. }
{ exact: epsd1peps_pos. }
{ exact/le_INR/leP. }
exact: epsd1peps_le_eps.
Qed.

Corollary fsum_reals_err' m (x : R^m.+1) (sn : nat_finset) (o : order sn) :
  let: n := size sn in
  (Rabs (\sum_(i <- sn) x (inord i) - fsum o [ffun i => frnd (x i)])
   <= INR n * eps * (\sum_(i <- sn) Rabs (x (inord i))) + (1 + INR n * eps) * INR n * eta)%Re.
Proof.
have Peps := eps_pos fs.
move: (fsum_reals_err x o) => /= H.
apply: (Rle_trans _ _ _ H); apply: Rplus_le_compat_r.
apply: Rmult_le_compat_r; [exact: big_sum_Rabs_pos|].
apply: (Rmult_le_reg_r (1 + eps)²); [apply: Rlt_0_sqr; lra|].
rewrite /Rsqr; field_simplify; [rewrite /Rdiv Rinv_1 !Rmult_1_r|lra].
apply: (Rplus_le_reg_r (- (INR (size sn) * eps))); ring_simplify.
rewrite -(Rplus_0_l (_ ^ 2 * _)); apply: Rplus_le_compat.
{ apply: Rmult_le_pos; [apply: pos_INR|apply: pow_le; exact: eps_pos]. }
rewrite Rmult_comm; apply Rmult_le_compat_r; [apply pow2_ge_0|].
by rewrite -[2]/(INR 2) -mult_INR; apply /le_INR /leP; rewrite multE leq_subr.
Qed.

End Fsum.
