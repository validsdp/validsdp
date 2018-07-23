(** * Miscellaneous lemmas. *)

Require Import Reals QArith CBigQ.
Require Import Flocq.Core.Raux.
Require Import Interval.Interval_missing.
Require Import Psatz.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finfun ssralg matrix bigop.
From mathcomp Require Import ssrnum ssrint rat.

From CoqEAL.refinements Require Import binrat.
Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Open Scope R_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.
Delimit Scope Q_scope with Qrat.

Import GRing.Theory.
Import Num.Theory.

(** As in the latest version of CoqEAL, all relations are in [Type],
we need to add some material, such as [ifft], which is similar to [iff] *)
Inductive ifft (A B : Type) : Type := Ifft of (A -> B) & (B -> A).
Infix "<=>" := ifft (at level 95) : type_scope.

Section ApplyIfft.

Variables P Q : Type.
Hypothesis eqPQ : P <=> Q.

Lemma ifft1 : P -> Q. Proof. by case: eqPQ. Qed.
Lemma ifft2 : Q -> P. Proof. by case: eqPQ. Qed.

End ApplyIfft.

Hint View for move/ ifft1|2 ifft2|2.
Hint View for apply/ ifft1|2 ifft2|2.

Lemma ifftW (P Q : Prop) : P <=> Q -> (P <-> Q).
Proof. by case. Qed.

(** ** Lemmas mostly about real numbers. *)
Section Misc.

(** [ord0] is the only value in ['I_1]. *)
Lemma ord_1_0 (i : 'I_1) : i = ord0.
Proof. by case: i => [[]] // HH; apply /eqP. Qed.

(** About [Rabs]. *)
Lemma Rabs_0 x : (Rabs x = 0 -> x = 0)%Re.
Proof. split_Rabs; lra. Qed.

Lemma Rge_opp_abs x : - Rabs x <= x.
Proof. split_Rabs; lra. Qed.

(** About [Rmax]. *)
Lemma Rle_max_compat x y z t : x <= y -> z <= t -> Rmax x z <= Rmax y t.
Proof.
move=> Hxy Hzt.
apply Rle_trans with (Rmax y z).
{ apply Rle_max_compat_r => //; apply Rle_max_compat_l. }
apply Rle_max_compat_l => //; apply Rle_max_compat_r.
Qed.

(** About square and square root. *)
Lemma sqr_ge_0 x : (0 <= x * x)%Re.
Proof. by replace (x * x)%Re with (x ^ 2)%Re; [apply pow2_ge_0|ring]. Qed.

Lemma sqrtx_le_x x : (1 <= x -> sqrt x <= x)%Re.
Proof.
move=> Hx.
rewrite -{2}(sqrt_Rsqr x); [|lra].
apply sqrt_le_1_alt; rewrite /Rsqr -{1}(Rmult_1_r x).
apply Rmult_le_compat_l; lra.
Qed.

Lemma sqrtx_le_xp1 x : (0 <= x -> sqrt x <= x + 1)%Re.
Proof.
move=> Hx.
rewrite -(sqrt_Rsqr (x + 1)); [|lra].
have Lx := Rle_0_sqr x; have L1 := Rle_0_sqr 1.
apply sqrt_le_1_alt; rewrite Rsqr_plus; lra.
Qed.

(** About [pow]. *)
Lemma pow_rexp r n : r ^ n = (r ^+ n)%Ri.
Proof.
elim: n => [//|n' IH].
by rewrite /= IH /GRing.exp /=; case n'=> //; rewrite Rmult_1_r.
Qed.

(** If the sum of two non negative is zero, they are both zero. *)
Lemma sum_pos_eq_0_l x y : (0 <= x -> 0 <= y -> x + y = 0 -> x = 0)%Re.
Proof. move => *; lra. Qed.

Lemma sum_pos_eq_0_r x y : (0 <= x -> 0 <= y -> x + y = 0 -> y = 0)%Re.
Proof. move => *; lra. Qed.

(** *** Lemmas about bigops. *)
Section Big_misc.

Ltac simpl_re := rewrite /GRing.add /GRing.zero /=.

(** If something exists for each item, we can build an array. *)
Lemma big_exists R (idx : R) op d (d0 : d) n F F' :
  (forall i : 'I_n, exists e : d, F i = F' i e) ->
  exists ea : d ^ n, \big[op/idx]_i F i = \big[op/idx]_i F' i (ea i).
Proof.
move => H.
suff [ea P]: exists ea : d ^ n, forall i : 'I_n, F i = F' i (ea i).
{ by exists ea; apply: eq_bigr. }
elim: n F F' H => //= [F F' _|n IH F F' H].
{ by exists [ffun => d0] => [[]]. }
have [i|y Hy] := (IH (F \o (lift ord0)) (F' \o (lift ord0))).
{ by have [y Hy] := (H (lift ord0 i)); exists y. }
have [x Hx] := H ord0.
exists [ffun i => if unlift ord0 i is Some j then y j else x] => i.
rewrite ffunE; case: unliftP => [j ->|-> //]; apply Hy.
Qed.

Lemma big_Rabs_pos_eq idx op n F : (forall i : 'I_n, 0 <= F i) ->
  \big[op/idx]_i Rabs (F i) = \big[op/idx]_i F i.
Proof. by move=> H; apply eq_bigr => i; rewrite Rabs_pos_eq //. Qed.

Lemma big_Rabs_ffunE idx op n F :
  \big[op/idx]_(i < n) Rabs ([ffun i => F i] i) = \big[op/idx]_i Rabs (F i).
Proof. by apply eq_bigr => i; rewrite ffunE. Qed.

Lemma big_sum_Ropp n F : (- (\sum_(i < n) F i) = \sum_i (- F i)%Re)%Re.
Proof.
apply (big_rec2 (fun x y => (- x = y)%Re)); [by rewrite Ropp_0|].
by move=> i y1 y2 _ H; rewrite -H /GRing.add /= Ropp_plus_distr.
Qed.

Lemma big_sum_const n x : (\sum_(i < n) x = INR n * x)%Re.
Proof.
move: n x; elim=> [|n IHk] x.
{ by rewrite big_ord0 /= Rmult_0_l. }
by rewrite big_ord_recl S_INR Rplus_comm Rmult_plus_distr_r Rmult_1_l IHk.
Qed.

Lemma big_sum_pred_const (I : Type) (r : seq I) (P : pred I) (x : R) :
  \big[+%R/0]_(i <- r | P i) x = INR (size [seq i <- r | P i]) * x.
Proof.
rewrite -big_filter; set l := [seq x <- r | P x]; elim l => [|h t IH].
{ by rewrite big_nil /= Rmult_0_l. }
simpl size; rewrite big_cons S_INR IH /GRing.add /GRing.mul /=; ring.
Qed.

Lemma big_sum_pred_pos_pos n (P : pred 'I_n) F :
  ((forall i : 'I_n, P i -> 0 <= F i) -> 0 <= \sum_(i | P i) F i)%Re.
Proof.
move=> HF.
apply big_rec; [by right|]; move=> i x HP Hx.
by apply Rplus_le_le_0_compat; [apply HF|].
Qed.

Lemma big_sum_pos_pos n F : ((forall i : 'I_n, 0 <= F i) -> 0 <= \sum_i F i)%Re.
Proof. by move=> HF; apply big_sum_pred_pos_pos. Qed.

Lemma big_sum_Rabs_pos n (F : 'I_n -> _) : (0 <= \sum_i (Rabs (F i)))%Re.
Proof. apply big_sum_pos_pos => i; apply Rabs_pos. Qed.

Lemma big_sum_sqr_pos n (F : 'I_n -> _) : (0 <= \sum_i (F i * F i)%Re)%Re.
Proof. apply big_sum_pos_pos => i; apply sqr_ge_0. Qed.

(** If a sum of nonnegative values is zero, then all terms are zero. *)
Lemma big_sum_pos_eq_0 n (F : 'I_n -> R) :
  ((forall i, 0 <= F i) -> \sum_i F i = 0 -> forall i, F i = 0)%Re.
Proof.
move=> H Hi i.
have [R|//] := Rle_lt_or_eq_dec _ _ (H i).
suff HH: (0 < \big[+%R/0]_j F j)%Re by move: Hi HH; simpl_re; lra.
rewrite (bigD1 i) //=.
set X := \big[_/_]_(_|_) _.
suff: (0 <= X)%Re by simpl_re; lra.
by apply big_sum_pred_pos_pos.
Qed.

Lemma big_Rabs_triang n (F : 'I_n -> R) :
  (Rabs (\sum_i (F i)) <= \sum_i (Rabs (F i)))%Re.
Proof. elim/big_rec2: _ => [|i y x _]; split_Rabs; simpl_re; lra. Qed.

End Big_misc.

(** *** A maximum on tuples. *)
Section Max_tuple.

(** Since R has no least element, the tuple has to be non-empty,
    hence the +1. *)
Fixpoint max_tuple n (a : R ^ n.+1) :=
  match n with
    | 0%N => a ord0
    | n'.+1 => Rmax (max_tuple [ffun i : 'I_n'.+1 => a (inord i)]) (a ord_max)
  end.

Lemma max_tuple_eq n (a1 : R ^ n.+1) (a2 : R ^ n.+1) :
  a1 =1 a2 -> max_tuple a1 = max_tuple a2.
Proof.
elim: n a1 a2 => [|n IHn] a1 a2 H12 //=.
apply f_equal2 => //; apply IHn => i; rewrite !ffunE //.
Qed.

Lemma max_tuple_monotone n (a1 : R ^ n.+1) (a2 : R ^ n.+1) :
  (forall i, a1 i <= a2 i) -> max_tuple a1 <= max_tuple a2.
Proof.
elim: n a1 a2 => [|n IHn] a1 a2 H12 //=; apply Rle_max_compat => //.
by apply IHn => i; rewrite !ffunE.
Qed.

Lemma max_tuple_i n (a : R ^ n.+1) (i : 'I_n.+1) : a i <= max_tuple a.
Proof.
elim: n a i => [|n IHn] a i /=; [by rewrite (ord_1_0 i); right|].
case (unliftP ord_max i) => [j ->|->]; [|by apply Rmax_r].
replace (a _) with ([ffun i : 'I_n.+1 => a (inord i)] j).
{ apply (Rle_trans _ _ _ (IHn _ _)), Rmax_l. }
rewrite ffunE; apply f_equal, ord_inj; rewrite lift_max inordK //.
apply ltnW, leq_ord.
Qed.

Lemma max_tuple_lub_lt n (a : R ^ n.+1) (x : R) :
  (forall i, a i < x) -> max_tuple a < x.
Proof.
elim: n a x => [|n IHn] a x Hx //=.
apply Rmax_lub_lt; [|by apply Hx].
apply IHn => i; rewrite ffunE; apply Hx.
Qed.

Lemma max_tuple_Rmult n (a : R ^ n.+1) (c : R) : 0 <= c ->
  (max_tuple [ffun i => c * a i] = c * max_tuple a)%Re.
Proof.
elim: n a c => [|n IHn] a c Hc /=; [by rewrite ffunE|].
rewrite -RmaxRmult; [|by []]; apply f_equal2; [|by rewrite ffunE].
by rewrite -IHn; [|by []]; apply max_tuple_eq => i; rewrite !ffunE.
Qed.

Lemma max_tuple_prod n (a b : R ^ n.+1) :
  (forall i, 0 <= a i) -> (forall i, 0 <= b i) ->
  max_tuple [ffun i => a i * b i] <= max_tuple a * max_tuple b.
Proof.
move=> Ha Hb.
apply Rle_trans with (max_tuple [ffun i => max_tuple a * b i]).
{ apply max_tuple_monotone => i; rewrite !ffunE.
  apply Rmult_le_compat_r; [apply Hb|apply max_tuple_i]. }
right; apply max_tuple_Rmult; apply (Rle_trans _ _ _ (Ha ord0)), max_tuple_i.
Qed.

Lemma max_tuple_sum n (a : R ^ n.+1) : \sum_i a i <= INR n.+1 * max_tuple a.
Proof.
elim: n a => [|n IHn] a.
{ by rewrite zmodp.big_ord1 Rmult_1_l; right. }
rewrite big_ord_recr S_INR Rmult_plus_distr_r Rmult_1_l; apply Rplus_le_compat.
{ apply Rle_trans with (INR n.+1 * max_tuple [ffun i : 'I_n.+1 => a (inord i)]).
  { replace (_ : R) with (\sum_i [ffun i : 'I_n.+1 => a (inord i)] i);
      [by apply IHn|].
    apply eq_bigr => i _; rewrite ffunE.
    apply f_equal, ord_inj; rewrite inordK //; apply ltnW, leq_ord. }
  apply Rmult_le_compat_l; [apply pos_INR|apply Rmax_l]. }
apply Rmax_r.
Qed.

End Max_tuple.

End Misc.

(** ** Lemmas about [BigQ] and [R] *)
Definition Q2R (x : Q) : R :=
  (IZR (Qnum x) / IZR (Z.pos (Qden x)))%Re.

Definition bigQ2R (x : BigQ.t_ (* the type of (_ # _)%bigQ *)) : R :=
  Q2R [x]%bigQ.

Ltac pos_IPR :=
  by rewrite /= -INR_IPR; apply not_0_INR, not_eq_sym, lt_0_neq, Pos2Nat.is_pos.

Lemma Q2R_0 : Q2R 0%Qrat = 0%Re.
Proof. by rewrite /Q2R /= /Rdiv Rmult_0_l. Qed.

Lemma Q2R_inv x : Q2R x <> 0%Re -> Q2R (/ x) = / (Q2R x).
Proof.
move: x => [[|a|a] b] Hx; rewrite /Q2R /Qinv /=.
{ by rewrite /Q2R /= /Rdiv Rmult_0_l in Hx. }
{ clear Hx; rewrite Rinv_Rdiv //. }
{ clear Hx; rewrite /Rdiv !Ropp_mult_distr_l_reverse -Ropp_inv_permute.
  rewrite Rinv_Rdiv //; pos_IPR.
  by apply Rmult_integral_contrapositive_currified;
    [pos_IPR|apply Rinv_neq_0_compat]. }
Qed.

Lemma Q2R_mult x y : Q2R (x * y) = (Q2R x * Q2R y)%Re.
Proof.
  rewrite /Q2R /= !(mult_IZR, Pos2Z.inj_mul) /Rdiv Rinv_mult_distr //; ring.
Qed.

Lemma Q2R_opp x : Q2R (- x) = (- Q2R x)%Re.
Proof. by rewrite /Q2R /= opp_IZR -Ropp_mult_distr_l_reverse. Qed.

Lemma Q2R_Qeq x y :
  Qeq x y -> Q2R x = Q2R y.
Proof.
move=> Hxy; rewrite /Q2R.
rewrite /Qeq in Hxy.
move/(congr1 IZR) in Hxy.
rewrite !mult_IZR in Hxy.
apply (Rmult_eq_reg_r (IZR (BinNums.Zpos (Qden y)))); last by simpl.
by rewrite /Rdiv Rmult_assoc [(/ _ * _)%Re]Rmult_comm -Rmult_assoc Hxy; field.
Qed.

Lemma Qeq_Q2R x y :
  Q2R x = Q2R y -> Qeq x y.
Proof.
move=> Hxy; rewrite /Qeq.
rewrite /Q2R in Hxy.
apply: eq_IZR.
rewrite !mult_IZR.
apply (Rmult_eq_reg_r (/ IZR (BinNums.Zpos (Qden x)))); last first.
{ apply: Rinv_neq_0_compat.
  by change 0%Re with (IZR 0); apply: IZR_neq. }
rewrite /Rdiv in Hxy.
by rewrite Rmult_assoc [(_ * / _)%Re]Rmult_comm -Rmult_assoc Hxy; field.
Qed.

(** ** Lemmas about [BigQ.check_int], [BigQ.norm] and [BigQ.red] *)

Local Open Scope Z_scope.

Lemma BigQ_check_int_den_neq0_aux n d :
  match BigQ.check_int n d with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof.
rewrite /BigQ.check_int.
case E: (_ ?= _)%bigN=>//.
move: E; rewrite BigN.compare_lt_iff=> E H.
apply (BigN.lt_irrefl BigN.one).
apply (BigN.lt_trans _ BigN.zero); [|apply BigN.lt_0_1].
by move: E; rewrite -BigN.ltb_lt BigN.spec_ltb H /=.
Qed.

Lemma BigQ_check_int_den_neq0 n d :
  match BigQ.check_int n d with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof.
move: (BigQ_check_int_den_neq0_aux n d); case (BigQ.check_int _ _)=>[//|_ n' H].
by apply/negP; rewrite /is_true BigN.spec_eqb Z.eqb_eq=>H'; apply H; rewrite H'.
Qed.

Lemma BigQ_norm_den_neq0_aux n d :
  match BigQ.norm n d with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof.
case E: (BigQ.norm _ _)=>//; move: E; rewrite /BigQ.norm.
case (_ ?= _)%bigN.
{ move: (BigQ_check_int_den_neq0_aux n d).
  by case (BigQ.check_int _ _)=>[//| n' d'] H [] _ <-. }
{ set n' := (_ / _)%bigZ; set d' := (_ / _)%bigN.
  move: (BigQ_check_int_den_neq0_aux n' d').
  by case (BigQ.check_int _ _)=>[//| n'' d''] H [] _ <-. }
by [].
Qed.

Lemma BigQ_norm_den_neq0 n d :
  match BigQ.norm n d with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof.
move: (BigQ_norm_den_neq0_aux n d); case (BigQ.norm _ _)=>[//|_ n' H].
by apply/negP; rewrite /is_true BigN.spec_eqb Z.eqb_eq=>H'; apply H; rewrite H'.
Qed.

Lemma BigQ_red_den_neq0_aux q :
  match BigQ.red q with
    | BigQ.Qz _ => True
    | BigQ.Qq _ d => [d]%bigN <> 0
  end.
Proof. by rewrite /BigQ.red; case q=>// n d; apply BigQ_norm_den_neq0_aux. Qed.

Lemma BigQ_red_den_neq0 q :
  match BigQ.red q with
    | BigQ.Qz _ => true
    | BigQ.Qq _ d => ~~(d =? BigN.zero)%bigN
  end.
Proof. by rewrite /BigQ.red; case q=>// n d; apply BigQ_norm_den_neq0. Qed.

(** ** Lemmas about [int], [rat] and [R] *)

Lemma Z2R_int2Z_nat (n : nat) : IZR (int2Z n) = n%:~R.
Proof.
elim: n => [//|n IHn].
rewrite -addn1 PoszD intrD -{}IHn /= addn1.
set zn := match n with O => Z0 | _ => Z.pos (Pos.of_nat n) end.
suff->: zn = Z.of_nat n.
{ change 1%N%:~R with (IZR 1).
  rewrite /GRing.add /= -plus_IZR Z.add_1_r -Nat2Z.inj_succ.
  by rewrite /Z.of_nat Pos.of_nat_succ. }
clear; rewrite {}/zn /Z.of_nat.
case: n => // n.
by rewrite Pos.of_nat_succ.
Qed.

Lemma Z2R_int2Z n : IZR (int2Z n) = n%:~R.
Proof.
elim/int_rec: n =>// n IHn.
{ exact: Z2R_int2Z_nat. }
by clear IHn; rewrite mulrNz /= -Z2R_int2Z_nat.
Qed.

Lemma int2Z_le m n : int2Z m <=? int2Z n = (m <= n)%Ri.
Proof.
rewrite -(ler_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.leb_le/IZR_le/RleP. }
by move/RleP/le_IZR/Z.leb_le.
Qed.

Lemma int2Z_lt m n : int2Z m <? int2Z n = (m < n)%Ri.
Proof.
rewrite -(ltr_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.ltb_lt/IZR_lt/RltP. }
by move/RltP/lt_IZR/Z.ltb_lt.
Qed.

Lemma bigQ2R_redE (c : bigQ) : bigQ2R (BigQ.red c) = bigQ2R c.
Proof.
case: c => [//|n d].
by rewrite /bigQ2R; apply: Q2R_Qeq; apply: BigQ.spec_red.
Qed.

Notation rat2R := (@ratr real_unitRingType) (only parsing).

Lemma bigQ2R_rat (c : bigQ) : bigQ2R c = rat2R (bigQ2rat c).
Proof.
rewrite -[LHS]bigQ2R_redE /bigQ2R BigQ.strong_spec_red.
rewrite /bigQ2rat /ratr; set r := Rat _.
rewrite /GRing.inv /= /invr ifF /GRing.mul /= /Rdiv.
{ rewrite /numq /denq /=; congr Rmult.
  { rewrite /IZR /Z2int; case: Qnum =>[//|p|p].
      by rewrite -INR_IPR binnat.to_natE INR_natmul.
    rewrite -INR_IPR binnat.to_natE INR_natmul /=.
    now rewrite -> mulrNz. }
  by rewrite /IZR /= -INR_IPR binnat.to_natE INR_natmul. }
rewrite -(denq_eq0 (r)).
have->: 0%Re = O%:~R by [].
exact/inj_eq/intr_inj.
Qed.

Lemma ratr_inj (R : numFieldType) : injective (@ratr R).
Proof. by move=> x y H; apply ler_asym; rewrite -!(ler_rat R) H lerr. Qed.
