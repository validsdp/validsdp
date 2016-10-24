(** * Miscellaneous lemmas. *)

Require Import Reals QArith BigQ.
Require Import Flocq.Core.Fcore_Raux.
Require Import Interval.Interval_missing.
Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.algebra.matrix mathcomp.ssreflect.bigop.
From mathcomp Require Import ssrnum ssrint rat div.

From CoqEAL.refinements Require Import binnat.
Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Open Scope R_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

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

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

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

(** Section taken from coq-interval *)
Section Map2.
Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B -> C.

Fixpoint map2 (s1 : seq A) (s2 : seq B) : seq C :=
  match s1, s2 with
    | a :: s3, b :: s4 => f a b :: map2 s3 s4
    | _, _ => [::]
  end.

Lemma size_map2 (s1 : seq A) (s2 : seq B) :
  size (map2 s1 s2) = minn (size s1) (size s2).
Proof.
elim: s1 s2 => [|x1 s1 IH1] [|x2 s2] //=.
by rewrite IH1 -addn1 addn_minl 2!addn1.
Qed.

Lemma nth_map2 s1 s2 (k : nat) da db dc :
  dc = f da db -> size s2 = size s1 ->
  nth dc (map2 s1 s2) k = f (nth da s1 k) (nth db s2 k).
Proof.
elim: s1 s2 k => [|x1 s1 IH1] s2 k Habc Hsize.
  by rewrite (size0nil Hsize) !nth_nil.
case: s2 IH1 Hsize =>[//|x2 s2] IH1 [Hsize].
case: k IH1 =>[//|k]; exact.
Qed.

End Map2.

(** About [BigQ] *)
Definition Q2R (x : Q) : R :=
  (Z2R (Qnum x) / Z2R (Z.pos (Qden x)))%Re.

Definition bigQ2R (x : BigQ.t_ (* the type of (_ # _)%bigQ *)) : R :=
  Q2R [x]%bigQ.


Ltac pos_P2R :=
  by rewrite P2R_INR; apply not_0_INR, not_eq_sym, lt_0_neq, Pos2Nat.is_pos.

Lemma Q2R_inv x : Q2R x <> 0%Re -> Q2R (/ x) = / (Q2R x).
Proof.
move: x => [[|a|a] b] Hx; rewrite /Q2R /Qinv /=.
{ by rewrite /Q2R /= /Rdiv Rmult_0_l in Hx. }
{ clear Hx; rewrite Rinv_Rdiv //; pos_P2R. }
{ clear Hx; rewrite /Rdiv !Ropp_mult_distr_l_reverse -Ropp_inv_permute.
  rewrite Rinv_Rdiv //; pos_P2R.
  apply Rmult_integral_contrapositive_currified; [|apply Rinv_neq_0_compat];
    pos_P2R. }
Qed.

Lemma Q2R_mult x y : Q2R (x * y) = (Q2R x * Q2R y)%Re.
Proof.
rewrite /Q2R /= !(Z2R_mult, P2R_INR, Pos2Nat.inj_mul, mult_INR) -!P2R_INR.
rewrite /Rdiv Rinv_mult_distr; first ring; pos_P2R.
Qed.

Lemma Q2R_opp x : Q2R (- x) = (- Q2R x)%Re.
Proof. by rewrite /Q2R /= Z2R_opp -Ropp_mult_distr_l_reverse. Qed.

Lemma Q2R_Qeq x y :
  Qeq x y -> Q2R x = Q2R y.
Proof.
move=> Hxy; rewrite /Q2R.
rewrite /Qeq in Hxy.
move/(congr1 Z2R) in Hxy.
rewrite !Z2R_mult in Hxy.
apply (Rmult_eq_reg_r (Z2R (' Qden y))); last by simpl; pos_P2R.
rewrite /Rdiv Rmult_assoc [(/ _ * _)%Re]Rmult_comm -Rmult_assoc Hxy.
field; split; simpl; pos_P2R.
Qed.

Lemma Qeq_Q2R x y :
  Q2R x = Q2R y -> Qeq x y.
Proof.
move=> Hxy; rewrite /Qeq.
rewrite /Q2R in Hxy.
apply: eq_Z2R.
rewrite !Z2R_mult.
apply (Rmult_eq_reg_r (/ Z2R (' Qden x))); last first.
{ apply: Rinv_neq_0_compat.
  by change R0 with (Z2R 0); apply: Z2R_neq. }
rewrite /Rdiv in Hxy.
rewrite Rmult_assoc [(_ * / _)%Re]Rmult_comm -Rmult_assoc Hxy.
field; split; simpl; pos_P2R.
Qed.

(** About [int] and [rat] *)

Lemma nat_of_pos_gt0 p : (0 < nat_of_pos p)%N.
Proof. by elim: p =>//= p IHp; rewrite NatTrec.doubleE double_gt0. Qed.

Lemma nat_of_pos_inj x y : nat_of_pos x = nat_of_pos y -> x = y.
Proof. rewrite -!binnat.to_natE; apply Pos2Nat.inj. Qed.

Lemma Posz_nat_of_pos_neq0 p : Posz (nat_of_pos p) == 0%Ri = false.
Proof.
rewrite -binnat.to_natE.
case E: (Pos.to_nat _)=>//; exfalso; move: E.
by move: (binnat.to_nat_gt0 p); case (Pos.to_nat _).
Qed.

Definition Z2int (z : BinNums.Z) :=
  match z with
  | Z0 => 0%:Z
  | Z.pos p => (nat_of_pos p)%:Z
  | Z.neg n => (- (nat_of_pos n)%:Z)%R
  end.

Lemma Z2int_inj x y : Z2int x = Z2int y -> x = y.
Proof.
rewrite /Z2int.
case x, y=>//.
{ move=>[] H.
  by rewrite -[Z0]/(Z.of_nat 0%N) H -binnat.to_natE positive_nat_Z. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ rewrite -binnat.to_natE; case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ by move=>[] /nat_of_pos_inj ->. }
{ rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case (Pos.to_nat p0)=>//=.
  by move=>[] H; move: (binnat.to_nat_gt0 p); rewrite H ltnn. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat p)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
case E: (Pos.to_nat p)=>//=.
{ by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
case E': (Pos.to_nat p0)=>//= [] [] H.
by move: E'; rewrite -H -E=>/Pos2Nat.inj ->.
Qed.

Lemma Z2int_opp n : Z2int (- n) = (- (Z2int n))%Ri.
Proof. by case n=>// p /=; rewrite GRing.opprK. Qed.

Lemma Z2int_add x y : Z2int (x + y) = (Z2int x + Z2int y)%Ri.
Proof.
rewrite /Z2int /GRing.add /= /intZmod.addz /Z.add; case x, y=>//.
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  by case (Pos.to_nat p)=>// n; rewrite subn0. }
{ by rewrite addn0. }
{ by rewrite nat_of_addn_gt0. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  move: (Z.pos_sub_discr p p0); case (Z.pos_sub _ _).
  { move<-; rewrite -binnat.to_natE; case (Pos.to_nat _)=>// n.
    by rewrite ltnSn subnn. }
  { move=> p' ->; rewrite -!binnat.to_natE Pos2Nat.inj_add.
    case (Pos.to_nat p0); [by rewrite Nat.add_0_l addn0|move=> n].
    rewrite ifT; [by rewrite plusE addKn|].
    by rewrite plusE; apply ltn_addr; rewrite ltnSn. }
  move=> p' ->; rewrite -!binnat.to_natE Pos2Nat.inj_add.
  case (Pos.to_nat p').
  { rewrite Nat.add_0_r; case (Pos.to_nat p)=>// n.
    by rewrite ltnSn subnn. }
  move=> n.
  case E: (Pos.to_nat p)=>/=; [by rewrite subn0|].
  rewrite ifF.
  { by rewrite plusE addnS -addSn addKn. }
  by rewrite plusE addnS -addSn -ltn_subRL subnn ltn0. }
{ rewrite /GRing.opp /= /intZmod.oppz -binnat.to_natE.
  by case (Pos.to_nat p); [rewrite addn0|move=>n; rewrite subn0]. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  move: (Z.pos_sub_discr p p0); case E': (Z.pos_sub _ _).
  { move<-; rewrite -binnat.to_natE Z.pos_sub_diag; case (Pos.to_nat _)=>// n.
    by rewrite ltnSn subnn. }
  { move=> ->.
    rewrite -!binnat.to_natE Pos2Nat.inj_add Z.pos_sub_lt; last first.
    { by apply Pos.lt_add_diag_r. }
    rewrite -binnat.to_natE Pos2Nat.inj_sub ?Pos2Nat.inj_add; last first.
    { by apply Pos.lt_add_diag_r. }
    rewrite plusE minusE addKn; case (Pos.to_nat _).
    { by rewrite addn0; case (Pos.to_nat p0)=>// n; rewrite ltnSn subnn. }
    move=> n.
    case E: (Pos.to_nat p0 + n.+1)%N.
    { by exfalso; move: E; rewrite addnS. }
    rewrite -E ifF.
    { f_equal.
      have H: (Pos.to_nat p0 + n.+1 - n.+1 = Pos.to_nat p0 + n.+1 - n.+1)%N.
      { done. }
      move: H; rewrite {2}E addnK=>->.
      by rewrite subnS subSn /= ?subKn //; move: E;
        rewrite addnS=>[] [] <-; rewrite leq_addl. }
    by rewrite addnS -ltn_subRL subnn ltn0. }
  move=> ->; rewrite Z.pos_sub_gt; [|by apply Pos.lt_add_diag_r].
  rewrite -!binnat.to_natE !Pos2Nat.inj_sub; [|by apply Pos.lt_add_diag_r].
  rewrite Pos2Nat.inj_add; case (Pos.to_nat p).
  { by rewrite plusE minusE !add0n subn0. }
  by move=> n; rewrite plusE minusE addKn ifT // leq_addr. }
rewrite -!binnat.to_natE Pos2Nat.inj_add /GRing.opp /= /intZmod.oppz plusE.
case (Pos.to_nat p).
{ by rewrite add0n; case (Pos.to_nat p0)=>// n; rewrite ltn0 subn0. }
move=> n; case (Pos.to_nat p0); [by rewrite addn0 ltn0 subn0|].
by move=> n'; rewrite addSn -addnS.
Qed.

Lemma Z2int_mul_nat_of_pos (x : BinNums.Z) (y : positive) :
  (Z2int x * nat_of_pos y)%Ri = Z2int (Z.mul x (BinNums.Zpos y)).
Proof.
rewrite /Z2int; case Ex: x.
{ by rewrite mul0r Z.mul_0_l. }
{ by rewrite /= -!binnat.to_natE Pos2Nat.inj_mul. }
by rewrite /= mulNr  -!binnat.to_natE Pos2Nat.inj_mul.
Qed.

Lemma Z2int_mul x y : Z2int (x * y) = (Z2int x * Z2int y)%Ri.
Proof.
case y=>/=.
{ by rewrite GRing.mulr0 Z.mul_0_r. }
{ by move=> p; rewrite Z2int_mul_nat_of_pos. }
move=> p.
by rewrite GRing.mulrN Z2int_mul_nat_of_pos -Z2int_opp Zopp_mult_distr_r.
Qed.

Lemma Z2int_le x y : (Z2int x <= Z2int y)%Ri <-> Z.le x y.
Proof.
rewrite /Z2int; case Ex: x; case Ey: y=> //.
{ rewrite oppr_ge0; split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply/negP; rewrite -ltrNge; apply nat_of_pos_gt0. }
{ split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply/negP; rewrite -ltrNge; apply nat_of_pos_gt0. }
{ rewrite -!binnat.to_natE /Num.Def.ler /=.
  by rewrite -!positive_nat_Z -Nat2Z.inj_le; split; [apply/leP|move/leP]. }
{ split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply /negP; rewrite -ltrNge.
  apply (@ltr_trans _ 0%Ri); rewrite ?oppr_lt0; apply nat_of_pos_gt0. }
{ rewrite oppr_le0; split; by rewrite /Z.le. }
{ split=>_; [by rewrite /Z.le|].
  by apply (@ler_trans _ 0%Ri); [apply oppr_le0|apply ltrW, nat_of_pos_gt0]. }
rewrite ler_opp2; split.
{ rewrite /Z.le /Z.compare -!binnat.to_natE /Num.Def.ler /= => /leP.
  by rewrite -Pos.compare_antisym -Pos2Nat.inj_le -Pos.compare_le_iff. }
rewrite /Z.le /Z.compare -!binnat.to_natE /Num.Def.ler /=.
rewrite -Pos.compare_antisym=>H; apply/leP.
by rewrite -Pos2Nat.inj_le -Pos.compare_le_iff.
Qed.

Lemma nat_of_pos_Z_to_pos x : nat_of_pos x = `|Z2int (' x)|%N.
Proof. by rewrite /absz /Z2int. Qed.

Lemma Zabs_natE n : Z.abs_nat n = `|Z2int n|%N.
Proof.
case: n => //= p; first by rewrite binnat.to_natE.
by rewrite abszN absz_nat binnat.to_natE.
Qed.

Definition int2Z (n : int) : BinNums.Z :=
  match n with
  | Posz O => Z0
  | Posz n => Z.pos (Pos.of_nat n)
  | Negz n => Z.neg (Pos.of_nat n.+1)
  end.

Lemma Z2R_int2Z_nat (n : nat) : Z2R (int2Z n) = n%:~R.
Proof.
elim: n => [//|n IHn].
rewrite -addn1 PoszD intrD -{}IHn /=.
rewrite addn1 -addn1 /= P2R_INR Nat2Pos.id ?addn1 // -addn1.
set zn := match n with O => Z0 | _ => Z.pos (Pos.of_nat n) end.
suff->: zn = Z.of_nat n by rewrite -INR_Z2R plus_INR.
clear; rewrite {}/zn /Z.of_nat.
case: n => // n.
by rewrite Pos.of_nat_succ.
Qed.

Lemma Z2R_int2Z n : Z2R (int2Z n) = n%:~R.
Proof.
elim/int_rec: n =>// n IHn.
{ exact: Z2R_int2Z_nat. }
by clear IHn; rewrite mulrNz /= -Z2R_int2Z_nat.
Qed.

Local Open Scope Z_scope.

Lemma int2Z_le m n : int2Z m <=? int2Z n = (m <= n)%Ri.
Proof.
rewrite -(ler_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.leb_le/Z2R_le/RleP. }
by move/RleP/le_Z2R/Z.leb_le.
Qed.

Lemma int2Z_lt m n : int2Z m <? int2Z n = (m < n)%Ri.
Proof.
rewrite -(ltr_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.ltb_lt/Z2R_lt/RltP. }
by move/RltP/lt_Z2R/Z.ltb_lt.
Qed.

Lemma dvdnP m n : reflect (Z.divide (Z.of_nat m) (Z.of_nat n)) (m %| n).
Proof.
apply: (iffP idP) => H.
{ rewrite dvdn_eq in H; rewrite -(eqP H) /Z.divide; exists (Z.of_nat (n %/ m)).
  by rewrite Nat2Z.inj_mul. }
{ have [q Hq] := H; apply/dvdnP; exists `|Z2int q|%N; apply/Nat2Z.inj.
  have [Zq|NZq] := Z_zerop q.
  { by rewrite Zq /= in Hq *. }
  case: m Hq H => [|m] Hq H.
  { by rewrite Zmult_comm /= in Hq; rewrite mulnC /=. }
  rewrite Nat2Z.inj_mul -Zabs_natE Zabs2Nat.id_abs Z.abs_eq //.
  have H0 : (0 <= q * Z.of_nat m.+1) by rewrite -Hq; apply Zle_0_nat.
  by apply: Zmult_le_0_reg_r H0. }
Qed.

Lemma ZgcdE n d : Z.gcd n (' d) = Z.of_nat (div.gcdn `|Z2int n| (nat_of_pos d)).
Proof.
apply: Z.gcd_unique.
{ exact: Zle_0_nat. }
{ apply/Z.divide_abs_r; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE dvdn_gcdl. }
{ apply/Z.divide_abs_r; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE /= dvdn_gcdr. }
move=> q Hn Hd; apply/Z.divide_abs_l; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
rewrite Zabs_natE dvdn_gcd.
apply/andP; split; apply/dvdnP; rewrite -!Zabs_natE !Zabs2Nat.id_abs.
{ by apply/Z.divide_abs_l/Z.divide_abs_r. }
{ by apply/Z.divide_abs_l; rewrite -binnat.to_natE positive_nat_Z. }
Qed.

Lemma ZgcdE' n m : Z.gcd n m = Z.of_nat (gcdn `|Z2int n| `|Z2int m|).
Proof.
case m.
{ rewrite Z.gcd_0_r {2}/absz {2}/Z2int /= gcdn0 -Zabs2Nat.id_abs; f_equal.
  rewrite /Z.abs_nat /absz /Z2int.
  case n=>// p; rewrite -!binnat.to_natE //.
  case (Pos.to_nat _); [by rewrite GRing.oppr0|move=> n'].
  by rewrite /GRing.opp /=. }
{ by move=> p; rewrite ZgcdE nat_of_pos_Z_to_pos. }
by move=> p; rewrite -Z.gcd_opp_r /= ZgcdE abszN /absz.
Qed.

Lemma Z_ggcd_coprime a b :
  let '(g, (a', b')) := Z.ggcd a b in
  g <> 0%Z -> coprime `|Z2int a'| `|Z2int b'|.
Proof.
move: (Z.ggcd_gcd a b) (Z.ggcd_correct_divisors a b).
case (Z.ggcd _ _)=> g ab; case ab=> a' b' /= Hg [] Ha Hb Pg.
rewrite /coprime; apply/eqP /Nat2Z.inj; rewrite -ZgcdE' /=.
suff ->: a' = (a / g)%Z.
{ suff ->: b' = (b / g)%Z; [by apply Z.gcd_div_gcd|].
  by rewrite Hb Z.mul_comm Z_div_mult_full. }
by rewrite Ha Z.mul_comm Z_div_mult_full.
Qed.

Lemma Z_ggcd_1_r n : Z.ggcd n 1 = (1, (n, 1))%Z.
Proof.
move: (Z.ggcd_gcd n 1) (Z.ggcd_correct_divisors n 1); rewrite Z.gcd_1_r.
case (Z.ggcd _ _)=> g ab /= ->; case ab=> a b [].
by rewrite !Z.mul_1_l => <- <-.
Qed.

Program Definition bigQ2rat (bq : bigQ) :=
  let q := Qred [bq]%bigQ in
  @Rat (Z2int (Qnum q), Z2int (Z.pos (Qden q))) _.
Next Obligation.
rewrite ltz_nat nat_of_pos_gt0 /=.
set q := [bq]%bigQ.
have /Qcanon.Qred_iff HQ := Qcanon.Qred_involutive q.
set n := Qnum (Qred q) in HQ *.
set d := Qden (Qred q) in HQ *.
rewrite ZgcdE in HQ.
by rewrite /div.coprime; apply/eqP/Nat2Z.inj; rewrite HQ.
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
  { rewrite /Z2R /Z2int; case: Qnum =>[//|p|p].
      by rewrite P2R_INR binnat.to_natE INR_natmul.
    rewrite P2R_INR binnat.to_natE INR_natmul /=.
    now rewrite -> mulrNz. }
  by rewrite /= P2R_INR binnat.to_natE INR_natmul. }
rewrite -(denq_eq0 (r)).
have->: 0%Re = O%:~R by [].
exact/inj_eq/intr_inj.
Qed.

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
