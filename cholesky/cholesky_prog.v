(** * Application: program for Cholesky decomposition. *)

(* TODO: coqdoc *)

Require Import Reals.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool
        mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype
        mathcomp.ssreflect.ssrnat mathcomp.ssreflect.fintype
        mathcomp.ssreflect.finfun mathcomp.algebra.matrix.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import CoqEAL_refinements.refinements.

Import Refinements.Op.

Require Import iteri_ord float_infnan_spec real_matrix cholesky cholesky_infnan.

Class sqrt T := sqrt_op : T -> T.

Class store_class A I B :=
  store : forall (m n : nat), B m n -> I m -> I n -> A -> B m n.

Class dotmulB0_class A I B :=
  dotmulB0 : forall n : nat, I n -> A -> B 1%nat n -> B 1%nat n -> A.

Section Generic_prog.

Context {T : Type} {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!zero T, !one T, !add T, !opp T, !mul T, !div T, !sqrt T}.
Context `{!fun_of T ord (mx T), !row_class ord (mx T), !store_class T ord (mx T), !dotmulB0_class T ord (mx T)}.
Context {n : nat}.
Context `{!I0_class ord n, !succ0_class ord n, !nat_of_class ord n}.

Definition ytilded (k : ord n) c a b bk := (dotmulB0 k c a b / bk)%C.

Definition ytildes (k : ord n) c a := (sqrt_op (dotmulB0 k c a a)).

(* note: R is transposed with respect to cholesky.v *)
Definition inner_loop j A R :=
  iteri_ord (nat_of j)
            (fun i R => store R j i (ytilded i (fun_of_matrix A i j)
                                             (row i R) (row j R)
                                             (fun_of_matrix R i i)))
            R.

(* note: R is transposed with respect to cholesky.v *)
Definition outer_loop A R :=
  iteri_ord n
            (fun j R =>
               let R := inner_loop j A R in
               store R j j (ytildes j (fun_of_matrix A j j)
                                    (row j R)))
            R.

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky A := outer_loop A A.

End Generic_prog.

Section Inst_ssr_matrix.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, !div T, !mul T, !sqrt T}.

Let ord := ordinal.
Let mx := matrix.

Global Instance fun_of_mx : fun_of T ord (mx T) :=
  fun m n => @matrix.fun_of_matrix T m n.

Global Instance row_mx : row_class ord (mx T) := @matrix.row T.

Global Instance store_mx : store_class T ord (mx T) :=
  fun m n (M : 'M[T]_(m, n)) (i : 'I_m) (j : 'I_n) v =>
  \matrix_(i', j')
    if ((nat_of_ord i' == i) && (nat_of_ord j' == j))%N then v else M i' j'.

Fixpoint fsum_l2r_rec n (c : T) : T ^ n -> T :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (c + (a ord0))%C [ffun i => a (lift ord0 i)]
  end.

Global Instance dotmulB0_mx : dotmulB0_class T ord (mx T) :=
  fun n =>
    match n with
      | 0%N => fun i c a b => c
      | n'.+1 => fun i c a b =>
        fsum_l2r_rec c
        [ffun k : 'I_i => (- ((a ord0 (inord k)) * (b ord0 (inord k))))%C]
    end.

Context {n' : nat}.
Let n := n'.+1.
Global Instance I0_ord : I0_class ord n := ord0.
Global Instance succ0_ord : succ0_class ord n := fun i => inord i.+1.
Global Instance nat_of_ord : nat_of_class ord n := @nat_of_ord n.

Definition ytilded_mx : 'I_n -> T -> 'M[T]_(1, n) -> 'M[T]_(1, n) -> T -> T :=
  @ytilded T ord mx _ _ _.

Definition ytildes_mx : 'I_n -> T -> 'M[T]_(1, n) -> T :=
  @ytildes T ord mx _ _ _.

Definition iteri_ord_mx : forall T, nat -> ('I_n -> T -> T) -> T -> T :=
  @iteri_ord ord _ _ _.

Definition inner_loop_mx : 'I_n -> 'M[T]_n -> 'M[T]_n -> 'M[T]_n :=
  @inner_loop T ord mx _ _ _ _ _ _ _ _ _.

Definition outer_loop_mx : 'M[T]_n -> 'M[T]_n -> 'M[T]_n :=
  @outer_loop T ord mx _ _ _ _ _ _ _ _ _ _.

Definition cholesky_mx : 'M[T]_n -> 'M[T]_n :=
  @cholesky T ord mx _ _ _ _ _ _ _ _ _ _.

Section Proof.

Lemma store_mx_eq (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  nat_of_ord i' = i -> nat_of_ord j' = j -> (store_mx M i j v) i' j' = v.
Proof. by rewrite /nat_of_ord mxE => -> ->; rewrite !eq_refl. Qed.

Lemma store_mx_lt1 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (nat_of_ord i' < i)%N -> (store_mx M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE (ltn_eqF Hi). Qed.

Lemma store_mx_lt2 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (nat_of_ord j' < j)%N -> (store_mx M i j v) i' j' = M i' j'.
Proof. by move=> Hj; rewrite mxE (ltn_eqF Hj) Bool.andb_false_r. Qed.

Lemma store_mx_gt1 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (i < nat_of_ord i')%N -> (store_mx M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE eq_sym (ltn_eqF Hi). Qed.

Lemma store_mx_gt2 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (j < nat_of_ord j')%N -> (store_mx M i j v) i' j' = M i' j'.
Proof.
move=> Hj.
by rewrite mxE (@eq_sym _ (nat_of_ord j')) (ltn_eqF Hj) Bool.andb_false_r.
Qed.

Lemma fsum_l2r_rec_eq k (c1 : T) (a1 : T ^ k)
      (c2 : T) (a2 : T ^ k) :
  c1 = c2 -> (forall i : 'I_k, a1 i = a2 i) ->
  fsum_l2r_rec c1 a1 = fsum_l2r_rec c2 a2.
Proof.
elim: k c1 a1 c2 a2 => [//|k IHk] c1 a1 c2 a2 Hc Ha.
by apply IHk; [rewrite /fplus Hc Ha|move=> i; rewrite !ffunE].
Qed.

Lemma dotmulB0_mx_eq k (i : 'I_k)
      (c1 : T) (a1 b1 : 'rV_k)
      (c2 : T) (a2 b2 : 'rV_k) :
  c1 = c2 -> (forall j : 'I_k, (j < i)%N -> a1 ord0 j = a2 ord0 j) ->
  (forall j : 'I_k, (j < i)%N -> b1 ord0 j = b2 ord0 j) ->
  dotmulB0_mx i c1 a1 b1 = dotmulB0_mx i c2 a2 b2.
Proof.
case: k i c1 a1 b1 c2 a2 b2 => //= k i c1 a1 b1 c2 a2 b2 Hc Ha Hb.
apply fsum_l2r_rec_eq => // j; rewrite !ffunE Ha ?Hb //;
  (rewrite inordK; [|apply (ltn_trans (ltn_ord j))]); apply ltn_ord.
Qed.

Lemma ytilded_mx_eq (k : 'I_n)
      (c1 : T) (a1 b1 : 'rV_n) (bk1 : T)
      (c2 : T) (a2 b2 : 'rV_n) (bk2 : T) :
  c1 = c2 -> (forall i : 'I_n, (i < k)%N -> a1 ord0 i = a2 ord0 i) ->
  (forall i : 'I_n, (i < k)%N -> b1 ord0 i = b2 ord0 i) -> (bk1 = bk2) ->
  ytilded_mx k c1 a1 b1 bk1 = ytilded_mx k c2 a2 b2 bk2.
Proof.
move=> Hc Ha Hb Hbk.
by rewrite /ytilded_mx /ytilded; apply f_equal2; [apply dotmulB0_mx_eq|].
Qed.

Lemma ytildes_mx_eq (k : 'I_n) (c1 : T) (a1 : 'rV_n) (c2 : T) (a2 : 'rV_n) :
  c1 = c2 -> (forall i : 'I_n, (i < k)%N -> a1 ord0 i = a2 ord0 i) ->
  ytildes_mx k c1 a1 = ytildes_mx k c2 a2.
Proof.
by move=> Hc Ha; rewrite /ytildes_mx /ytildes; apply f_equal, dotmulB0_mx_eq.
Qed.

Definition cholesky_spec_mx (A R : 'M_n) : Prop :=
  (forall (j i : 'I_n),
     (i < j)%N ->
     (R i j = ytilded_mx i (A i j) (row i R^T) (row j R^T) (R i i)))
  /\ (forall (j : 'I_n),
        (R j j = ytildes_mx j (A j j) (row j R^T))).

(** *** Loop invariants. *)

Definition outer_loop_inv (A R : 'M_n) j : Prop :=
  (forall (j' i' : 'I_n),
     (j' < j)%N ->
     (i' < j')%N ->
     (R j' i' = ytilded_mx i' (A i' j') (row i' R) (row j' R) (R i' i')))
  /\ (forall (j' : 'I_n),
        (j' < j)%N ->
        (R j' j' = ytildes_mx j' (A j' j') (row j' R))).

Definition inner_loop_inv (A R : 'M_n) j i : Prop :=
  outer_loop_inv A R j /\
  (forall (j' i' : 'I_n),
        nat_of_ord j' = j ->
        (i' < i)%N ->
        (i' < j)%N ->
        (R j' i' = ytilded_mx i' (A i' j') (row i' R) (row j' R) (R i' i'))).

Global Instance succ0_correct_ord : succ0_correct ord n.
Proof. by move=> i H; rewrite /nat_of /nat_of_ord inordK. Qed.

Global Instance I0_correct_ord : I0_correct ord n.
Proof. done. Qed.

Global Instance nat_of_correct_ord : nat_of_correct ord n.
Proof. apply ord_inj. Qed.

Lemma inner_loop_correct (A R : 'M_n) (j : 'I_n) :
  inner_loop_inv A R j 0 -> inner_loop_inv A (inner_loop_mx j A R) j n.
Proof.
move=> H; cut (inner_loop_inv A (inner_loop_mx j A R) j j).
{ by move=> {H} [Ho Hi]; split; [|move=> j' i' Hj' _ Hi'; apply Hi]. }
rewrite /inner_loop_mx /inner_loop /nat_of /nat_of_ord.
set f := fun _ _ => _.
set P := fun i s => inner_loop_inv A s j i; rewrite -/(P _ _).
apply iteri_ord_ind => //.
{ apply /ltnW /(ltn_ord j). }
move=> i R' _ [Ho Hi]; split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
{ rewrite store_mx_lt1 // (proj1 Ho _ _ Hj' Hi').
  apply ytilded_mx_eq => // [i''|i''|]; try rewrite 2!mxE.
  { by rewrite store_mx_lt1 //; apply (ltn_trans Hi'). }
  { by rewrite store_mx_lt1. }
  by rewrite store_mx_lt1 //; apply (ltn_trans Hi'). }
{ rewrite store_mx_lt1 // (proj2 Ho _ Hj').
  by apply ytildes_mx_eq => // i''; rewrite 2!mxE store_mx_lt1. }
move=> j' i' Hj' Hi' Hi'j; case (ltnP i' i) => Hii'.
{ rewrite store_mx_lt2 // (Hi _ _ Hj' Hii' Hi'j).
  apply ytilded_mx_eq => // [i'' Hi''|i'' Hi''|]; try rewrite 2!mxE.
  { by rewrite store_mx_lt1. }
  { by rewrite store_mx_lt2 //; apply ltn_trans with i'. }
  by rewrite store_mx_lt2. }
have Hi'i : nat_of_ord i' = i.
{ apply anti_leq; rewrite Hii' Bool.andb_true_r -ltnS //. }
rewrite store_mx_eq //.
have Hini : inord i = i'; [by rewrite -Hi'i inord_val|].
have Hinj : inord j = j'; [by rewrite -Hj' inord_val|].
move: Hini Hinj; rewrite !inord_val => <- <-; apply ytilded_mx_eq => //.
{ by move=> i''' Hi'''; rewrite 2!mxE store_mx_lt2. }
{ by move=> i''' Hi'''; rewrite 2!mxE store_mx_lt2. }
by rewrite store_mx_lt1 //; move: Hi'i; rewrite /nat_of_ord => <-.
Qed.

Lemma outer_loop_correct (A R : 'M_n) : outer_loop_inv A (outer_loop_mx A R) n. 
Proof.
rewrite /outer_loop_mx /outer_loop.
set f := fun _ _ => _.
set P := fun i s => outer_loop_inv A s i; rewrite -/(P _ _).
apply iteri_ord_ind => // j R' _ H.
have Hin_0 : inner_loop_inv A R' j 0; [by []|].
have Hin_n := inner_loop_correct Hin_0.
split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
{ case (ltnP j' j) => Hjj'.
  { rewrite store_mx_lt1 // (proj1 (proj1 Hin_n) _ _ Hjj' Hi').
    apply ytilded_mx_eq => // [i''|i''|]; try rewrite 2!mxE.
    { by rewrite store_mx_lt1 //; apply (ltn_trans Hi'). }
    { by rewrite store_mx_lt1. }
    by rewrite store_mx_lt1 //; apply (ltn_trans Hi'). }
  have Hj'j : nat_of_ord j' = j.
  { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
  have Hi'j : (i' < j)%N by rewrite -Hj'j.
  rewrite store_mx_lt2 // (proj2 Hin_n _ _ Hj'j (ltn_ord i') Hi'j).
  apply ytilded_mx_eq => // [i'' Hi''|i'' Hi''|]; try rewrite 2!mxE.
  { by rewrite store_mx_lt1. }
  { by rewrite store_mx_lt2 //; move: Hi'j; apply ltn_trans. }
  by rewrite store_mx_lt2. }
case (ltnP j' j) => Hjj'.
{ rewrite store_mx_lt2 // (proj2 (proj1 Hin_n) _ Hjj').
  apply ytildes_mx_eq => // j''; try rewrite 2!mxE.
  by rewrite store_mx_lt1. }
have Hj'j : nat_of_ord j' = j.
{ by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
have Hinjj' : inord j = j'; [by rewrite -Hj'j inord_val|].
rewrite store_mx_eq //.
move: Hinjj'; rewrite inord_val => <-; apply ytildes_mx_eq => // i'' Hi''.
by rewrite 2!mxE store_mx_lt2.
Qed.

(** *** The implementation satisfies the specification above. *)

Lemma cholesky_correct (A : 'M[T]_n) : cholesky_spec_mx A (cholesky_mx A)^T.
Proof.
split; [move=> j i Hij|move=> j]; rewrite !mxE.
{ replace ((cholesky_mx A) j i)
  with (ytilded_mx i (A i j)
                   (row i (cholesky_mx A)) (row j (cholesky_mx A))
                   ((cholesky_mx A) i i)).
  { by apply /ytilded_mx_eq => // i' Hi'; rewrite !mxE. }
  by apply sym_eq, outer_loop_correct; [apply ltn_ord|]. }
replace ((cholesky_mx A) j j)
with (ytildes_mx j (A j j) (row j (cholesky_mx A))).
{ by apply ytildes_mx_eq => // i' Hi'; rewrite !mxE. }
by apply sym_eq, outer_loop_correct, ltn_ord.
Qed.

End Proof.

End Inst_ssr_matrix.

(** *** And this spec corresponds to the one in cholesky.v. *)

Section Inst_ssr_matrix_float_infnan.

Context {n' : nat}.
Let n := n'.+1.

Variable fs : Float_infnan_spec.

Instance add_infnan : add (FI fs) := @fiplus fs.
Instance mul_infnan : mul (FI fs) := @fimult fs.
Instance sqrt_infnan : sqrt (FI fs) := @fisqrt fs.
Instance div_infnan : div (FI fs) := @fidiv fs.
Instance opp_infnan : opp (FI fs) := @fiopp fs.
Instance zero_infnan : zero (FI fs) := @FI0 fs.
Instance one_infnan : one (FI fs) := @FI1 fs.

Lemma dotmulB0_correct k (c : FI fs) (a b : 'rV_n) :
  dotmulB0_mx k c a b = stilde_infnan c
                                      [ffun i : 'I_k => a ord0 (inord i)]
                                      [ffun i : 'I_k => b ord0 (inord i)].
Proof.
case: k => //= k Hk; elim: k Hk c a b => //= k IHk Hk c a b.
pose a' := \row_(i < n) a ord0 (inord (lift ord0 i)).
pose b' := \row_(i < n) b ord0 (inord (lift ord0 i)).
rewrite (@fsum_l2r_rec_eq _ _ _ _ _ _
  [ffun i : 'I_k => (- (a' ord0 (inord i) * b' ord0 (inord i)))%C] erefl).
{ rewrite (IHk (ltnW Hk)).
  by apply stilde_infnan_eq => [|i|i]; rewrite !ffunE // mxE /=;
    do 3 apply f_equal; apply inordK, (ltn_trans (ltn_ord i)), ltnW. }
by move=> i; rewrite !ffunE !mxE /=; apply f_equal, f_equal2;
  do 3 apply f_equal; apply sym_eq, inordK, (ltn_trans (ltn_ord i)), ltnW.
Qed.

Lemma ytilded_correct k (c : FI fs) (a b : 'rV_n) (bk : FI fs) :
  ytilded_mx k c a b bk = ytilded_infnan c
                                         [ffun i : 'I_k => a ord0 (inord i)]
                                         [ffun i : 'I_k => b ord0 (inord i)]
                                         bk.
Proof.
rewrite /ytilded_mx /ytilded /ytilded_infnan; apply f_equal2 => //.
apply dotmulB0_correct.
Qed.

Lemma ytildes_correct k (c : FI fs) (a : 'rV_n) :
  ytildes_mx k c a = ytildes_infnan c [ffun i : 'I_k => a ord0 (inord i)].
Proof.
rewrite /ytildes_mx /ytildes /ytildes_infnan; apply f_equal => //.
apply dotmulB0_correct.
Qed.

Lemma cholesky_spec_correct (A R : 'M_n) :
  cholesky_spec_mx A R -> cholesky_spec_infnan A R.
Proof.
move=> H; split.
{ move=> j i Hij; rewrite (proj1 H) // ytilded_correct /ytilded_infnan.
  by apply f_equal2=>//; apply stilde_infnan_eq=>// k; rewrite !ffunE !mxE. }
move=> j; rewrite (proj2 H) ytildes_correct /ytildes_infnan; apply f_equal.
by apply stilde_infnan_eq=>// i; rewrite !ffunE !mxE.
Qed.

(** *** Which enables to restate corollaries from cholesky.v. *)

(** If [A] contains no infinity or NaN, then [MFI2F A] = [A] and
    [posdef (MF2R (MFI2F A))] means that [A] is positive definite. *)
Lemma corollary_2_4_with_c_upper_bound :
  4 * INR n.+1 * eps fs < 1 ->
  forall A : 'M[FI fs]_n, MF2R (MFI2F A^T) = MF2R (MFI2F A) ->
  (forall i : 'I_n, 0 <= (MFI2F A) i i) ->
  forall maxdiag : R, (forall i : 'I_n, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma.gamma fs (2 * n.+1) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n * (2 * INR n.+1 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FI fs]_n,
  ((forall i j : 'I_n, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n, (MFI2F At) i i <= (MFI2F A) i i - c)) ->
  let R := cholesky_mx At in
  (forall i, (0 < (MFI2F R) i i)%Re) ->
  posdef (MF2R (MFI2F A)).
Proof.
move=> H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt R HAR.
apply corollary_2_4_with_c_upper_bound_infnan with maxdiag c At R^T;
  try assumption; split; [|by move=> i; move: (HAR i); rewrite !mxE].
apply cholesky_spec_correct, cholesky_correct.
Qed.

End Inst_ssr_matrix_float_infnan.
