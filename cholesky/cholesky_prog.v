Require Import Reals.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype finfun matrix.
From CoqEAL_refinements Require Import refinements.
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix cholesky cholesky_infnan.

(** * Application: program for Cholesky decomposition *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Refinements.Op.

(** ** Part 0: Definition of operational type classes *)

(** for cholesky *)
Class sqrt T := sqrt_op : T -> T.
Class store_class A I B :=
  store : forall (m n : nat), B m n -> I m -> I n -> A -> B m n.
Class dotmulB0_class A I B :=
  dotmulB0 : forall n : nat, I n -> A -> B 1%nat n -> B 1%nat n -> A.

(** for cholesky-based tactic, including up/d(ow)n-rounded operations *)
Class map_mx_class mx := map_mx :
  forall {T T'} {m n : nat},
  (T -> T') -> mx T m n -> mx T' m n.
Class addup_class B := addup : B -> B -> B.
Class mulup_class B := mulup : B -> B -> B.
Class divup_class B := divup : B -> B -> B.
Class nat2Fup_class B := nat2Fup : nat -> B.
Class subdn_class B := subdn : B -> B -> B.

(** ** Part 1: Generic programs *)

Section generic_cholesky.

(** *** 1.1 Cholesky *)

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

(** *** 1.2 Reflexive tactic *)

Context `{!heq (mx T)}.
Context `{!transpose_class (mx T)}.

Definition is_sym (A : mx T n n) : bool := (A^T == A)%HC.

Definition foldl_diag T' f (z : T') A :=
  iteri_ord n (fun i z => f z (fun_of_matrix A i i)) z.

Definition all_diag f A := foldl_diag (fun b c => b && f c) true A.

Context `{!leq T}.

Definition noneg_diag := all_diag (fun x => 0 <= x)%C.

Context `{!lt T}.

Definition pos_diag := all_diag (fun x => 0 < x)%C.

Definition max x y := if (x <= y)%C then y else x.

Definition max_diag A := foldl_diag max 0%C A.

Definition map_diag f A :=
  iteri_ord n (fun i A' => store A' i i (f (fun_of_matrix A i i))) A.

Context `{!addup_class T, !mulup_class T, !divup_class T}.
Context `{!nat2Fup_class T, !subdn_class T}.

Definition tr_up A := foldl_diag addup 0%C A.

(* overapproximations of eps and eta *)
Variables eps eta : T.

(* [compute_c n A maxdiag] overapproximates
   /2 gamma (2 (n + 1)) \tr A + 4 eta n * (2 (n + 1) + maxdiag) *)
Definition compute_c_aux (A : mx T n n) (maxdiag : T) : T :=
let np1 := nat2Fup n.+1 in
let dnp1 := nat2Fup (2 * n.+1)%N in
let tnp1 := mulup dnp1 eps in
let g := divup (mulup np1 eps) (- (addup tnp1 (-1%C)))%C in
addup
  (mulup g (tr_up A))
  (mulup
    (mulup (mulup (nat2Fup 4) eta) (nat2Fup n))
    (addup dnp1 maxdiag)).

Variable is_finite : T -> bool.

Definition compute_c (A : mx T n n) :
  option T :=
  let nem1 := addup (mulup ((nat2Fup (2 * n.+1)%N)) eps) (-1%C)%C in
  if is_finite nem1 && (nem1 < 0)%C then
    let c := compute_c_aux A (max_diag A) in
    if is_finite c then Some c else None
  else None.

(* check that n is not too large *)
Definition test_n n'' : bool :=
  let f := mulup (mulup (nat2Fup 4%N) (nat2Fup n''.+1)) eps in
  is_finite f && (f < 1)%C.

Definition posdef_check (A : mx T n n) : bool :=
test_n n && is_sym A && noneg_diag A &&
  (match compute_c A with
     | None => false
     | Some c =>
       let A' := map_diag (fun x => subdn x c) A in
       let R := cholesky A' in
       all_diag is_finite R && pos_diag R
   end).

Definition posdef_check_itv (A : mx T n n) (r : T) : bool :=
is_finite r && (0 <= r)%C &&
  let nm := mulup (nat2Fup n) r in
  let A' := map_diag (fun x => subdn x nm) A in
  posdef_check A'.

Context `{!map_mx_class mx}.

Variables (F : Type) (F2FI : F -> T).

Definition posdef_check_F (A : mx F n n) : bool := posdef_check (map_mx F2FI A).

Definition posdef_check_itv_F (A : mx F n n) (r : F) : bool :=
  posdef_check_itv (map_mx F2FI A) (F2FI r).

End generic_cholesky.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_cholesky.

(** *** Proof-oriented definitions *)

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, !div T, !mul T, !sqrt T}.

Global Instance fun_of_ssr : fun_of T ordinal (matrix T) :=
  fun m n => @matrix.fun_of_matrix T m n.

Global Instance row_ssr : row_class ordinal (matrix T) := @matrix.row T.

Global Instance store_ssr : store_class T ordinal (matrix T) :=
  fun m n (M : 'M[T]_(m, n)) (i : 'I_m) (j : 'I_n) v =>
  \matrix_(i', j')
    if ((nat_of_ord i' == i) && (nat_of_ord j' == j))%N then v else M i' j'.

Fixpoint fsum_l2r_rec n (c : T) : T ^ n -> T :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (c + (a ord0))%C [ffun i => a (lift ord0 i)]
  end.

Global Instance dotmulB0_ssr : dotmulB0_class T ordinal (matrix T) :=
  fun n =>
    match n with
      | 0%N => fun i c a b => c
      | n'.+1 => fun i c a b =>
        fsum_l2r_rec c
        [ffun k : 'I_i => (- ((a ord0 (inord k)) * (b ord0 (inord k))))%C]
    end.

Context {n : nat}.

(* FIXME: these definition may be unnecessary *)

Definition ytilded_ssr : 'I_n.+1 -> T -> 'M[T]_(1, n.+1) -> 'M[T]_(1, n.+1) -> T -> T :=
  ytilded.

Definition ytildes_ssr : 'I_n.+1 -> T -> 'M[T]_(1, n.+1) -> T :=
  ytildes.

Definition iteri_ord_ssr : forall T, nat -> ('I_n.+1 -> T -> T) -> T -> T :=
  iteri_ord.

Definition inner_loop_ssr : 'I_n.+1 -> 'M[T]_n.+1 -> 'M[T]_n.+1 -> 'M[T]_n.+1 :=
  inner_loop.

Definition outer_loop_ssr : 'M[T]_n.+1 -> 'M[T]_n.+1 -> 'M[T]_n.+1 :=
  outer_loop.

Definition cholesky_ssr : 'M[T]_n.+1 -> 'M[T]_n.+1 :=
  cholesky.

(** *** Proofs *)

Lemma store_ssr_eq (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  nat_of_ord i' = i -> nat_of_ord j' = j -> (store_ssr M i j v) i' j' = v.
Proof. by rewrite /nat_of_ssr mxE => -> ->; rewrite !eq_refl. Qed.

Lemma store_ssr_lt1 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (nat_of_ord i' < i)%N -> (store_ssr M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE (ltn_eqF Hi). Qed.

Lemma store_ssr_lt2 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (nat_of_ord j' < j)%N -> (store_ssr M i j v) i' j' = M i' j'.
Proof. by move=> Hj; rewrite mxE (ltn_eqF Hj) Bool.andb_false_r. Qed.

Lemma store_ssr_gt1 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (i < nat_of_ord i')%N -> (store_ssr M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE eq_sym (ltn_eqF Hi). Qed.

Lemma store_ssr_gt2 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (j < nat_of_ord j')%N -> (store_ssr M i j v) i' j' = M i' j'.
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

Lemma dotmulB0_ssr_eq k (i : 'I_k)
      (c1 : T) (a1 b1 : 'rV_k)
      (c2 : T) (a2 b2 : 'rV_k) :
  c1 = c2 -> (forall j : 'I_k, (j < i)%N -> a1 ord0 j = a2 ord0 j) ->
  (forall j : 'I_k, (j < i)%N -> b1 ord0 j = b2 ord0 j) ->
  dotmulB0_ssr i c1 a1 b1 = dotmulB0_ssr i c2 a2 b2.
Proof.
case: k i c1 a1 b1 c2 a2 b2 => //= k i c1 a1 b1 c2 a2 b2 Hc Ha Hb.
apply fsum_l2r_rec_eq => // j; rewrite !ffunE Ha ?Hb //;
  (rewrite inordK; [|apply (ltn_trans (ltn_ord j))]); apply ltn_ord.
Qed.

Lemma ytilded_ssr_eq (k : 'I_n.+1)
      (c1 : T) (a1 b1 : 'rV_n.+1) (bk1 : T)
      (c2 : T) (a2 b2 : 'rV_n.+1) (bk2 : T) :
  c1 = c2 -> (forall i : 'I_n.+1, (i < k)%N -> a1 ord0 i = a2 ord0 i) ->
  (forall i : 'I_n.+1, (i < k)%N -> b1 ord0 i = b2 ord0 i) -> (bk1 = bk2) ->
  ytilded_ssr k c1 a1 b1 bk1 = ytilded_ssr k c2 a2 b2 bk2.
Proof.
move=> Hc Ha Hb Hbk.
by rewrite /ytilded_ssr /ytilded; apply f_equal2; [apply dotmulB0_ssr_eq|].
Qed.

Lemma ytildes_ssr_eq (k : 'I_n.+1) (c1 : T) (a1 : 'rV_n.+1) (c2 : T) (a2 : 'rV_n.+1) :
  c1 = c2 -> (forall i : 'I_n.+1, (i < k)%N -> a1 ord0 i = a2 ord0 i) ->
  ytildes_ssr k c1 a1 = ytildes_ssr k c2 a2.
Proof.
by move=> Hc Ha; rewrite /ytildes_ssr /ytildes; apply f_equal, dotmulB0_ssr_eq.
Qed.

Definition cholesky_spec_ssr (A R : 'M_n.+1) : Prop :=
  (forall (j i : 'I_n.+1),
     (i < j)%N ->
     (R i j = ytilded_ssr i (A i j) (row i R^T) (row j R^T) (R i i)))
  /\ (forall (j : 'I_n.+1),
        (R j j = ytildes_ssr j (A j j) (row j R^T))).

(** *** Loop invariants *)

Definition outer_loop_inv (A R : 'M_n.+1) j : Prop :=
  (forall (j' i' : 'I_n.+1),
     (j' < j)%N ->
     (i' < j')%N ->
     (R j' i' = ytilded_ssr i' (A i' j') (row i' R) (row j' R) (R i' i')))
  /\ (forall (j' : 'I_n.+1),
        (j' < j)%N ->
        (R j' j' = ytildes_ssr j' (A j' j') (row j' R))).

Definition inner_loop_inv (A R : 'M_n.+1) j i : Prop :=
  outer_loop_inv A R j /\
  (forall (j' i' : 'I_n.+1),
        nat_of_ord j' = j ->
        (i' < i)%N ->
        (i' < j)%N ->
        (R j' i' = ytilded_ssr i' (A i' j') (row i' R) (row j' R) (R i' i'))).

Lemma inner_loop_correct (A R : 'M_n.+1) (j : 'I_n.+1) :
  inner_loop_inv A R j 0 -> inner_loop_inv A (inner_loop_ssr j A R) j n.+1.
Proof.
move=> H; cut (inner_loop_inv A (inner_loop_ssr j A R) j j).
{ by move=> {H} [Ho Hi]; split; [|move=> j' i' Hj' _ Hi'; apply Hi]. }
rewrite /inner_loop_ssr /inner_loop /nat_of /nat_of_ssr.
set P := fun i s => inner_loop_inv A s j i; rewrite -/(P _ _).
apply iteri_ord_ind => //.
{ apply /ltnW /(ltn_ord j). }
move=> i R' _ [Ho Hi]; split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
{ rewrite store_ssr_lt1 // (proj1 Ho _ _ Hj' Hi').
  apply ytilded_ssr_eq => // [i''|i''|]; try rewrite 2!mxE.
  { by rewrite store_ssr_lt1 //; apply (ltn_trans Hi'). }
  { by rewrite store_ssr_lt1. }
  by rewrite store_ssr_lt1 //; apply (ltn_trans Hi'). }
{ rewrite store_ssr_lt1 // (proj2 Ho _ Hj').
  by apply ytildes_ssr_eq => // i''; rewrite 2!mxE store_ssr_lt1. }
move=> j' i' Hj' Hi' Hi'j; case (ltnP i' i) => Hii'.
{ rewrite store_ssr_lt2 // (Hi _ _ Hj' Hii' Hi'j).
  apply ytilded_ssr_eq => // [i'' Hi''|i'' Hi''|]; try rewrite 2!mxE.
  { by rewrite store_ssr_lt1. }
  { by rewrite store_ssr_lt2 //; apply ltn_trans with i'. }
  by rewrite store_ssr_lt2. }
have Hi'i : nat_of_ord i' = i.
{ apply anti_leq; rewrite Hii' Bool.andb_true_r -ltnS //. }
rewrite store_ssr_eq //.
have Hini : inord i = i'; [by rewrite -Hi'i inord_val|].
have Hinj : inord j = j'; [by rewrite -Hj' inord_val|].
move: Hini Hinj; rewrite !inord_val => <- <-; apply ytilded_ssr_eq => //.
{ by move=> i''' Hi'''; rewrite 2!mxE store_ssr_lt2. }
{ by move=> i''' Hi'''; rewrite 2!mxE store_ssr_lt2. }
by rewrite store_ssr_lt1 //; move: Hi'i; rewrite /nat_of_ord => <-.
Qed.

Lemma outer_loop_correct (A R : 'M_n.+1) : outer_loop_inv A (outer_loop_ssr A R) n.+1. 
Proof.
rewrite /outer_loop_ssr /outer_loop.
set P := fun i s => outer_loop_inv A s i; rewrite -/(P _ _).
apply iteri_ord_ind => // j R' _ H.
have Hin_0 : inner_loop_inv A R' j 0; [by []|].
have Hin_n := inner_loop_correct Hin_0.
split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
{ case (ltnP j' j) => Hjj'.
  { rewrite store_ssr_lt1 // (proj1 (proj1 Hin_n) _ _ Hjj' Hi').
    apply ytilded_ssr_eq => // [i''|i''|]; try rewrite 2!mxE.
    { by rewrite store_ssr_lt1 //; apply (ltn_trans Hi'). }
    { by rewrite store_ssr_lt1. }
    by rewrite store_ssr_lt1 //; apply (ltn_trans Hi'). }
  have Hj'j : nat_of_ord j' = j.
  { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
  have Hi'j : (i' < j)%N by rewrite -Hj'j.
  rewrite store_ssr_lt2 // (proj2 Hin_n _ _ Hj'j (ltn_ord i') Hi'j).
  apply ytilded_ssr_eq => // [i'' Hi''|i'' Hi''|]; try rewrite 2!mxE.
  { by rewrite store_ssr_lt1. }
  { by rewrite store_ssr_lt2 //; move: Hi'j; apply ltn_trans. }
  by rewrite store_ssr_lt2. }
case (ltnP j' j) => Hjj'.
{ rewrite store_ssr_lt2 // (proj2 (proj1 Hin_n) _ Hjj').
  apply ytildes_ssr_eq => // j''; try rewrite 2!mxE.
  by rewrite store_ssr_lt1. }
have Hj'j : nat_of_ord j' = j.
{ by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
have Hinjj' : inord j = j'; [by rewrite -Hj'j inord_val|].
rewrite store_ssr_eq //.
move: Hinjj'; rewrite inord_val => <-; apply ytildes_ssr_eq => // i'' Hi''.
by rewrite 2!mxE store_ssr_lt2.
Qed.

(** *** The implementation satisfies the specification above. *)

Lemma cholesky_correct (A : 'M[T]_n.+1) : cholesky_spec_ssr A (cholesky_ssr A)^T.
Proof.
split; [move=> j i Hij|move=> j]; rewrite !mxE.
{ replace ((cholesky_ssr A) j i)
  with (ytilded_ssr i (A i j)
                   (row i (cholesky_ssr A)) (row j (cholesky_ssr A))
                   ((cholesky_ssr A) i i)).
  { by apply /ytilded_ssr_eq => // i' Hi'; rewrite !mxE. }
  by apply sym_eq, outer_loop_correct; [apply ltn_ord|]. }
replace ((cholesky_ssr A) j j)
with (ytildes_ssr j (A j j) (row j (cholesky_ssr A))).
{ by apply ytildes_ssr_eq => // i' Hi'; rewrite !mxE. }
by apply sym_eq, outer_loop_correct, ltn_ord.
Qed.

End theory_cholesky. (* TO TIDY: Part 3: Parametricity: Section parametricity. *)

(** *** And this spec corresponds to the one in cholesky.v. *)
Section inst_ssr_matrix_float_infnan.

Context {fs : Float_infnan_spec}.

Global Instance add_instFI : add (FI fs) := @fiplus fs.
Global Instance mul_instFI : mul (FI fs) := @fimult fs.
Global Instance sqrt_instFI : sqrt (FI fs) := @fisqrt fs.
Global Instance div_instFI : div (FI fs) := @fidiv fs.
Global Instance opp_instFI : opp (FI fs) := @fiopp fs.
Global Instance zero_instFI : zero (FI fs) := @FI0 fs.
Global Instance one_instFI : one (FI fs) := @FI1 fs.
(** The following instances aren't used in this file but kept for convenience *)
Global Instance eq_instFI : eq (FI fs) := @fieq fs.
Global Instance leq_instFI : leq (FI fs) := @file fs.
Global Instance lt_instFI : lt (FI fs) := @filt fs.

Context {n' : nat}.
Let n := n'.+1.

Lemma dotmulB0_correct k (c : FI fs) (a b : 'rV_n) :
  dotmulB0_ssr k c a b = stilde_infnan c
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
  ytilded_ssr k c a b bk = ytilded_infnan c
                                         [ffun i : 'I_k => a ord0 (inord i)]
                                         [ffun i : 'I_k => b ord0 (inord i)]
                                         bk.
Proof.
rewrite /ytilded_ssr /ytilded /ytilded_infnan; apply f_equal2 => //.
apply dotmulB0_correct.
Qed.

Lemma ytildes_correct k (c : FI fs) (a : 'rV_n) :
  ytildes_ssr k c a = ytildes_infnan c [ffun i : 'I_k => a ord0 (inord i)].
Proof.
rewrite /ytildes_ssr /ytildes /ytildes_infnan; apply f_equal => //.
apply dotmulB0_correct.
Qed.

Lemma cholesky_spec_correct (A R : 'M_n) :
  cholesky_spec_ssr A R -> cholesky_spec_infnan A R.
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
  let R := cholesky_ssr At in
  (forall i, (0 < (MFI2F R) i i)%Re) ->
  posdef (MF2R (MFI2F A)).
Proof.
move=> H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt R HAR.
apply corollary_2_4_with_c_upper_bound_infnan with maxdiag c At R^T;
  try assumption; split; [|by move=> i; move: (HAR i); rewrite !mxE].
apply cholesky_spec_correct, cholesky_correct.
Qed.

End inst_ssr_matrix_float_infnan.
