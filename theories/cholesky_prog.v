Require Import Reals BigZ Psatz ROmega BigQ.
From Flocq Require Import Fcore_Raux Fcore_defs Fcore_digits.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From CoqEAL Require Import hrel.
From CoqEAL Require Import param refinements (*seqmx*).
From Interval Require Import Interval_xreal.
From Interval Require Import Interval_definitions.
From Interval Require Import Interval_specific_ops.
Require Import seqmx seqmx_complements.
Require Import Rstruct misc.
Require Import coqinterval_infnan zulp.
Require Import iteri_ord float_infnan_spec real_matrix cholesky cholesky_infnan.
Require Import gamma fsum.

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
Class sqrt_of T := sqrt_op : T -> T.

Class dotmulB0_of A I B :=
  dotmulB0_op : forall n : nat, I n -> A -> B 1%nat n -> B 1%nat n -> A.

(** for cholesky-based tactic, including up/d(ow)n-rounded operations *)
Class addup_class B := addup : B -> B -> B.
Class mulup_class B := mulup : B -> B -> B.
Class divup_class B := divup : B -> B -> B.
Class nat2Fup_class B := nat2Fup : nat -> B.
Class subdn_class B := subdn : B -> B -> B.

(** ** Part 1: Generic programs *)

Section generic_cholesky.

(** *** 1.1 Cholesky *)

Context {T : Type} {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!zero_of T, !one_of T, !add_of T, !opp_of T, !mul_of T, !div_of T, !sqrt_of T}.
Context `{!fun_of_of T ord (mx T), !row_of ord (mx T), !store_of T ord (mx T), !dotmulB0_of T ord (mx T)}.
Context {n : nat}.
Context `{!I0_class ord n, !succ0_class ord n, !nat_of_class ord n}.

Definition ytilded (k : ord n) (c : T) a b bk := (dotmulB0_op k c a b %/ bk)%C.

Definition ytildes (k : ord n) c a := (sqrt_op (dotmulB0_op k c a a)).

(* note: R is transposed with respect to cholesky.v *)
Definition inner_loop j A R :=
  iteri_ord (nat_of j)
            (fun i R => store_op R j i (ytilded i (fun_of_op A i j)
                                                (row_op i R) (row_op j R)
                                                (fun_of_op R i i)))
            R.

(* note: R is transposed with respect to cholesky.v *)
Definition outer_loop A R :=
  iteri_ord n
            (fun j R =>
               let R := inner_loop j A R in
               store_op R j j (ytildes j (fun_of_op A j j)
                                       (row_op j R)))
            R.

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky A := outer_loop A A.

(** *** 1.2 Reflexive tactic *)

Context `{!heq_of (mx T), !trmx_of (mx T)}.

Definition is_sym (A : mx T n n) : bool := (A^T == A)%HC.

Definition foldl_diag T' f (z : T') A :=
  iteri_ord n (fun i z => f z (fun_of_op A i i)) z.

Definition all_diag f A := foldl_diag (fun b c => b && f c) true A.

Context `{!leq_of T}.

Definition noneg_diag := all_diag (fun x => 0 <= x)%C.

Context `{!lt_of T}.

Definition pos_diag := all_diag (fun x => 0 < x)%C.

Definition max (x y : T) := if (x <= y)%C then y else x.

Definition max_diag A := foldl_diag max 0%C A.

Definition map_diag f A :=
  iteri_ord n (fun i A' => store_op A' i i (f (fun_of_op A i i))) A.

Context `{!addup_class T, !mulup_class T, !divup_class T}.
Context `{!nat2Fup_class T, !subdn_class T}.

Definition tr_up A := foldl_diag addup 0%C A.

(** over-approximations of [eps] and [eta] *)
Variables eps eta : T.

(** [compute_c_aux (A : 'M_n) maxdiag] over-approximates
[/2 * gamma (2 * (n + 1)) * \tr A + 4 * eta * n * (2 * (n + 1) + maxdiag)] *)
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

(** [test_n] checks that [n] is not too large *)
Definition test_n n : bool :=
  let f := mulup (mulup (nat2Fup 4%N) (nat2Fup n.+1)) eps in
  is_finite f && (f < 1)%C.

Definition posdef_check (A : mx T n n) : bool :=
[&& test_n n, is_sym A, noneg_diag A &
  (match compute_c A with
     | None => false
     | Some c =>
       let A' := map_diag (fun x => subdn x c) A in
       let R := cholesky A' in
       all_diag is_finite R && pos_diag R
   end)].

Definition posdef_check_itv (A : mx T n n) (r : T) : bool :=
[&& is_finite r, (0 <= r)%C &
  let nm := mulup (nat2Fup n) r in
  let A' := map_diag (fun x => subdn x nm) A in
  posdef_check A'].

End generic_cholesky.

Section seqmx_cholesky.

(** *** 1.3 Generic defs for seqmx

- instantiation of dotmulB0, store, map_mx, eq, transpose
- a few support lemmas
 *)

Context {T : Type}.
Context `{!zero_of T, !one_of T, !add_of T, !opp_of T, !div_of T, !mul_of T, !sqrt_of T}.

Fixpoint stilde_seqmx k (c : T) a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => stilde_seqmx k (c + (- (a1 * b1)))%C a2 b2
  end.

Global Instance dotmulB0_seqmx : dotmulB0_of T ord_instN hseqmx :=
  fun n k c a b => stilde_seqmx k c (head [::] a) (head [::] b).

Context {n : nat}.

Definition ytilded_seqmx :
  ord_instN n.+1 -> T -> hseqmx 1%N n.+1 -> hseqmx 1%N n.+1 -> T -> T :=
  ytilded (T := T).

Definition ytildes_seqmx : ord_instN n.+1 -> T -> hseqmx 1%N n.+1 -> T :=
  ytildes.

Definition cholesky_seqmx : @hseqmx T n.+1 n.+1 -> @hseqmx T n.+1 n.+1 :=
  cholesky.

Definition outer_loop_seqmx :
  @hseqmx T n.+1 n.+1 -> @hseqmx T n.+1 n.+1 -> @hseqmx T n.+1 n.+1 :=
  outer_loop.

Definition inner_loop_seqmx :
  ord_instN n.+1 -> @hseqmx T n.+1 n.+1 -> @hseqmx T n.+1 n.+1 -> @hseqmx T n.+1 n.+1 :=
  inner_loop.

Context `{!eq_of T, !leq_of T, !lt_of T}.

(** Rely on arithmetic operations with directed rounding: *)
Context `{!addup_class T, !mulup_class T, !divup_class T}.
Context `{!nat2Fup_class T, !subdn_class T}.

Variable feps feta : T.

Variable is_finite : T -> bool.

Definition posdef_check_seqmx : @hseqmx T n.+1 n.+1 -> bool :=
  posdef_check feps feta is_finite.

Definition posdef_check_itv_seqmx : @hseqmx T n.+1 n.+1 -> T -> bool :=
  posdef_check_itv feps feta is_finite.

End seqmx_cholesky.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_cholesky.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

Context {T : Type}.
Context `{!zero_of T, !one_of T, !add_of T, !opp_of T, !div_of T, !mul_of T, !sqrt_of T}.

Global Instance fun_of_ssr : fun_of_of T ordinal (matrix T) :=
  fun m n => @matrix.fun_of_matrix T m n.

Global Instance row_ssr : row_of ordinal (matrix T) := @matrix.row T.

Fixpoint fsum_l2r_rec n (c : T) : T ^ n -> T :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (c + (a ord0))%C [ffun i => a (lift ord0 i)]
  end.

Global Instance dotmulB0_ssr : dotmulB0_of T ordinal (matrix T) :=
  fun n =>
    match n with
      | 0%N => fun i c a b => c
      | n'.+1 => fun i c a b =>
        fsum_l2r_rec c
        [ffun k : 'I_i => (- ((a ord0 (inord k)) * (b ord0 (inord k))))%C]
    end.

Context {n : nat}.

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

(** *** Proofs for cholesky-based tactic *)

Definition all_diag_ssr : (T -> bool) -> 'M[T]_n.+1 -> bool :=
  all_diag.

Definition foldl_diag_ssr (T' : Type) : (T' -> T -> T') -> T' -> 'M_n.+1 -> T' :=
  foldl_diag (T' := T').

Definition map_diag_ssr : (T -> T) -> 'M[T]_n.+1 -> 'M[T]_n.+1 :=
  map_diag.

Lemma all_diag_correct f A : all_diag_ssr f A -> forall i, f (A i i).
Proof.
move=> Had i; move: (ltn_ord i) Had.
set P := fun i b => b = true -> f (A i i) = true.
rewrite -/(P i (all_diag_ssr f A)).
rewrite -/(nat_of _); apply iteri_ord_ind_strong_cases.
{ move=> j' s Hj' H j'' Hj''.
  by rewrite /P Bool.andb_true_iff => Hb; elim Hb => Hb' _; apply H. }
by move=> j' s Hj' H; rewrite /P Bool.andb_true_iff => Hb; elim Hb.
Qed.

Lemma foldl_diag_correct (T' : Type) (f : T' -> T -> T') (z : T') (A : 'M_n.+1) :
  forall (P : nat -> T' -> Type),
  (forall (i : 'I_n.+1) z, P i z -> P i.+1 (f z (A i i))) ->
  P O z -> P n.+1 (foldl_diag_ssr f z A).
Proof.
move=> P Hind; rewrite /foldl_diag_ssr /foldl_diag.
apply iteri_ord_ind => // i s Hi HPi; apply Hind.
by move: HPi; rewrite /nat_of /nat_of_ord.
Qed.

Lemma map_diag_correct_ndiag f (A : 'M[T]_n.+1) :
  forall i j : 'I_n.+1, i <> j -> (map_diag_ssr f A) i j = A i j.
Proof.
move=> i j Hij.
rewrite /map_diag_ssr /map_diag /iteri_ord; set f' := fun _ _ => _.
suff H : forall k R i',
           (matrix.fun_of_matrix (@iteri_ord_rec _ _ succ0_ssr _ k i' f' R) i j
            = R i j) => //; elim => // k IHk R i' /=.
rewrite IHk; case (ltnP i' j) => Hi'j; [by rewrite store_ssr_gt2|].
case (ltnP i j) => Hij'.
{ by rewrite store_ssr_lt1 //; apply (leq_trans Hij'). }
case (ltnP i' i) => Hi'i; [by rewrite store_ssr_gt1|].
rewrite store_ssr_lt2 //; move: Hi'i; apply leq_trans.
case (leqP i j) => Hij'' //.
by casetype False; apply Hij, ord_inj, anti_leq; rewrite Hij''.
Qed.

Lemma map_diag_correct_diag f (A : 'M[T]_n.+1) :
  forall i, (map_diag_ssr f A) i i = f (A i i).
Proof.
move=> i; rewrite /map_diag_ssr /map_diag.
set f' := fun _ _ => _.
set P := fun i s => s i i = f (A i i); rewrite -/(P i _).
apply iteri_ord_ind_strong_cases with (i0 := i) => //.
{ move=> j s Hj Hind j' Hj'.
  rewrite /P /f' store_ssr_lt1 //; apply Hind => //; apply ltn_ord. }
{ move=> j s Hj Hind; rewrite /P /f' store_ssr_eq //. }
apply ltn_ord.
Qed.

End theory_cholesky.

Section theory_cholesky_2.

(** *** Proof-oriented definitions, Float_infnan_spec scalars *)

(** This spec corresponds to the one in [cholesky.v]... *)

Context {fs : Float_infnan_spec}.

Global Instance add_instFIS : add_of (FIS fs) := @fiplus fs.
Global Instance mul_instFIS : mul_of (FIS fs) := @fimult fs.
Global Instance sqrt_instFIS : sqrt_of (FIS fs) := @fisqrt fs.
Global Instance div_instFIS : div_of (FIS fs) := @fidiv fs.
Global Instance opp_instFIS : opp_of (FIS fs) := @fiopp fs.
Global Instance zero_instFIS : zero_of (FIS fs) := @FIS0 fs.
Global Instance one_instFIS : one_of (FIS fs) := @FIS1 fs.

Global Instance eq_instFIS : eq_of (FIS fs) := @fieq fs.
Global Instance leq_instFIS : leq_of (FIS fs) := @file fs.
Global Instance lt_instFIS : lt_of (FIS fs) := @filt fs.

Context {n : nat}.

Lemma dotmulB0_correct k (c : FIS fs) (a b : 'rV_n.+1) :
  dotmulB0_ssr k c a b = stilde_infnan c
                                       [ffun i : 'I_k => a ord0 (inord i)] 
                                       [ffun i : 'I_k => b ord0 (inord i)].
Proof.
case: k => //= k Hk; elim: k Hk c a b => //= k IHk Hk c a b.
pose a' := \row_(i < n.+1) a ord0 (inord (lift ord0 i)).
pose b' := \row_(i < n.+1) b ord0 (inord (lift ord0 i)).
rewrite (@fsum_l2r_rec_eq _ _ _ _ _ _
  [ffun i : 'I_k => (- (a' ord0 (inord i) * b' ord0 (inord i)))%C] erefl).
{ rewrite (IHk (ltnW Hk)).
  by apply stilde_infnan_eq => [|i|i]; rewrite !ffunE // mxE /=;
    do 3 apply f_equal; apply inordK, (ltn_trans (ltn_ord i)), ltnW. }
by move=> i; rewrite !ffunE !mxE /=; apply f_equal, f_equal2;
  do 3 apply f_equal; apply sym_eq, inordK, (ltn_trans (ltn_ord i)), ltnW.
Qed.

Lemma ytilded_correct k (c : FIS fs) (a b : 'rV_n.+1) (bk : FIS fs) :
  ytilded_ssr k c a b bk = ytilded_infnan c
                                          [ffun i : 'I_k => a ord0 (inord i)]
                                          [ffun i : 'I_k => b ord0 (inord i)]
                                          bk.
Proof.
rewrite /ytilded_ssr /ytilded /ytilded_infnan; apply f_equal2 => //.
apply dotmulB0_correct.
Qed.

Lemma ytildes_correct k (c : FIS fs) (a : 'rV_n.+1) :
  ytildes_ssr k c a = ytildes_infnan c [ffun i : 'I_k => a ord0 (inord i)].
Proof.
rewrite /ytildes_ssr /ytildes /ytildes_infnan; apply f_equal => //.
apply dotmulB0_correct.
Qed.

Lemma cholesky_spec_correct (A R : 'M[FIS fs]_n.+1) :
  cholesky_spec_ssr A R -> cholesky_spec_infnan A R.
Proof.
move=> H; split.
{ move=> j i Hij; rewrite (proj1 H) // ytilded_correct /ytilded_infnan.
  by apply f_equal2=>//; apply stilde_infnan_eq=>// k; rewrite !ffunE !mxE. }
move=> j; rewrite (proj2 H) ytildes_correct /ytildes_infnan; apply f_equal.
by apply stilde_infnan_eq=>// i; rewrite !ffunE !mxE.
Qed.

(** ... which enables to restate corollaries from [cholesky.v]. *)

(** If [A] contains no infinity or NaN, then [MFI2F A] = [A] and
    [posdef (MF2R (MFI2F A))] means that [A] is positive definite. *)
Lemma corollary_2_4_with_c_upper_bound :
  4 * INR n.+2 * eps fs < 1 ->
  forall A : 'M[FIS fs]_n.+1, MF2R (MFI2F A^T) = MF2R (MFI2F A) ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma.gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FIS fs]_n.+1,
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, (MFI2F At) i i <= (MFI2F A) i i - c)) ->
  let R := cholesky_ssr At in
  (forall i, (0 < (MFI2F R) i i)%Re) ->
  posdef (MF2R (MFI2F A)).
Proof.
move=> H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt R HAR.
apply corollary_2_4_with_c_upper_bound_infnan with maxdiag c At R^T =>//.
split.
- by apply cholesky_spec_correct, cholesky_correct.
- by move=> i; move: (HAR i); rewrite !mxE.
Qed.

End theory_cholesky_2.

Section theory_cholesky_3.

(** *** Proof-oriented definitions, Float_round_up_infnan_spec scalars *)

Context {fs : Float_round_up_infnan_spec}.

Global Instance addup_instFIS : addup_class (FIS (fris fs)) := @fiplus_up fs.
Global Instance mulup_instFIS : mulup_class (FIS (fris fs)) := @fimult_up fs.
Global Instance divup_instFIS : divup_class (FIS (fris fs)) := @fidiv_up fs.
Global Instance nat2Fup_instFI : nat2Fup_class (FIS (fris fs)) :=
  @float_of_nat_up fs.
Global Instance subdn_instFIS : subdn_class (FIS (fris fs)) := @fiminus_down fs.

Global Instance trmx_instFIS_ssr : trmx_of (matrix (FIS fs)) := @trmx (FIS fs).

Context {n : nat}.

Lemma is_sym_correct_aux (A : 'M[FIS fs]_n.+1) :
  is_sym A -> forall i j, fieq (A^T i j) (A i j).
Proof. by move=> H i j; move/forallP/(_ i)/forallP/(_ j) in H. Qed.

Lemma is_sym_correct (A : 'M[FIS fs]_n.+1) :
  is_sym A -> MF2R (MFI2F A^T) = MF2R (MFI2F A).
Proof.
move/is_sym_correct_aux=> H; apply /matrixP=> i j.
move: (H i j); rewrite !mxE; apply fieq_spec.
Qed.

Definition max_diag_ssr (A : 'M[FIS fs]_n.+1) : FIS fs :=
  @max_diag _ _ _ _ fun_of_ssr _ _ succ0_ssr _ A.

Lemma max_diag_correct (A : 'M[FIS fs]_n.+1) : (forall i, finite (A i i)) ->
  forall i, (MFI2F A) i i <= FIS2FS (max_diag_ssr A).
Proof.
move=> HF.
set f := fun m c : FIS fs => if (m <= c)%C then c else m.
move=> i; move: i (ltn_ord i).
set P' := fun j (s : FIS fs) => forall (i : 'I_n.+1), (i < j)%N ->
  (MFI2F A) i i <= FIS2FS s; rewrite -/(P' _ _).
suff : (finite (foldl_diag_ssr f (FIS0 fs) A)
        /\ P' n.+1 (foldl_diag_ssr f (FIS0 fs) A)).
{ by move=> H; elim H. }
set P := fun j s => finite s /\ P' j s; rewrite -/(P _ _).
apply foldl_diag_correct; rewrite /P /P'.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by apply fimax_spec_f. }
  move=> j Hj; case (ltnP j i) => Hji.
  { rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ (Hind' _ Hji)).
    by apply fimax_spec_lel. }
  have H' : j = i.
  { by apply ord_inj, anti_leq; rewrite Hji Bool.andb_true_r. }
  by rewrite H' /f -/(fimax _ _) mxE; apply fimax_spec_ler. }
by split; [apply finite0|].
Qed.

Lemma max_diag_pos (A : 'M[FIS fs]_n.+1) : (forall i, finite (A i i)) ->
  0 <= FIS2FS (max_diag_ssr A).
Proof.
move=> HF.
set f := fun m c : FIS fs => if (m <= c)%C then c else m.
suff : (finite (foldl_diag_ssr f (FIS0 fs) A)
        /\ 0 <= FIS2FS (foldl_diag_ssr f (FIS0 fs) A)).
{ by move=> H; elim H. }
set P := fun (j : nat) s => @finite fs s /\ 0 <= FIS2FS s.
apply foldl_diag_correct with (P0 := P); rewrite /P.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by case (fimax_spec_eq z (A i i)) => H; rewrite /f -/(fimax _ _) H. }
  by rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ Hind'), fimax_spec_lel. }
by split; [apply finite0|rewrite FIS2FS0; right].
Qed.

Definition tr_up_ssr (n : nat) : 'M[FIS fs]_n.+1 -> FIS fs := tr_up.

Lemma tr_up_correct (A : 'M[FIS fs]_n.+1) : finite (tr_up_ssr A) ->
  \tr (MF2R (MFI2F A)) <= FIS2FS (tr_up_ssr A).
Proof.
rewrite /tr_up_ssr /tr_up -/(foldl_diag_ssr _ _ _).
replace (\tr _) with (\sum_(i < n.+1) (FIS2FS (A (inord i) (inord i)) : R));
  [|by apply eq_big => // i _; rewrite !mxE inord_val].
set P := fun j (s : FIS fs) => finite s ->
  (\sum_(i < j) (FIS2FS (A (inord i) (inord i)) : R)) <= FIS2FS s.
rewrite -/(P _ _); apply foldl_diag_correct; rewrite /P.
{ move=> i z Hind Fa; move: (fiplus_up_spec Fa); apply Rle_trans.
  rewrite big_ord_recr /= /GRing.add /= inord_val.
  apply Rplus_le_compat_r, Hind, (fiplus_up_spec_fl Fa). }
move=> _; rewrite big_ord0 FIS2FS0; apply Rle_refl.
Qed.

Definition test_n_ssr : nat -> bool :=
  test_n (fieps fs) (@finite fs).

Lemma test_n_correct : test_n_ssr n.+1 -> 4 * INR n.+2 * eps fs < 1.
Proof.
rewrite /test_n_ssr /test_n; set f := _ (fieps _).
move/andP => [Ff Hf]; have Ffeps := fimult_up_spec_fr Ff.
have Fp := fimult_up_spec_fl Ff.
have Ff4 := fimult_up_spec_fl Fp; have Ffn := fimult_up_spec_fr Fp.
apply (Rle_lt_trans _ (FIS2FS f)).
{ move: (fimult_up_spec Ff); apply Rle_trans, Rmult_le_compat.
  { apply Rmult_le_pos; [lra|apply pos_INR]. }
  { apply eps_pos. }
  { move: (fimult_up_spec Fp); apply Rle_trans, Rmult_le_compat.
    { lra. }
    { apply pos_INR. }
    { move: (float_of_nat_up_spec Ff4); apply Rle_trans=>/=; lra. }
    by move: (float_of_nat_up_spec Ffn); apply Rle_trans; right. }
  apply fieps_spec. }
apply (Rlt_le_trans _ _ _ (filt_spec Ff (finite1 fs) Hf)).
by rewrite FIS2FS1; right.
Qed.

Definition compute_c_aux_ssr : 'M[FIS fs]_n.+1 -> FIS fs -> FIS fs :=
  compute_c_aux (fieps fs) (fieta fs).

Lemma compute_c_aux_correct (A : 'M[FIS fs]_n.+1) maxdiag :
  (INR (2 * n.+2) * eps fs < 1) ->
  (finite (addup (mulup ((nat2Fup (2 * n.+2)%N)) (fieps fs)) (- (1)))%C) ->
  (FIS2FS (addup (mulup ((nat2Fup (2 * n.+2)%N)) (fieps fs)) (- (1)))%C < 0) ->
  (forall i, 0 <= FIS2FS (A i i)) ->
  (0 <= FIS2FS maxdiag) ->
  finite (compute_c_aux_ssr A maxdiag) ->
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + FIS2FS maxdiag)
  <= FIS2FS (compute_c_aux_ssr A maxdiag))%R.
Proof.
have Pnp2 := pos_INR (n.+2)%N.
have P2np2 := pos_INR (2 * n.+2)%N.
have Pe := eps_pos fs.
move=> Heps Fnem1 Nnem1 Pdiag Pmaxdiag Fc.
rewrite /compute_c_aux_ssr /compute_c_aux.
move: (fiplus_up_spec Fc); apply Rle_trans, Rplus_le_compat.
{ have Fl := fiplus_up_spec_fl Fc.
  move: (fimult_up_spec Fl); apply Rle_trans, Rmult_le_compat.
  { by apply Rmult_le_pos; [lra|apply gamma_pos]. }
  { by apply big_sum_pos_pos => i; rewrite !mxE. }
  { rewrite /gamma mult_INR -!(Rmult_assoc (/2)) Rinv_l; [|lra].
    rewrite Rmult_1_l.
    have Fll := fimult_up_spec_fl Fl.
    have F1mne := fiopp_spec_f Fnem1.
    move: (fidiv_up_spec Fll F1mne); apply Rle_trans, Rmult_le_compat.
    { apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
    { apply Rlt_le, Rinv_0_lt_compat; rewrite -mult_INR.
      by set ne := Rmult _ _; apply (Rplus_lt_reg_r ne); ring_simplify. }
    { have Flr := fidiv_up_spec_fl Fll F1mne.
      move: (fimult_up_spec Flr); apply /Rle_trans /Rmult_le_compat => //.
      { apply float_of_nat_up_spec, (fimult_up_spec_fl Flr). }
      apply fieps_spec. }
    rewrite (fiopp_spec F1mne) -mult_INR; apply Rinv_le.
    { by rewrite -Ropp_0; apply Ropp_lt_contravar. }
    rewrite -Ropp_minus_distr; apply Ropp_le_contravar.
    move: (fiplus_up_spec Fnem1); apply Rle_trans; apply Rplus_le_compat.
    { have Fne := fiplus_up_spec_fl Fnem1.
      move: (fimult_up_spec Fne); apply /Rle_trans /Rmult_le_compat => //.
      { apply float_of_nat_up_spec, (fimult_up_spec_fl Fne). }
      apply fieps_spec. }
    rewrite (fiopp_spec (fiplus_up_spec_fr Fnem1)); apply Ropp_le_contravar.
    by rewrite FIS2FS1; right. }
  apply tr_up_correct, (fimult_up_spec_fr Fl). }
have Fr := fiplus_up_spec_fr Fc.
move: (fimult_up_spec Fr); apply Rle_trans; apply Rmult_le_compat.
{ apply Rmult_le_pos; [|by apply pos_INR]; apply Rmult_le_pos; [lra|].
  apply Rlt_le, eta_pos. }
{ apply Rplus_le_le_0_compat; [|apply Pmaxdiag].
  apply Rmult_le_pos; [lra|apply pos_INR]. }
{ move: (fimult_up_spec (fimult_up_spec_fl Fr)); apply Rle_trans.
  have Frl := fimult_up_spec_fl Fr.
  apply Rmult_le_compat.
  { apply Rmult_le_pos; [lra|apply Rlt_le, eta_pos]. }
  { apply pos_INR. }
  { have Frll := fimult_up_spec_fl Frl.
    move: (fimult_up_spec Frll); apply Rle_trans.
    apply Rmult_le_compat; [lra|by apply Rlt_le, eta_pos| |by apply fieta_spec].
    replace 4 with (INR 4); [|by simpl; lra].
    apply float_of_nat_up_spec, (fimult_up_spec_fl Frll). }
  apply float_of_nat_up_spec, (fimult_up_spec_fr Frl). }
have Frr := fimult_up_spec_fr Fr.
move: (fiplus_up_spec Frr); apply Rle_trans, Rplus_le_compat_r.
have Frrl := fiplus_up_spec_fl Frr.
by change 2 with (INR 2); rewrite -mult_INR; apply float_of_nat_up_spec.
Qed.

Definition compute_c_ssr : 'M[FIS fs]_n.+1 -> option (FIS fs) :=
  compute_c (fieps fs) (fieta fs) (@finite fs).

Lemma compute_c_correct (A : 'M[FIS fs]_n.+1) :
  (INR (2 * n.+2) * eps fs < 1) ->
  (forall i, finite (A i i)) ->
  (forall i, (0 <= FIS2FS (A i i))%R) ->
  forall c : FIS fs, compute_c_ssr A = Some c ->
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + FIS2FS (max_diag_ssr A))
   <= FIS2FS c)%R.
Proof.
move=> Heps Fdiag Pdiag c.
rewrite /compute_c_ssr /compute_c.
set nem1 := addup _ _.
case_eq (finite nem1 && (nem1 < 0)%C); [|by []].
rewrite Bool.andb_true_iff => H; elim H => Fnem1 Nnem1.
set c' := compute_c_aux _ _ _ _.
case_eq (finite c') => Hite'; [|by []]; move=> Hc'.
have Hc'' : c' = c by injection Hc'.
rewrite -Hc''; apply compute_c_aux_correct => //.
{ eapply (Rlt_le_trans _ (FIS2FS zero_instFIS)); [|by right; rewrite FIS2FS0].
  apply filt_spec => //; apply finite0. }
by apply max_diag_pos.
Qed.

Definition posdef_check_ssr : 'M[FIS fs]_n.+1 -> bool :=
  posdef_check (fieps fs) (fieta fs) (@finite fs).

Lemma posdef_check_f1 A : posdef_check_ssr A ->
  forall i j, finite (A i j).
Proof.
rewrite /posdef_check_ssr /posdef_check.
case/and4P=> [H1 H2 H3 H4].
move: H4; set cc := compute_c _ _ _ _; case_eq cc => // c' Hc'.
set At := map_diag _ _; set Rt := cholesky _.
move/andP => [Had Hpd].
suff: forall i j : 'I_n.+1, (i <= j)%N -> finite (A i j).
{ move=> H i j; case (ltnP j i); [|by apply H]; move=> Hij.
  rewrite -(@fieq_spec_f _ (A^T i j)); [by rewrite mxE; apply H, ltnW|].
  by apply is_sym_correct_aux. }
move=> i j Hij; suff: finite (At i j).
{ case_eq (i == j :> nat) => Hij'.
  { move /eqP /ord_inj in Hij'; rewrite Hij' map_diag_correct_diag.
    apply fiminus_down_spec_fl. }
  rewrite map_diag_correct_ndiag //.
  by move /eqP in Hij' => H; apply Hij'; rewrite H. }
apply (@cholesky_success_infnan_f1 _ _ At Rt^T) => //; split.
{ rewrite /Rt -/(cholesky_ssr At).
  apply cholesky_spec_correct, cholesky_correct. }
move=> i'; rewrite mxE.
have->: R0 = FIS2FS (FIS0 fs) by rewrite FIS2FS0.
apply filt_spec; [by apply finite0| |].
{ move: Had i'; rewrite -/(all_diag_ssr _ _); apply all_diag_correct. }
move: Hpd i'; rewrite /pos_diag -/(all_diag_ssr _ _); apply all_diag_correct.
Qed.

Lemma posdef_check_correct A :
  posdef_check_ssr A -> posdef (MF2R (MFI2F A)).
Proof.
move=> H; have Hfdiag := posdef_check_f1 H.
move: H; move/eqP/eqP.
rewrite /posdef_check_ssr /posdef_check.
case/and3P => [Hn Hsym Htpdiag].
move/test_n_correct in Hn.
have Hn' : 2 * INR n.+2 * eps fs < 1.
{ move: (neps_pos fs n.+1); rewrite !Rmult_assoc; lra. }
have Hn'' : INR (2 * n.+2) * eps fs < 1 by rewrite mult_INR.
move/is_sym_correct in Hsym.
move: Htpdiag.
set cc := compute_c _ _ _ _; case_eq cc => // c' Hc'.
case/and3P.
set At := map_diag _ _; set Rt := cholesky _.
move=> Htpdiag HtfRt HtpRt.
have Htpdiag' := all_diag_correct Htpdiag.
have Hpdiag : forall i, 0 <= FIS2FS (A i i).
{ move=> i.
  eapply (Rle_trans _ (FIS2FS zero_instFIS)); [by right; rewrite FIS2FS0|].
  by apply file_spec => //; [apply finite0|apply Htpdiag']. }
have HfRt := all_diag_correct HtfRt.
have HtpRt' := all_diag_correct HtpRt.
have HpRt : forall i, 0 < (MFI2F Rt) i i.
{ move=> i.
  eapply (Rle_lt_trans _ (FIS2FS zero_instFIS)); [by right; rewrite FIS2FS0|].
  rewrite mxE; apply filt_spec => //; [apply finite0|apply HtpRt']. }
move {Htpdiag HtfRt HtpRt Htpdiag' HtpRt'}.
apply corollary_2_4_with_c_upper_bound with
 (maxdiag := FIS2FS (max_diag_ssr A)) (c := FIS2FS c') (At0 := At) => //.
{ by move=> i; rewrite mxE. }
{ by apply max_diag_correct. }
{ by apply compute_c_correct. }
have Hfat : forall i, finite (At i i).
{ move=> i; move: (cholesky_spec_correct (cholesky_correct At)).
  elim=> _ Hs; move: (Hs i); rewrite mxE /cholesky_ssr => {Hs} Hs.
  move: (HfRt i); rewrite /Rt Hs /ytildes_infnan => H.
  move: (fisqrt_spec_f1 H); apply stilde_infnan_fc. }
split; move=> i; [move=> j Hij|].
{ by apply /map_diag_correct_ndiag /eqP; rewrite neq_ltn Hij. }
move: (Hfat i); rewrite !mxE /At map_diag_correct_diag; apply fiminus_down_spec.
by rewrite andbF in Hc'.
Qed.

Lemma map_diag_sub_down_correct (A : 'M_n.+1) r :
  (forall i, finite (fiminus_down (A i i) r)) ->
  exists d : 'rV_n.+1,
    MF2R (MFI2F (map_diag_ssr ((@fiminus_down fs)^~ r) A))
    = MF2R (MFI2F A) - diag_mx d
    /\ (FIS2FS r : R) *: 1 <=m: diag_mx d.
Proof.
move=> HF; set A' := map_diag_ssr _ _.
exists (\row_i (((MFI2F A) i i : R) - ((MFI2F A') i i : R))); split.
{ rewrite -matrixP => i j; rewrite !mxE.
  set b := (_ == _)%B; case_eq b; rewrite /b /GRing.natmul /= => Hij.
  { move /eqP in Hij; rewrite Hij map_diag_correct_diag.
    rewrite /GRing.add /GRing.opp /=; ring. }
  rewrite /GRing.add /GRing.opp /GRing.zero /= Ropp_0 Rplus_0_r.
  by apply /f_equal /f_equal /map_diag_correct_ndiag /eqP; rewrite Hij. }
move=> i j; rewrite !mxE.
set b := (_ == _)%B; case_eq b; rewrite /b /GRing.natmul /= => Hij.
{ rewrite /GRing.mul /GRing.one /= Rmult_1_r /A' map_diag_correct_diag.
  rewrite /GRing.add /GRing.opp /=.
  replace (FIS2FS r : R)
  with (Rminus (FIS2FS (A i i)) (Rminus (FIS2FS (A i i)) (FIS2FS r))) by ring.
  by apply Rplus_le_compat_l, Ropp_le_contravar, fiminus_down_spec. }
by rewrite GRing.mulr0; right.
Qed.

Definition posdef_check_itv_ssr : 'M[FIS fs]_n.+1 -> FIS fs -> bool :=
  posdef_check_itv (fieps fs) (fieta fs) (@finite fs).

Lemma posdef_check_itv_f1 A r : posdef_check_itv_ssr A r ->
  forall i j, finite (A i j).
Proof.
rewrite /posdef_check_itv_ssr /posdef_check_itv; set A' := map_diag _ _.
move/and3P => [H1 H2 H3] i j.
suff: finite (A' i j); [|by apply posdef_check_f1].
case_eq (i == j :> nat) => Hij'.
{ move /eqP /ord_inj in Hij'; rewrite Hij' map_diag_correct_diag.
  apply fiminus_down_spec_fl. }
rewrite map_diag_correct_ndiag //.
by move /eqP in Hij' => H; apply Hij'; rewrite H.
Qed.

Lemma posdef_check_itv_correct A r : posdef_check_itv_ssr A r ->
  forall Xt : 'M[R]_n.+1,
  Mabs (Xt - MF2R (MFI2F A)) <=m: MF2R (MFI2F (matrix.const_mx r)) ->
  posdef Xt.
Proof.
rewrite /posdef_check_itv_ssr /posdef_check_itv.
set nr := mulup _ _; set A' := map_diag _ _.
case/and3P => [Fr Pr HA' Xt HXt].
have HA'' := posdef_check_correct HA'.
have HF := posdef_check_f1 HA'.
have HF' : forall i, finite (fiminus_down (A i i) nr).
{ by move=> i; move: (HF i i); rewrite map_diag_correct_diag. }
rewrite -(GRing.addr0 Xt) -(GRing.subrr (MF2R (MFI2F A))).
elim (map_diag_sub_down_correct HF') => d [Hd Hd'].
rewrite /map_diag_ssr /fiminus_down -/A' in Hd.
have HA : MF2R (MFI2F A) = MF2R (MFI2F A') + diag_mx d.
{ by rewrite Hd -GRing.addrA (GRing.addrC _ (_ d)) GRing.subrr GRing.addr0. }
rewrite {1}HA.
rewrite !GRing.addrA (GRing.addrC Xt) -!GRing.addrA (GRing.addrC (diag_mx d)).
apply posdef_norm_eq_1 => x Hx.
rewrite mulmxDr mulmxDl -(GRing.addr0 0); apply Madd_lt_le_compat.
{ apply HA'' => Hx'; rewrite Hx' norm2_0 /GRing.zero /GRing.one /= in Hx.
  move: Rlt_0_1; rewrite Hx; apply Rlt_irrefl. }
rewrite GRing.addrA mulmxDr mulmxDl -(GRing.opprK (_ *m diag_mx d *m _)).
apply Mle_sub.
apply Mle_trans with (- Mabs (x^T *m (Xt - MF2R (MFI2F A)) *m x));
  [apply Mopp_le_contravar|by apply Mge_opp_abs].
apply Mle_trans with ((Mabs x)^T *m Mabs (Xt - MF2R (MFI2F A)) *m Mabs x).
{ apply (Mle_trans (Mabs_mul _ _)), Mmul_le_compat_r; [by apply Mabs_pos|].
  rewrite map_trmx; apply (Mle_trans (Mabs_mul _ _)).
  by apply Mmul_le_compat_l; [apply Mabs_pos|apply Mle_refl]. }
apply (Mle_trans (Mmul_abs_lr _ HXt)).
apply Mle_trans with (INR n.+1 * FIS2FS r)%Re%:M.
{ apply r_upper_bound => //.
  { move: HXt; apply Mle_trans, Mabs_pos. }
  by move=> i j; rewrite !mxE; right. }
set IN := INR n.+1; rewrite Mle_scalar !mxE /GRing.natmul /= -(Rmult_1_r (_ * _)).
replace R1 with (R1^2) by ring; rewrite /GRing.one /= in Hx; rewrite -Hx.
rewrite norm2_sqr_dotprod /dotprod mxE /= big_distrr /=.
apply big_rec2 => [|i y1 y2 _ Hy12]; [by right|]; rewrite mul_mx_diag !mxE.
rewrite /GRing.add /GRing.mul /=; apply Rplus_le_compat => //.
rewrite (Rmult_comm _ (d _ _)) !Rmult_assoc -Rmult_assoc.
apply Rmult_le_compat_r; [by apply Rle_0_sqr|].
have Fnr : finite nr.
{ move: (HF' ord0); rewrite /fiminus_down => F.
  apply fiopp_spec_f1 in F; apply (fiplus_up_spec_fl F). }
apply (Rle_trans _ (FIS2FS nr)).
{ apply (Rle_trans _ (FIS2FS (float_of_nat_up fs n.+1) * FIS2FS r)).
  { apply Rmult_le_compat_r.
    { change R0 with (F0 fs : R); rewrite -FIS2FS0; apply file_spec.
      { apply finite0. }
      { move: Fnr; rewrite /nr; apply fimult_up_spec_fr. }
      by move: Pr. }
    by apply float_of_nat_up_spec, (fimult_up_spec_fl Fnr). }
  by apply fimult_up_spec. }
by move: (Hd' i i); rewrite !mxE eq_refl /GRing.natmul /GRing.mul /= Rmult_1_r.
Qed.

End theory_cholesky_3.

(** Tactic addressing goals like [refines R3 (f a b) (f' c d)],
    by repetitive (e)apply [refines_apply], to get something like
    [refines (R1 ==> R2 ==> R3) f f'], solve this by tc (needs an instance)
    and try to solve the remainings (refines R1 a c) and (refines R2 b d). *)
Ltac refines_apply_tc :=
  (by tc) || (eapply refines_apply; first refines_apply_tc;
              try by tc; try by rewrite refinesE).

(** ** Part 3: Parametricity *)

(** *** 3.1 Data refinement *)

Section refinement_cholesky.

(** "C" for "concrete type" *)
Context {C : Type}.
Context `{!zero_of C, !one_of C, !add_of C, !opp_of C, !mul_of C, !div_of C, !sqrt_of C}.
Local Notation mxC := (@hseqmx C) (only parsing).

Context `{!leq_of C}.

Context {n1 n2 : nat} {rn : nat_R n1 n2}.

Let r1 := nat_R_S_R nat_R_O_R.
Let rn' := nat_R_S_R rn.

Global Instance param_dotmulB0 :
  refines (Rord rn' ==> eq ==> Rseqmx r1 rn' ==> Rseqmx r1 rn' ==> eq)
    (@dotmulB0_ssr _ _ _ _ n1.+1) (@dotmulB0_seqmx C _ _ _ n2.+1).
Proof.
rewrite refinesE=> k _ <- c _ <- _ _ [a a' ha1 ha2 ha3] _ _ [b b' hb1 hb2 hb3].
rewrite /dotmulB0_seqmx.
move: ha1; case Ea' : a'=>[//|a'0 a'1] _ /=.
move: hb1; case Eb' : b'=>[//|b'0 b'1] _ /=.
move: (ha2 O erefl) (hb2 O erefl) (ha3 ord0) (hb3 ord0).
rewrite Ea' Eb' /= -(nat_R_eq rn').
elim: n1 k {ha3} a {hb3} b c {Ea'} a'0 {Eb'} b'0 => [|n' IH] k a b c a'0 b'0.
{ by rewrite (ord_1_0 k). }
case Ea'0 : a'0 => [//|a'00 a'01].
case Eb'0 : b'0 => [//|b'00 b'01] ha1 hb1 ha3 hb3.
case k => {k} k Hk; case: k Hk => //= k Hk; set cc := (c + - _)%C.
rewrite ltnS in Hk.
rewrite <-(IH (Ordinal Hk) (\row_(i < n'.+1) a ord0 (lift ord0 i))
                           (\row_(i < n'.+1) b ord0 (lift ord0 i))).
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE /cc.
  { by repeat f_equal; [rewrite ha3 inordK|rewrite hb3 inordK]. }
  f_equal; apply f_equal2; rewrite mxE; f_equal; apply ord_inj.
  { rewrite inordK /=.
    { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
    by rewrite /bump add1n ltnS; apply (ltn_trans (ltn_ord _)). }
  rewrite inordK /=.
  { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
  by rewrite /bump add1n ltnS; apply (ltn_trans (ltn_ord _)). }
{ by move: ha1 => [ha1']. }
{ by move: hb1 => [hb1']. }
{ by move=> j; rewrite mxE ha3. }
by move=> j; rewrite mxE hb3.
Qed.

Global Instance param_ytilded :
  refines (Rord rn' ==> eq ==> Rseqmx r1 rn' ==> Rseqmx r1 rn' ==> eq ==> eq)
    (ytilded_ssr (T:=C) (n := n1)) (ytilded_seqmx (n := n2)).
Proof.
rewrite refinesE=> k k' rk c _ <- a a' ra b b' rb bk _ <-.
rewrite /ytilded_ssr /ytilded_seqmx /ytilded; f_equal.
apply refinesP; refines_apply_tc.
Qed.

Global Instance param_ytildes :
  refines (Rord rn' ==> eq ==> Rseqmx r1 rn' ==> eq)
    (ytildes_ssr (T:=C) (n := n1)) (ytildes_seqmx (n := n2)).
Proof.
rewrite refinesE=> k k' rk c _ <- a a' ra.
rewrite /ytildes_ssr /ytildes_seqmx /ytildes; f_equal.
apply refinesP; refines_apply_tc.
Qed.

Global Instance param_iteri_ord :
  forall T T', forall RT : T -> T' -> Type,
  refines ((fun j j' => j = j' /\ (j <= n1.+1)%N) ==> (Rord rn' ==> RT ==> RT)
           ==> RT ==> RT)
    (@iteri_ord _ n1.+1 I0_ssr succ0_ssr T)
    (@iteri_ord _ n2.+1 I0_instN succ0_instN T').
Proof.
move=> T T' RT.
rewrite refinesE => j j' [Hj' Hj] f f' rf x x' rx; rewrite -Hj' -(nat_R_eq rn).
apply (iteri_ord_ind2 (M := T) (M' := T') (j := j)) => // i i' s s' Hi Hi' Hs.
apply refinesP; refines_apply_tc.
Qed.

Global Instance param_inner_loop :
  refines (Rord rn' ==> Rseqmx rn' rn' ==> Rseqmx rn' rn' ==> Rseqmx rn' rn')
    (inner_loop_ssr (T:=C) (n := n1)) (inner_loop_seqmx (n := n2)).
Proof.
rewrite refinesE=> j j' rj a a' ra r r' rr.
rewrite /inner_loop_ssr /inner_loop_seqmx /inner_loop.
apply refinesP; refines_apply_tc.
{ rewrite refinesE; split; [by []|apply ltnW, ltn_ord]. }
rewrite refinesE=> i i' ri s s' rs.
exact: refinesP.
Qed.

Global Instance param_outer_loop :
  refines (Rseqmx rn' rn' ==> Rseqmx rn' rn' ==> Rseqmx rn' rn')
    (outer_loop_ssr (T:=C) (n := n1)) (outer_loop_seqmx (n := n2)).
Proof.
rewrite refinesE=> a a' ra r r' rr.
rewrite /outer_loop_ssr /outer_loop_seqmx /outer_loop.
apply refinesP; refines_apply_tc.
{ by rewrite refinesE; split; [rewrite (nat_R_eq rn)|]. }
rewrite refinesE=> i i' ri s s' rs.
exact: refinesP.
Qed.

Global Instance param_cholesky :
  refines (Rseqmx rn' rn' ==> Rseqmx rn' rn')
    (cholesky_ssr (T:=C) (n := n1)) (cholesky_seqmx (n := n2)).
Proof.
rewrite refinesE=> a a' ra; rewrite /cholesky_ssr /cholesky_seqmx /cholesky.
exact: refinesP.
Qed.

End refinement_cholesky.

(* FIXME: closing/opening a new section should be unnecessary here *)
Section refinement_cholesky_2.
(* C := FIS fs *)

Context {fs : Float_round_up_infnan_spec}.

(* FIXME: D.R.Y *)
Variables (F : Type) (F2FIS : F -> FIS fs) (toR : F -> R).
Hypothesis (F2FIS_correct : forall f, finite (F2FIS f) -> FIS2FS (F2FIS f) = toR f :> R).

(* FIXME: remove @, _, etc. *)

Section rn.

Context {n1 n2 : nat} {rn : nat_R n1 n2}.

Let rn' := nat_R_S_R rn.

Global Instance param_is_sym :
  refines (Rseqmx rn' rn' ==> eq)
    (@is_sym _ _ n1.+1 (@heq_ssr (FIS fs) (@fieq fs)) (@trmx _))
    (@is_sym _ _ n2.+1 _ trmx_seqmx).
Proof.
rewrite refinesE=> a a' ra; rewrite /is_sym /trmx_op /heq_op.
exact: refinesP.
Qed.

Global Instance param_foldl_diag T' :
  refines (eq ==> eq ==> Rseqmx rn' rn' ==> eq)
    (@foldl_diag _ _ matrix (@fun_of_ssr (FIS fs)) n1.+1
       (@I0_ssr n1) (@succ0_ssr n1) T')
    (@foldl_diag _ _ (@hseqmx) (@fun_of_seqmx (FIS fs) (FIS0 fs)) n2.+1
       (@I0_instN n2) (@succ0_instN n2) T').
Proof.
rewrite refinesE=> f _ <- z z' rz m m' rm.
rewrite /foldl_diag.
apply refinesP; refines_apply_tc.
{ by rewrite -(nat_R_eq rn') refinesE. }
rewrite refinesE=> i i' ri x _ <-; apply f_equal.
exact: refinesP.
Unshelve.
exact rn.
Qed.

Global Instance param_all_diag :
  refines (eq ==> Rseqmx rn' rn' ==> eq)
    (@all_diag _ _ _ (@fun_of_ssr _) n1.+1 (@I0_ssr n1) (@succ0_ssr n1))
    (@all_diag _ _ (@hseqmx)
       (@fun_of_seqmx _ (@zero_instFIS fs)) n2.+1 (@I0_instN n2)
       (@succ0_instN n2)).
Proof.
rewrite refinesE=> f _ <- a a' ra; rewrite /all_diag.
apply refinesP; refines_apply_tc.
Qed.

Global Instance param_max_diag :
  refines (Rseqmx rn' rn' ==> eq)
    (@max_diag _ _ _ (FIS0 fs)
       (@fun_of_ssr (FIS fs)) n1.+1 (@I0_ssr n1) (@succ0_ssr n1)
       (@leq_instFIS fs))
    (@max_diag _ _ (@hseqmx) (FIS0 fs)
       (@fun_of_seqmx (FIS fs) (FIS0 fs)) n2.+1 (@I0_instN n2)
       (@succ0_instN n2) leq_instFIS).
Proof.
rewrite refinesE=> a a' ra; rewrite /max_diag.
apply refinesP; refines_apply_tc.
Qed.

Global Instance param_compute_c_aux :
  refines (Rseqmx rn' rn' ==> eq ==> eq)
    (@compute_c_aux _ _ _ (FIS0 fs) (FIS1 fs) (@fiopp fs)
       (@fun_of_ssr (FIS fs)) n1.+1
       (@I0_ssr n1) (@succ0_ssr n1) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
       (float_of_nat_up fs) (fieps fs) (fieta fs))
    (@compute_c_aux _ _ (@hseqmx) (FIS0 fs) (FIS1 fs) (@fiopp fs)
       (@fun_of_seqmx (FIS fs) (FIS0 fs)) n2.+1
       (@I0_instN n2) (@succ0_instN n2) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
       (float_of_nat_up fs) (fieps fs) (fieta fs)).
Proof.
rewrite refinesE=> a a' ra x _ <-; rewrite /compute_c_aux.
set ta := tr_up a; set ta' := tr_up a'.
have <- : ta = ta'; [|by rewrite -(nat_R_eq rn')].
rewrite /ta /ta' /tr_up; apply refinesP; refines_apply_tc.
Qed.

Global Instance param_compute_c :
  refines (Rseqmx rn' rn' ==> eq)
    (@compute_c (FIS fs) _ _
       (@zero_instFIS fs) (@one_instFIS fs) (@opp_instFIS fs)
       (@fun_of_ssr (FIS fs)) n1.+1 (@I0_ssr n1)
       (@succ0_ssr n1) (@leq_instFIS fs) (@lt_instFIS fs) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
       (float_of_nat_up fs) (fieps fs) (fieta fs) (@finite fs))
    (@compute_c _ _ (@hseqmx)
       zero_instFIS one_instFIS opp_instFIS
       (@fun_of_seqmx _ zero_instFIS) n2.+1 (@I0_instN n2)
       (@succ0_instN n2) leq_instFIS lt_instFIS (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
       (float_of_nat_up fs) (fieps fs) (fieta fs) (@finite fs)).
Proof.
rewrite refinesE=> a a' ra; rewrite /compute_c.
set ca := compute_c_aux _ _ a _.
set ca' := compute_c_aux _ _ a' _.
have <- : ca = ca'; [by exact: refinesP|].
by rewrite -(nat_R_eq rn').
Qed.

Global Instance param_map_diag :
  refines ((eq ==> eq) ==> Rseqmx rn' rn' ==> Rseqmx rn' rn')
    (@map_diag _ _ _
       (@fun_of_ssr (FIS fs)) (@store_ssr (FIS fs)) n1.+1
       (@I0_ssr n1) (@succ0_ssr n1))
    (@map_diag _ _ (@hseqmx)
       (@fun_of_seqmx _ zero_instFIS) (@store_seqmx _) n2.+1
       (@I0_instN n2) (@succ0_instN n2)).
Proof.
rewrite refinesE=> f f' rf a a' ra; rewrite /map_diag.
apply refinesP; refines_apply_tc; [by rewrite -(nat_R_eq rn') refinesE|].
rewrite refinesE=> i i' ri b b' rb.
exact: refinesP.
Unshelve.
exact rn.
Qed.

Global Instance param_posdef_check :
  refines (Rseqmx rn' rn' ==> eq)
    (@posdef_check_ssr fs n1)
    (posdef_check_seqmx (n:=n2) (fieps fs) (fieta fs) (@finite fs)).
Proof.
rewrite refinesE=> a a' ra.
rewrite /posdef_check_ssr /posdef_check_seqmx /posdef_check.
f_equal.
{ by rewrite -(nat_R_eq rn'). }
f_equal.
{ exact: refinesP. }
f_equal.
{ rewrite /noneg_diag; apply refinesP; refines_apply_tc. }
set c := compute_c _ _ _ a.
set c' := compute_c _ _ _ a'.
have <- : c = c'; [by exact: refinesP|]; case c=>// m.
set r := cholesky _; set r' := cholesky _.
suff rr : refines (Rseqmx (H:=FIS0 fs) rn' rn') r r'.
{ f_equal; rewrite/pos_diag; apply refinesP; refines_apply_tc. }
by do 2 refines_apply_tc; rewrite refinesE=> f _ <-.
Qed.

Lemma param_posdef_check_itv_aux :
  refines (Rseqmx rn' rn' ==> eq ==> eq)
    (@posdef_check_itv_ssr fs n1)
    (posdef_check_itv_seqmx (n:=n2) (fieps fs) (fieta fs) (@finite fs)).
Proof.
rewrite refinesE=> a a' ra' r _ <-.
rewrite /posdef_check_itv_ssr /posdef_check_itv_seqmx /posdef_check_itv.
do 2 apply f_equal; rewrite /posdef_check.
f_equal.
{ by rewrite -(nat_R_eq rn'). }
set b := map_diag _ a; set b' := map_diag _ a'.
suff rb : refines (Rseqmx (H:=FIS0 fs) rn' rn') b b'.
{ f_equal.
  { exact: refinesP. }
  f_equal.
  { rewrite /noneg_diag; apply refinesP; refines_apply_tc. }
  set c := compute_c _ _ _ b.
  set c' := compute_c _ _ _ b'.
  have <- : c = c'; [by exact: refinesP|]; case c=>// m.
  set d := cholesky _; set d' := cholesky _.
  suff rd : refines (Rseqmx (H:=FIS0 fs) rn' rn') d d'.
  { f_equal; rewrite/pos_diag; apply refinesP; refines_apply_tc. }
  by do 2 refines_apply_tc; rewrite refinesE=> f _ <-. }
by refines_apply_tc; rewrite -(nat_R_eq rn') refinesE=> e _ <-.
Qed.

End rn.

Global Instance refines_posdef_check_itv n :
  refines (Rseqmx (nat_Rxx n.+1) (nat_Rxx n.+1) ==> eq ==> eq)
    (@posdef_check_itv_ssr fs n)
    (posdef_check_itv_seqmx (n:=n) (fieps fs) (fieta fs) (@finite fs)).
Proof.
rewrite refinesE=> _ _ [Q Q' h1 h2 h3] r r' rr.
apply refinesP; eapply refines_apply; [eapply refines_apply|].
{ apply (param_posdef_check_itv_aux (rn:=nat_Rxx n)). }
{ by rewrite refinesE; split. }
by rewrite refinesE.
Qed.

End refinement_cholesky_2.

(** *** 3.2 Data refinement with CoqInterval datatypes *)
Section refinement_cholesky_3.

Let fis := coqinterval_infnan.coqinterval_infnan.

Definition eps_inv := Eval compute in (2 ^ 53)%bigZ.

Lemma eps_inv_correct : (Z2R [eps_inv]%bigZ <= / eps fis)%Re.
Proof. by rewrite /= /flx64.eps /= Rinv_involutive; [right|lra]. Qed.

(* This definition of [F2FI_val] is irrelevant as it maps some floats
   such as [Interval_specific_ops.Float eps_inv (-1)%bigZ] to Fnan,
   while these floats would faitfully satisfy [mantissa_bounded].

Definition F2FI_val (f : F.type) : F.type :=
  match f with
    | Interval_specific_ops.Fnan => Interval_specific_ops.Fnan
    | Interval_specific_ops.Float m e =>
      if (BigZ.abs m <? eps_inv)%bigZ then f else Interval_specific_ops.Fnan
  end.

Goal mantissa_bounded (Interval_specific_ops.Float eps_inv (-1)%bigZ).
rewrite /eps_inv /mantissa_bounded /F.toX.
right.
exists (2 ^ 52).
simpl; f_equal; field.
apply: FLX_format_generic.
have->: (2 ^ 52)%R = (bpow radix2 52) by simpl; ring.
exact: generic_format_bpow.
Qed.
 *)

Definition F2FI_val (f : F.type) : F.type :=
  match f with
    | Interval_specific_ops.Fnan => Interval_specific_ops.Fnan
    | Interval_specific_ops.Float m e =>
      if (signif_digits m <=? 53)%bigZ then f else Interval_specific_ops.Fnan
  end.

Lemma F2FI_proof (x : F.type) : mantissa_bounded (F2FI_val x).
Proof.
case: x => [|m e]; first by left; rewrite /mantissa_bounded /F.toX /x_bounded /=.
rewrite /F2FI_val.
case E: BigZ.leb; last by left.
exact/signif_digits_correct.
Qed.

Definition F2FI (f : F.type) : FI := Build_FI _ (F2FI_proof f).

Lemma F2FI_correct (f : F.type) : F.real (F2FI f) ->
                                  FI2FS (F2FI f) = toR f :> R.
Proof.
case f => // m e.
rewrite /= FtoX_real /coqinterval_infnan.FI2FS.
case (FI_prop (F2FI (Float m e))) => Hf; [by rewrite Hf|].
destruct Hf as (r, Hr, Hr'); move=> HF /=.
suff: Xreal r = Xreal (proj_val (F.toX (Float m e))).
{ by case. }
move: HF.
by rewrite -real_FtoX_toR // -Hr /F2FI /=; case (_ <=? _)%bigZ.
Qed.

Local Notation fris := coqinterval_round_up_infnan.

Definition posdef_check4_coqinterval' (M : seq (seq (FIS fris))) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_seqmx (T := FIS fris) (n := m.-1)
    coqinterval_infnan.fieps coqinterval_infnan.fieta
    (@float_infnan_spec.finite _) M.

Definition posdef_check_itv4_coqinterval' (M : seq (seq (FIS fris))) (r : (FIS fris)) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_itv_seqmx (T := FIS fris) (n := m.-1)
    coqinterval_infnan.fieps coqinterval_infnan.fieta
    (@float_infnan_spec.finite _) M r.

Definition prec := 53%bigZ.

Definition bigQ2F (q : bigQ) : F.type * F.type :=
  match q with
  | BigQ.Qz m => let m0 := Interval_specific_ops.Float m Bir .exponent_zero in (m0, m0)
  | BigQ.Qq m n => let m0 := Interval_specific_ops.Float m Bir.exponent_zero in
                   let n0 := Interval_specific_ops.Float (BigZ.Pos n) Bir.exponent_zero in
                   (F.div rnd_DN prec m0 n0, F.div rnd_UP prec m0 n0)
  end.

Lemma toR_Float (m e : bigZ) :
  toR (Float m e) = (Z2R [m]%bigZ * bpow F.radix [e]%bigZ)%Re.
Proof.
rewrite /F.toX /F.toF /=.
have := Bir.mantissa_sign_correct m.
case E_m: (Bir.mantissa_sign m) => [|s m']; last case.
  by rewrite /Bir.MtoZ =>-> /=; rewrite Rmult_0_l.
rewrite /proj_val /FtoX.
rewrite (FtoR_split radix2 s (Bir.MtoP m') [e]%bigZ).
rewrite /F2R /= /cond_Zopp => H1 H2; congr Rmult.
move: H1; case: (s) => H1.
by rewrite Pos2Z.opp_pos -H1.
by rewrite -H1.
Qed.

End refinement_cholesky_3.
