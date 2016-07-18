Require Import Reals Flocq.Core.Fcore_Raux BigZ Psatz.
From Flocq Require Import Fcore.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements seqmatrix.
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix cholesky cholesky_infnan.
Require Import misc gamma fsum.

(** * Application: program for Cholesky decomposition *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Refinements.Op.

Notation seqmatrix' := ((fun (A : Type) (_ _ : nat) => seqmatrix A)) (only parsing).

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

Context `{!map_mx_class mx}.

Variables (F : Type) (F2FI : F -> T).

Definition posdef_check_F (A : mx F n n) : bool := posdef_check (map_mx F2FI A).

Definition posdef_check_itv_F (A : mx F n n) (r : F) : bool :=
  posdef_check_itv (map_mx F2FI A) (F2FI r).

End generic_cholesky.

Section seqmx_cholesky.

(** *** 1.3 Generic defs for seqmx

- instantiation of dotmulB0, store, map_mx, eq, transpose
- a few support lemmas
 *)

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, !div T, !mul T, !sqrt T}.

Fixpoint stilde_seqmx k c a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => stilde_seqmx k (c + (- (a1 * b1)))%C a2 b2
  end.

Global Instance dotmulB0_seqmx : dotmulB0_class T ord_instN (seqmatrix' T) :=
  fun n k c a b => stilde_seqmx k c (head [::] a) (head [::] b).

Fixpoint store_aux T s k (v : T) :=
  match s, k with
    | [::], _ => [::]
    | _ :: t, O => v :: t
    | h :: t, S k => h :: store_aux t k v
  end.

Fixpoint store_seqmx0 T m i j (v : T) :=
  match m, i with
    | [::], _ => [::]
    | h :: t, O => store_aux h j v :: t
    | h :: t, S i => h :: store_seqmx0 t i j v
  end.

Global Instance store_seqmx : store_class T ord_instN (seqmatrix' T) :=
  fun (_ _ : nat) M i j v => store_seqmx0 M i j v.

Context {n : nat}.

Definition ytilded_seqmx :
  ord_instN n.+1 -> T -> seqmatrix' T 1%N n.+1 -> seqmatrix' T 1%N n.+1 -> T -> T :=
  ytilded (T := T).

Definition ytildes_seqmx : ord_instN n.+1 -> T -> seqmatrix' T 1%N n.+1 -> T :=
  ytildes.

Definition cholesky_seqmx : seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 :=
  cholesky.

Definition outer_loop_seqmx :
  seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 :=
  outer_loop.

Definition inner_loop_seqmx :
  ord_instN n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 :=
  inner_loop.

Lemma size_store_seqmx0 :
  forall s i j x,
  seq.size (@store_seqmx0 T s j i x) = seq.size s.
Proof.
move=> s i j x.
elim: s j => [|a s IHs] j; first by case: j.
case: j IHs => [|j] IHs //=.
by rewrite -(IHs j).
Qed.

Lemma size_inner_loop_seqmx :
  forall A j R, (nat_of j <= n.+1)%N ->
  seq.size R = n.+1 -> seq.size (inner_loop_seqmx j A R) = n.+1.
Proof.
move=> A j R Hj H0; rewrite /inner_loop_seqmx /inner_loop.
by apply iteri_ord_ind => // i0 s Hs /=; rewrite size_store_seqmx0.
Qed.

Lemma size_outer_loop_seqmx :
  forall A R, seq.size R = n.+1 -> seq.size (outer_loop_seqmx A R) = n.+1.
Proof.
move=> A R HRs; rewrite /outer_loop_seqmx /outer_loop.
set P := fun (i : nat) (s : seqmatrix T) => seq.size s = n.+1.
rewrite -/(P n.+1 _).
apply iteri_ord_ind => // i s Hle Hs /=; rewrite /P size_store_seqmx0.
by apply size_inner_loop_seqmx => //; apply ltnW.
Qed.

Lemma size_cholesky_seqmx M : seq.size M = n.+1 -> seq.size (cholesky_seqmx M) = n.+1.
Proof. apply size_outer_loop_seqmx. Qed.

Lemma size_store_aux :
  forall s i x,
  seq.size (@store_aux T s i x) = seq.size s.
Proof.
move=> s i x.
elim: s i => [|a s IHs] i; first by case: i.
case: i IHs => [|i] IHs //=.
by rewrite -(IHs i).
Qed.

Lemma size_nth_store_seqmx0 :
  forall s i j k x,
  seq.size (nth [::] (@store_seqmx0 T s j i x) k) = seq.size (nth [::] s k).
Proof.
move=> s i j k x.
elim: s j k => [|a s IHs] j k; first by case: j.
case: j IHs => [|j] IHs //=; case: k IHs => [|k] IHs //=.
by rewrite size_store_aux.
Qed.

Lemma size_nth_inner_loop_seqmx :
  forall A j k R, (nat_of j <= n.+1)%N ->
  seq.size (nth [::] R k) = n.+1 ->
  seq.size (nth [::] (inner_loop_seqmx j A R) k) = n.+1.
Proof.
move=> A j k R Hj; rewrite /inner_loop_seqmx /inner_loop.
apply iteri_ord_ind => //.
by move=> i0 s Hle Hs; rewrite size_nth_store_seqmx0.
Qed.

Lemma size_nth_outer_loop_seqmx :
  forall A R (i : nat), (i < n.+1)%N ->
  seq.size (nth [::] R i) = n.+1 ->
  seq.size (nth [::] (outer_loop_seqmx A R) i) = n.+1.
Proof.
move=> A R i Hi HRs; rewrite /outer_loop_seqmx /outer_loop.
set P := fun (i : nat) (s : seqmatrix T) => seq.size (nth [::] s i) = n.+1.
rewrite -/(P _ _).
apply iteri_ord_ind => // i0 s Hle Hs; rewrite /P size_nth_store_seqmx0.
by apply size_nth_inner_loop_seqmx => //; apply ltnW.
Qed.

Lemma size_nth_cholesky_seqmx M :
  forall i : nat, (i < n.+1)%N ->
  seq.size (nth [::] M i) = n.+1 ->
  seq.size (nth [::] (cholesky_seqmx M) i) = n.+1.
Proof. by move=> *; apply: size_nth_outer_loop_seqmx. Qed.

Context `{!eq T}.

Global Instance eq_seqmx : @heq nat (seqmatrix' T) :=
  fun _ _ : nat => eq_seq (eq_seq eq_op).

Global Instance transpose_seqmx : transpose_class (seqmatrix' T) :=
  fun _ _ : nat => @trseqmx T.

Context `{!leq T, !lt T}.

(** Rely on arithmetic operations with directed rounding: *)
Context `{!addup_class T, !mulup_class T, !divup_class T}.
Context `{!nat2Fup_class T, !subdn_class T}.

Variable feps feta : T.

Variable is_finite : T -> bool.

Definition posdef_check_seqmx : seqmatrix' T n.+1 n.+1 -> bool :=
  posdef_check feps feta is_finite.

Definition posdef_check_itv_seqmx : seqmatrix' T n.+1 n.+1 -> T -> bool :=
  posdef_check_itv feps feta is_finite.

Global Instance map_mx_seqmx : map_mx_class seqmatrix' :=
  fun T T' m n f s => map (map f) s.

Variables (F : Type) (F2FI : F -> T) (zeroF : F).

Definition posdef_check_F_seqmx : seqmatrix' F n.+1 n.+1 -> bool :=
  posdef_check_F feps feta is_finite F2FI.

Definition posdef_check_itv_F_seqmx : seqmatrix' F n.+1 n.+1 -> F -> bool :=
  posdef_check_itv_F feps feta is_finite F2FI.

End seqmx_cholesky.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_cholesky.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

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

Global Instance add_instFI : add (FI fs) := @fiplus fs.
Global Instance mul_instFI : mul (FI fs) := @fimult fs.
Global Instance sqrt_instFI : sqrt (FI fs) := @fisqrt fs.
Global Instance div_instFI : div (FI fs) := @fidiv fs.
Global Instance opp_instFI : opp (FI fs) := @fiopp fs.
Global Instance zero_instFI : zero (FI fs) := @FI0 fs.
Global Instance one_instFI : one (FI fs) := @FI1 fs.

Global Instance eq_instFI : eq (FI fs) := @fieq fs.
Global Instance leq_instFI : leq (FI fs) := @file fs.
Global Instance lt_instFI : lt (FI fs) := @filt fs.

Context {n : nat}.

Lemma dotmulB0_correct k (c : FI fs) (a b : 'rV_n.+1) :
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

Lemma ytilded_correct k (c : FI fs) (a b : 'rV_n.+1) (bk : FI fs) :
  ytilded_ssr k c a b bk = ytilded_infnan c
                                          [ffun i : 'I_k => a ord0 (inord i)]
                                          [ffun i : 'I_k => b ord0 (inord i)]
                                          bk.
Proof.
rewrite /ytilded_ssr /ytilded /ytilded_infnan; apply f_equal2 => //.
apply dotmulB0_correct.
Qed.

Lemma ytildes_correct k (c : FI fs) (a : 'rV_n.+1) :
  ytildes_ssr k c a = ytildes_infnan c [ffun i : 'I_k => a ord0 (inord i)].
Proof.
rewrite /ytildes_ssr /ytildes /ytildes_infnan; apply f_equal => //.
apply dotmulB0_correct.
Qed.

Lemma cholesky_spec_correct (A R : 'M_n.+1) :
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
  forall A : 'M[FI fs]_n.+1, MF2R (MFI2F A^T) = MF2R (MFI2F A) ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma.gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FI fs]_n.+1,
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

Global Instance addup_instFI : addup_class (FI (fris fs)) := @fiplus_up fs.
Global Instance mulup_instFI : mulup_class (FI (fris fs)) := @fimult_up fs.
Global Instance divup_instFI : divup_class (FI (fris fs)) := @fidiv_up fs.
Global Instance nat2Fup_instFI : nat2Fup_class (FI (fris fs)) :=
  @float_of_nat_up fs.
Global Instance subdn_instFI : subdn_class (FI (fris fs)) := @fiminus_down fs.

Global Instance heq_instFI_ssr : @heq nat (matrix (FI fs)) :=
  fun n1 n2 a b => [forall i, [forall j, fieq (a i j) (b i j)]].

Global Instance trmx_instFI_ssr : transpose_class (matrix (FI fs)) := @matrix.trmx (FI fs).

Context {n : nat}.

Lemma is_sym_correct_aux (A : 'M[FI fs]_n.+1) :
  is_sym A -> forall i j, fieq (A^T i j) (A i j).
Proof. by move=> H i j; move/forallP/(_ i)/forallP/(_ j) in H. Qed.

Lemma is_sym_correct (A : 'M[FI fs]_n.+1) :
  is_sym A -> MF2R (MFI2F A^T) = MF2R (MFI2F A).
Proof.
move/is_sym_correct_aux=> H; apply /matrixP=> i j.
move: (H i j); rewrite !mxE; apply fieq_spec.
Qed.

Definition max_diag_ssr (A : 'M[FI fs]_n.+1) : FI fs :=
  @max_diag _ _ _ _ fun_of_ssr _ _ succ0_ssr _ A.

Lemma max_diag_correct (A : 'M[FI fs]_n.+1) : (forall i, finite (A i i)) ->
  forall i, (MFI2F A) i i <= FI2F (max_diag_ssr A).
Proof.
move=> HF.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
move=> i; move: i (ltn_ord i).
set P' := fun j (s : FI fs) => forall (i : 'I_n.+1), (i < j)%N ->
  (MFI2F A) i i <= FI2F s; rewrite -/(P' _ _).
suff : (finite (foldl_diag_ssr f (FI0 fs) A)
        /\ P' n.+1 (foldl_diag_ssr f (FI0 fs) A)).
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

Lemma max_diag_pos (A : 'M[FI fs]_n.+1) : (forall i, finite (A i i)) ->
  0 <= FI2F (max_diag_ssr A).
Proof.
move=> HF.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
suff : (finite (foldl_diag_ssr f (FI0 fs) A)
        /\ 0 <= FI2F (foldl_diag_ssr f (FI0 fs) A)).
{ by move=> H; elim H. }
set P := fun (j : nat) s => @finite fs s /\ 0 <= FI2F s.
apply foldl_diag_correct with (P0 := P); rewrite /P.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by case (fimax_spec_eq z (A i i)) => H; rewrite /f -/(fimax _ _) H. }
  by rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ Hind'), fimax_spec_lel. }
by split; [apply finite0|rewrite FI2F0; right].
Qed.

Definition tr_up_ssr (n : nat) : 'M[FI fs]_n.+1 -> FI fs := tr_up.

Lemma tr_up_correct (A : 'M[FI fs]_n.+1) : finite (tr_up_ssr A) ->
  \tr (MF2R (MFI2F A)) <= FI2F (tr_up_ssr A).
Proof.
rewrite /tr_up_ssr /tr_up -/(foldl_diag_ssr _ _ _).
replace (\tr _) with (\sum_(i < n.+1) (FI2F (A (inord i) (inord i)) : R));
  [|by apply eq_big => // i _; rewrite !mxE inord_val].
set P := fun j (s : FI fs) => finite s ->
  (\sum_(i < j) (FI2F (A (inord i) (inord i)) : R)) <= FI2F s.
rewrite -/(P _ _); apply foldl_diag_correct; rewrite /P.
{ move=> i z Hind Fa; move: (fiplus_up_spec Fa); apply Rle_trans.
  rewrite big_ord_recr /= /GRing.add /= inord_val.
  apply Rplus_le_compat_r, Hind, (fiplus_up_spec_fl Fa). }
move=> _; rewrite big_ord0 FI2F0; apply Rle_refl.
Qed.

Definition test_n_ssr : nat -> bool :=
  test_n (fieps fs) (@is_finite fs).

Lemma test_n_correct : test_n_ssr n.+1 -> 4 * INR n.+2 * eps fs < 1.
Proof.
rewrite /test_n_ssr /test_n; set f := _ (fieps _).
move/andP => [Ff Hf]; have Ffeps := fimult_up_spec_fr Ff.
have Fp := fimult_up_spec_fl Ff.
have Ff4 := fimult_up_spec_fl Fp; have Ffn := fimult_up_spec_fr Fp.
apply (Rle_lt_trans _ (FI2F f)).
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
by rewrite FI2F1; right.
Qed.

Definition compute_c_aux_ssr : 'M[FI fs]_n.+1 -> FI fs -> FI fs :=
  compute_c_aux (fieps fs) (fieta fs).

Lemma compute_c_aux_correct (A : 'M[FI fs]_n.+1) maxdiag :
  (INR (2 * n.+2) * eps fs < 1) ->
  (finite (addup (mulup ((nat2Fup (2 * n.+2)%N)) (fieps fs)) (- (1)))%C) ->
  (FI2F (addup (mulup ((nat2Fup (2 * n.+2)%N)) (fieps fs)) (- (1)))%C < 0) ->
  (forall i, 0 <= FI2F (A i i)) ->
  (0 <= FI2F maxdiag) ->
  finite (compute_c_aux_ssr A maxdiag) ->
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + FI2F maxdiag)
  <= FI2F (compute_c_aux_ssr A maxdiag))%R.
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
    by rewrite FI2F1; right. }
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

Definition compute_c_ssr : 'M[FI fs]_n.+1 -> option (FI fs) :=
  compute_c (fieps fs) (fieta fs) (@is_finite fs).

Lemma compute_c_correct (A : 'M[FI fs]_n.+1) :
  (INR (2 * n.+2) * eps fs < 1) ->
  (forall i, finite (A i i)) ->
  (forall i, (0 <= FI2F (A i i))%R) ->
  forall c : FI fs, compute_c_ssr A = Some c ->
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + FI2F (max_diag_ssr A))
   <= FI2F c)%R.
Proof.
move=> Heps Fdiag Pdiag c.
rewrite /compute_c_ssr /compute_c.
set nem1 := addup _ _.
case_eq (is_finite nem1 && (nem1 < 0)%C); [|by []].
rewrite Bool.andb_true_iff => H; elim H => Fnem1 Nnem1.
set c' := compute_c_aux _ _ _ _.
case_eq (is_finite c') => Hite'; [|by []]; move=> Hc'.
have Hc'' : c' = c by injection Hc'.
rewrite -Hc''; apply compute_c_aux_correct => //.
{ eapply (Rlt_le_trans _ (FI2F 0%C)); [|by right; rewrite FI2F0].
  apply filt_spec => //; apply finite0. }
by apply max_diag_pos.
Qed.

Definition posdef_check_ssr : 'M[FI fs]_n.+1 -> bool :=
  posdef_check (fieps fs) (fieta fs) (@is_finite fs).

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
have->: R0 = FI2F (FI0 fs) by rewrite FI2F0.
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
have Hpdiag : forall i, 0 <= FI2F (A i i).
{ move=> i; eapply (Rle_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  by apply file_spec => //; [apply finite0|apply Htpdiag']. }
have HfRt := all_diag_correct HtfRt.
have HtpRt' := all_diag_correct HtpRt.
have HpRt : forall i, 0 < (MFI2F Rt) i i.
{ move=> i; eapply (Rle_lt_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  rewrite mxE; apply filt_spec => //; [apply finite0|apply HfRt|apply HtpRt']. }
move {Htpdiag HtfRt HtpRt Htpdiag' HtpRt'}.
apply corollary_2_4_with_c_upper_bound with
 (maxdiag := FI2F (max_diag_ssr A)) (c := FI2F c') (At0 := At) => //.
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
    /\ (FI2F r : R) *: 1 <=m: diag_mx d.
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
  replace (FI2F r : R)
  with (Rminus (FI2F (A i i)) (Rminus (FI2F (A i i)) (FI2F r))) by ring.
  by apply Rplus_le_compat_l, Ropp_le_contravar, fiminus_down_spec. }
by rewrite GRing.mulr0; right.
Qed.

Definition posdef_check_itv_ssr : 'M[FI fs]_n.+1 -> FI fs -> bool :=
  posdef_check_itv (fieps fs) (fieta fs) (@is_finite fs).

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
apply Mle_trans with (INR n.+1 * FI2F r)%Re%:M.
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
apply (Rle_trans _ (FI2F nr)).
{ apply (Rle_trans _ (FI2F (float_of_nat_up fs n.+1) * FI2F r)).
  { apply Rmult_le_compat_r.
    { change R0 with (F0 fs : R); rewrite -FI2F0; apply file_spec.
      { apply finite0. }
      { move: Fnr; rewrite /nr; apply fimult_up_spec_fr. }
      by move: Pr. }
    by apply float_of_nat_up_spec, (fimult_up_spec_fl Fnr). }
  by apply fimult_up_spec. }
by move: (Hd' i i); rewrite !mxE eq_refl /GRing.natmul /GRing.mul /= Rmult_1_r.
Qed.

Variables (F : Type) (F2FI : F -> FI fs) (toR : F -> R).
Hypothesis (F2FI_correct : forall f, finite (F2FI f) -> FI2F (F2FI f) = toR f :> R).

Global Instance map_mx_ssr : map_mx_class matrix :=
  fun T T' m n f A => matrix.map_mx f A.

Definition posdef_check_F_ssr : 'M[F]_n.+1 -> bool :=
  posdef_check_F (fieps fs) (fieta fs) (@is_finite fs) F2FI.

Definition posdef_check_itv_F_ssr : 'M[F]_n.+1 -> F -> bool :=
  posdef_check_itv_F (fieps fs) (fieta fs) (@is_finite fs) F2FI.

Lemma posdef_check_F_f1 A : posdef_check_F_ssr A ->
  forall i j, finite ((map_mx F2FI A) i j).
Proof. apply posdef_check_f1. Qed.

Lemma posdef_check_itv_F_f1 A r : posdef_check_itv_F_ssr A r ->
  forall i j, finite ((map_mx F2FI A) i j).
Proof. apply posdef_check_itv_f1. Qed.

Lemma posdef_check_F_correct (A : 'M[F]_n.+1) :
  posdef_check_F_ssr A -> posdef (matrix.map_mx toR A).
Proof.
move=> H; move: (posdef_check_correct H).
set A' := MF2R _; set A'' := matrix.map_mx _ _.
have->: A' = A''; [|by []].
apply/matrixP=> i j; rewrite !mxE; apply F2FI_correct.
by move: (posdef_check_f1 H i j); rewrite mxE.
Qed.

Lemma posdef_check_itv_F_correct (A : 'M[F]_n.+1) (r : F) :
  posdef_check_itv_F_ssr A r ->
  forall Xt : 'M_n.+1,
  Mabs (Xt - matrix.map_mx toR A) <=m: matrix.const_mx (toR r) ->
  posdef Xt.
Proof.
move=> H Xt HXt; apply (posdef_check_itv_correct H).
move=> i j; move: (HXt i j); rewrite !mxE F2FI_correct.
{ by rewrite F2FI_correct //; move: H; case/and3P. }
by move: (posdef_check_itv_f1 H i j); rewrite mxE.
Qed.

End theory_cholesky_3.

(** ** Part 3: Parametricity *)

(** *** 3.0 Generalized version of seqmatrix lemmas *)

Section Rseqmx_aux.

Context {A : Type}. (* {ordC : nat -> Type} {mxC : nat -> nat -> Type}. *)
Context `{!zero A}.

(** Version of Rseqmx_fun_of_seqmx not assuming zmodType *)
Instance Rseqmx_fun_of_seqmx' m n :
  param (Rseqmx ==> @Rord m ==> @Rord n ==> Logic.eq) (@matrix.fun_of_matrix A m n) (@fun_of_seqmx A _ m n).
Proof.
rewrite paramE => x a rxa i p <- j q <-.
rewrite /fun_of_seqmx.
by rewrite refines_nth_def.
Qed.

(** Version of Rseqmx_rowseqmx not assuming zmodType *)
Instance Rseqmx_rowseqmx' A m n :
  param (@Rord m ==> Rseqmx ==> Rseqmx) (@matrix.row A m n) (@rowseqmx A m n).
Proof.
rewrite paramE=> i p rip x a rxa.
rewrite /rowseqmx.
apply refines_seqmxP=> //.
case=> //= _.
rewrite refines_nth_col_size //.
rewrite refines_row_size.
by rewrite -rip.
case. case=> //= ? j.
rewrite !mxE.
rewrite -rip.
by rewrite refines_nth.
Qed.

End Rseqmx_aux.

(** *** 3.1 Data refinement *)

Section refinement_cholesky.

(** "C" for "concrete type" *)
Context {C : Type}.
Context `{!zero C, !one C, !add C, !opp C, !mul C, !div C, !sqrt C}.
Local Notation mxC := (seqmatrix' C) (only parsing).

(*
Lemma foldl_iteri_ord T T' n' f x x' s :
  (seq.size s = n'.+1)%N ->
  @foldl T T' f x s =
  iteri_ord (ord := ordinal) (n := n'.+1)
    (seq.size s) (fun i x => f x (nth x' s i)) x.
Proof.
move=> Hsize.
rewrite -[in LHS](take_size s).
eapply iteri_ord_ind =>//; rewrite ?Hsize // ?take0 //.
move=> i s' Hi Hs'.
rewrite -{}Hs'.
rewrite (take_nth x').
Fail rewrite -[RHS]Rcomplements.foldl_rcons.
Admitted. (*
f_equal.
by rewrite Hsize.
Qed. *)
Arguments foldl_iteri_ord [_ _ _ _ _ x' _] _.
*)

Context `{!leq C}.

Lemma param_store_aux n' : param (Rseqmx ==> Rord ==> Logic.eq ==> Rseqmx)
  (fun M j v => @store_ssr C 1%N n' M ord0 j v)
  (fun M j v =>
     match M with
     | [::] => [::]
     | l :: _ => [:: @store_aux C l j v] end).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => j j' param_j.
apply param_abstr => v v' pv; rewrite -(param_eq pv) => {v' pv}.
move: (@refines_row_size _ _ _ _ _ param_M); case_eq M' => // l l' Hl _.
apply /trivial_param /refines_seqmxP => //.
{ move=> i Hi.
  have Hi' : i = 0%N by move: Hi; case i.
  rewrite Hi' /= size_store_aux.
  change l with (nth [::] (l :: l') 0); rewrite -Hl -Hi'.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite Hi' Hl. }
move=> i j''; rewrite (ord_1_0 i) => /= {i}.
move: n' j' M M' param_M j param_j l l' Hl j''.
elim=> [|n' Hn'] j' M M' param_M j param_j l l' Hl j''; [by case j''|].
rewrite /store_seqmx mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hl /=.
case_eq l => [|x t] Hxt; [by rewrite /store_aux nth_nil|].
have St : seq.size t = n'.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (x :: t)); rewrite -Hxt.
  change l with (nth [::] (l :: l') (@ord0 n'.+1)); rewrite -Hl.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hl. }
have Hj' : (j' = j :> nat); [by move: param_j; rewrite paramE|rewrite Hj'].
case_eq (fintype.nat_of_ord j'') => /= [|j'''] Hj'''.
{ by case (fintype.nat_of_ord j). }
case_eq (fintype.nat_of_ord j) => [|j''''] Hj''''.
{ by apply set_nth_default; rewrite -Hj''' -(leq_add2r 1) !addn1 St. }
set M'' := \row_j nth zero0 t j : 'rV_n'.
specialize (Hn' j'''' M'' [:: t]).
have Hlj''' : (j''' < n')%N by rewrite -Hj''' -(leq_add2r 1) !addn1.
have Hlj'''' : (j'''' < n')%N by rewrite -Hj'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((store_ssr M'' ord0 (Ordinal Hlj'''') v) ord0 (Ordinal Hlj''')).
{ replace j''' with (fintype.nat_of_ord (Ordinal Hlj''')) at 2.
  { apply Hn' with (l' := [::]) => //.
    { rewrite paramE; apply refines_seqmxP => //; [by case|move=> i0 j0].
      by rewrite /M'' mxE (ord_1_0 i0) /=; apply set_nth_default; rewrite St. }
    by rewrite paramE /Rord; move: Hlj''''; case j''''. }
  by move: Hlj'''; case j'''. }
rewrite /store_ssr /M'' !mxE /= -(addn1 j''') -(addn1 j'''') eqn_add2r.
by rewrite (@set_nth_default _ _ (M ord0 j'')) // St.
Qed.

Lemma param_store_seqmx0 m n' : param (Rseqmx ==> Rord ==> Rord ==> Logic.eq ==> Rseqmx)
  (@store_ssr C m n') (@store_seqmx0 C).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => i i' param_i.
apply param_abstr => j j' param_j.
apply param_abstr => v v' param_v; rewrite -(param_eq param_v).
apply /trivial_param /refines_seqmxP => //.
{ rewrite size_store_seqmx0; move: param_M; apply refines_row_size. }
{ move=> i'' Hi''; rewrite size_nth_store_seqmx0.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
move: m M M' param_M i i' param_i.
elim=> [|m Hm] M M' param_M i i' param_i; [by case|move=> i'' j''].
rewrite /store_ssr mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
case_eq M' => [|l t] Hlt; [by rewrite !nth_nil|].
have Sl : seq.size l = n'.
{ change l with (nth [::] (l :: t) 0); rewrite -Hlt.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hlt. }
have St : seq.size t = m.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (l :: t)); rewrite -Hlt.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
have Hi' : (i' = i :> nat); [by move: param_i; rewrite paramE|rewrite Hi'].
case_eq (fintype.nat_of_ord i'') => /= [|i'''] Hi'''.
{ case (fintype.nat_of_ord i) => /= [|_].
  { set M'' := \row_j M ord0 j.
    have param_M'' : param Rseqmx M'' [:: l].
    { rewrite paramE; apply /refines_seqmxP => //; [by case|].
      move=> i0 j0; rewrite (ord_1_0 i0) /= /M'' mxE.
      rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
      by apply set_nth_default; rewrite Sl. }
    have H0 := param_apply (param_store_aux n') param_M''.
    have HM'' := param_apply (param_apply H0 param_j) param_v.
    rewrite -(param_eq param_v) in HM'' => {H0}.
    replace (if _ then _ else _) with ((store_ssr M'' ord0 j v) ord0 j'').
    { change (store_aux l j' v) with (nth [::] [:: store_aux l j' v] 0).
      by rewrite (@refines_nth _ _ _ _ _ _ _ HM''). }
    rewrite /store_ssr /M'' !mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
    rewrite Hlt /=; case (_ == _)%B => //.
    by apply set_nth_default; rewrite Sl. }
  by apply set_nth_default; rewrite Sl. }
have Slt : forall i, (i < m)%N -> seq.size (nth [::] t i) = n'.
{ move=> i0 Hi0; change (nth _ _ _) with (nth [::] (l :: t) i0.+1).
  rewrite -Hlt (@refines_nth_col_size _ _ _ _ _ param_M) => //.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
case_eq (fintype.nat_of_ord i) => [|i''''] Hi''''.
{ by apply set_nth_default; rewrite Slt // -Hi'''; move: (ltn_ord i''). }
set M'' := \matrix_(i, j) M (lift ord0 (i : 'I_m)) j.
specialize (Hm M'' t).
have Hli''' : (i''' < m)%N by rewrite -Hi''' -(leq_add2r 1) !addn1.
have Hli'''' : (i'''' < m)%N by rewrite -Hi'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((store_ssr M'' (Ordinal Hli'''') j v) (Ordinal Hli''') j'').
{ replace i''' with (fintype.nat_of_ord (Ordinal Hli''')) at 2.
  { apply Hm.
    { rewrite paramE; apply refines_seqmxP => // i0 j0.
      rewrite /M'' mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt.
      by apply set_nth_default => /=; rewrite Slt. }
    by rewrite paramE; move: Hli''''; case. }
  by move: Hli'''; case. }
rewrite /store_ssr /M'' !mxE /= -(addn1 i''') -(addn1 i'''') eqn_add2r.
rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
by rewrite (@set_nth_default _ _ (M i'' j'')) // Slt.
Qed.

Context {n : nat}.

Global Instance param_store_seqmx :
  param (Rseqmx ==> Rord ==> Rord ==> Logic.eq ==> Rseqmx)
    (@store_ssr C n.+1 n.+1) (@store_seqmx0 C).
Proof. apply param_store_seqmx0. Qed.

Global Instance param_dotmulB0 :
  param (Rord ==> Logic.eq ==> Rseqmx ==> Rseqmx ==> Logic.eq)
  (@dotmulB0_ssr _ _ _ _ n.+1) (@dotmulB0 C ord_instN _ _ n.+1).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
rewrite paramE in param_c; rewrite -{c'}param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
rewrite paramE /dotmulB0 /= /dotmulB0_seqmx.
case: k param_k => [k Hk] param_k.
rewrite paramE /Rord /= in param_k; rewrite -{k'}param_k.
have := @refines_row_size _ _ _ _ _ param_a.
case Ea' : a' => [//|a'0 a'1]; case: a'1 Ea' =>//= Ea' _.
have := @refines_row_size _ _ _ _ _ param_b.
case Eb' : b' => [//|b'0 b'1]; case: b'1 Eb' =>//= Eb' _.
elim: n k Hk a b c a' b' a'0 param_a Ea' b'0 param_b Eb'
  => [|n' IHn'] k Hk a b c a' b' a'0 param_a Ea' b'0 param_b Eb'.
{ by rewrite /fsum_l2r_rec /=; case: k Hk. }
have := @refines_nth_col_size _ _ _ _ _ param_a 0.
rewrite refines_row_size Ea'; move/(_ erefl) => /=.
case Ea'0 : a'0 => [//|a'00 a'01] Ha'0; simpl in Ha'0.
have := @refines_nth_col_size _ _ _ _ _ param_b 0.
rewrite refines_row_size Eb'; move/(_ erefl) => /=.
case Eb'0 : b'0 => [//|b'00 b'01] Hb'0; simpl in Hb'0.
case: k Hk => //= k Hk; set cc := (c + - _)%C.
have Hk1 : (k < n'.+1)%N by rewrite -ltnS.
rewrite <-(IHn' k Hk1 (\row_(i < n'.+1) a ord0 (lift ord0 i))
                      (\row_(i < n'.+1) b ord0 (lift ord0 i)) cc
                      [:: behead a'0] [:: behead b'0]).
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE /cc.
  { repeat f_equal.
    { by rewrite -(refines_nth _ _ param_a) Ea' Ea'0 /= inordK. }
    by rewrite -(refines_nth _ _ param_b) Eb' Eb'0 /= inordK. }
  f_equal; apply f_equal2; rewrite mxE; f_equal; apply ord_inj.
  { rewrite inordK /=.
    { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
    rewrite /bump; case (0 <= i)%N => /=.
    { by rewrite add1n ltnS; apply (ltn_trans (ltn_ord _)). }
    by rewrite add0n; apply (ltn_trans (ltn_ord _)), leqW. }
  rewrite inordK /=.
  { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
  rewrite /bump; case (0 <= i)%N => /=.
  { by rewrite add1n ltnS; apply (ltn_trans (ltn_ord _)). }
  by rewrite add0n; apply (ltn_trans (ltn_ord _)), leqW. }
{ rewrite paramE; apply/refines_seqmxP=> //.
  { move=> i; rewrite ltnS leqn0; move/eqP=> -> /=.
    by rewrite Ea'0 /=; apply eq_add_S. }
  move=> i j; rewrite !mxE (ord_1_0 i) /= -[in RHS](refines_nth _ _ param_a).
  rewrite nth_behead Ea'; f_equal. }
{ by rewrite Ea'0. }
{ rewrite paramE; apply/refines_seqmxP=> //.
  { move=> i; rewrite ltnS leqn0; move/eqP=> -> /=.
    by rewrite Eb'0 /=; apply eq_add_S. }
  move=> i j; rewrite !mxE (ord_1_0 i) /= -[in RHS](refines_nth _ _ param_b).
  rewrite nth_behead Eb'; f_equal. }
by rewrite Eb'0.
Qed.

Global Instance param_ytilded :
  param (Rord ==> Logic.eq ==> Rseqmx ==> Rseqmx ==> Logic.eq ==> Logic.eq)
  (ytilded_ssr (n := n)) (ytilded_seqmx (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
eapply param_abstr => bk bk' param_bk.
rewrite /ytilded_ssr /ytilded_seqmx /ytilded.
eapply param_apply; last by tc.
eapply param_apply.
rewrite paramE; by move=> ? ? h1 ? ? h2; rewrite h1 h2.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
by tc.
Qed.

Global Instance param_ytildes :
  param (Rord ==> Logic.eq ==> Rseqmx ==> Logic.eq)
  (ytildes_ssr (n := n)) (ytildes_seqmx (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
rewrite /ytildes_ssr /ytildes_seqmx /ytildes.
eapply param_apply; last by tc.
by rewrite paramE; move=> ? ? ->.
Qed.

Lemma param_iteri_ord :
  forall T T', forall RT : T -> T' -> Prop,
  param ((fun j j' => j = j' /\ (j <= n.+1)%N) ==> (Rord ==> RT ==> RT) ==> RT
  ==> RT)
  (@iteri_ord _ n.+1 I0_ssr succ0_ssr T) (@iteri_ord _ n.+1 I0_instN succ0_instN T').
Proof.
move=> T T' RT.
apply param_abstr => j j' param_j.
rewrite paramE in param_j; destruct param_j as (Hj', Hj); rewrite -Hj'.
eapply param_abstr => f f' param_f.
apply param_abstr => x x'.
apply (iteri_ord_ind2 (M := T) (M' := T') (j := j)) => //.
move=> i i' s s' Hi Hi'.
apply param_apply.
have: param Rord i i'.
{ by move: Hi'; rewrite paramE /Rord /nat_of /nat_of_ord. }
by apply param_apply.
Qed.

Lemma param_inner_loop :
  param (Rord ==> Rseqmx ==> Rseqmx ==> Rseqmx)
  (inner_loop_ssr (n := n)) (inner_loop_seqmx (n := n)).
Proof.
apply param_abstr => j j' param_j.
rewrite paramE /Rord in param_j; rewrite -param_j => {j' param_j}.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /inner_loop_ssr /inner_loop_seqmx /inner_loop.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ eapply param_apply; [by apply param_iteri_ord|].
  rewrite paramE; split; [by []|].
  rewrite /nat_of /nat_of_ord; apply ltnW, ltn_ord. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ eapply param_apply; [|exact param_i].
  eapply param_apply.
  { by eapply param_apply; [apply param_store_seqmx|]. }
  by rewrite paramE. }
eapply param_apply.
{ eapply param_apply.
  { eapply param_apply.
    { eapply param_apply.
      { by eapply param_apply; [apply param_ytilded|exact param_i]. }
      eapply param_apply.
      { eapply param_apply; [|exact param_i].
        by eapply param_apply; [apply Rseqmx_fun_of_seqmx'|apply param_A]. }
      by rewrite paramE. }
    eapply param_apply; [|exact param_s].
    eapply param_apply; [apply Rseqmx_rowseqmx'|exact param_i]. }
  eapply param_apply; [|exact param_s].
  eapply param_apply; [apply Rseqmx_rowseqmx'|by rewrite paramE]. }
do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_s].
Qed.

Lemma param_outer_loop :
  param (Rseqmx ==> Rseqmx ==> Rseqmx)
  (outer_loop_ssr (n := n)) (outer_loop_seqmx (n := n)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /outer_loop_ssr /outer_loop_seqmx /outer_loop.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => j j' param_j.
apply param_abstr => s s' param_s.
have Hin : param Rseqmx (inner_loop_ssr j A s) (inner_loop_seqmx (n := n) j' As s').
{ eapply param_apply; [|exact param_s].
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_inner_loop|exact param_j]. }
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_j]).
  by eapply param_apply; [apply param_store_seqmx|]. }
eapply param_apply.
{ eapply param_apply.
  { eapply param_apply; [apply param_ytildes|exact param_j]. }
  do 2 (eapply param_apply; [|exact param_j]).
  eapply param_apply; [|exact param_A].
  apply Rseqmx_fun_of_seqmx'. }
eapply param_apply; [|apply Hin].
eapply param_apply; [apply Rseqmx_rowseqmx'|exact param_j].
Qed.

Global Instance param_cholesky :
  param (Rseqmx ==> Rseqmx) (cholesky_ssr (n := n)) (cholesky_seqmx (n := n)).
Proof.
apply param_abstr => A As param_A.
rewrite /cholesky_ssr /cholesky_seqmx /cholesky.
do 2 (eapply param_apply; [|exact param_A]).
apply param_outer_loop.
Qed.

End refinement_cholesky.

(* FIXME: closing/opening a new section should be unnecessary here *)
Section refinement_cholesky_2.
(* C := FI fs *)

Context {fs : Float_round_up_infnan_spec}.

Context {n : nat}.

(* FIXME: D.R.Y *)
Variables (F : Type) (F2FI : F -> FI fs) (toR : F -> R).
Hypothesis (F2FI_correct : forall f, finite (F2FI f) -> FI2F (F2FI f) = toR f :> R).

Lemma param_heq_op :
  param (Rseqmx ==> Rseqmx ==> Logic.eq)
  (heq_op (heq := @heq_instFI_ssr fs) (m := n.+1) (n := n.+1))
  (heq_op (heq := @eq_seqmx _ _) (m := n.+1) (n := n.+1)).
Proof.
apply param_abstr => A1 A1s param_A1.
apply param_abstr => A2 A2s param_A2.
have SA1s : seq.size A1s = n.+1 by move: param_A1; apply refines_row_size.
have SA2s : seq.size A2s = n.+1 by move: param_A2; apply refines_row_size.
have SzAs : seq.size (zip A1s A2s) = n.+1.
{ by rewrite size1_zip; rewrite SA1s; [|rewrite SA2s]. }
have SA1si : forall i : 'I_n.+1, seq.size (nth [::] A1s i) = n.+1.
{ move=> i; rewrite refines_nth_col_size // SA1s; apply ltn_ord. }
have SA2si : forall i : 'I_n.+1, seq.size (nth [::] A2s i) = n.+1.
{ move=> i; rewrite refines_nth_col_size // SA2s; apply ltn_ord. }
rewrite paramE /heq_op /eq_seqmx /eq_seqmx.
set b := eq_seq _ _ _.
apply /forallP; case_eq b => Hb.
{ move=> i; apply /forallP => j.
  move: Hb; rewrite /b eq_seqE; [|by rewrite SA1s SA2s].
  move /all_nthP => Ha.
  have Hi : (i < seq.size (zip A1s A2s))%N by rewrite SzAs; apply ltn_ord.
  specialize (Ha ([::], [::]) i Hi); move: Ha; rewrite eq_seqE.
  { move /all_nthP; set s := zip _ _; move=> Ha.
    have Hs' : seq.size s = n.+1.
    { rewrite /s nth_zip /=; [|by rewrite SA1s SA2s].
      by rewrite size1_zip; rewrite SA1si; [|rewrite SA2si]. }
    have Hj : (j < seq.size s)%N by rewrite Hs'; apply ltn_ord.
    specialize (Ha (A1 i j, A2 i j) j Hj).
    rewrite /s !nth_zip /= in Ha; first last.
    - by rewrite SA1s SA2s.
    - by rewrite SA1si SA2si.
    - by rewrite SA1s SA2s.
    rewrite (@refines_nth _ _ _ _ _ _ _ param_A1) in Ha.
    by rewrite (@refines_nth _ _ _ _ _ _ _ param_A2) in Ha. }
  by rewrite nth_zip /=; [rewrite SA1si SA2si|rewrite SA1s SA2s]. }
move=> Ha.
rewrite /b eq_seqE in Hb; [|by rewrite SA1s SA2s].
move: Hb; set al := all _ _; suff: al = true; [|rewrite /al].
{ by move=> Hal; rewrite Hal. }
apply /(all_nthP ([::], [::])) => i Hi; specialize (Ha (inord i)).
have Hii : (i = @inord n i)%N by rewrite inordK; [|rewrite SzAs in Hi].
rewrite nth_zip /=; [|by rewrite SA1s SA2s].
rewrite eq_seqE; [|by rewrite Hii SA1si SA2si].
apply /(all_nthP (FI0 fs, FI0 fs)) => j Hj.
have Hsz : seq.size (zip (nth [::] A1s i) (nth [::] A2s i)) = n.+1.
{ by rewrite size1_zip; rewrite Hii SA1si; [|rewrite SA2si]. }
have Hjj : (j = @inord n j)%N by rewrite inordK; rewrite Hsz in Hj.
rewrite Hii Hjj nth_zip /=; [|by rewrite SA1si SA2si].
rewrite (set_nth_default (A1 (inord i) (inord j)) (FI0 _)); [|by rewrite SA1si].
rewrite (set_nth_default (A2 (inord i) (inord j)) (FI0 _)); [|by rewrite SA2si].
by rewrite !refines_nth; move /forallP in Ha; specialize (Ha (inord j)).
Qed.

(* FIXME: remove @, _, etc. *)

Lemma param_is_sym :
  param (Rseqmx ==> Logic.eq)
  (@is_sym _ _ n.+1 (@heq_instFI_ssr fs) (@trmx _))
  (@is_sym _ _ n.+1 (@eq_seqmx _ (@eq_instFI _)) transpose_seqmx).
Proof.
apply param_abstr => A As param_A.
rewrite /is_sym.
eapply param_apply; [|exact param_A].
eapply param_apply; [apply param_heq_op|].
eapply param_apply; [apply Rseqmx_trseqmx|exact param_A].
Qed.

Lemma param_foldl_diag T' :
  param (Logic.eq ==> Logic.eq ==> Rseqmx ==> Logic.eq)
  (@foldl_diag _ _ matrix (@fun_of_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n) T')
  (@foldl_diag _ _ seqmatrix' (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1
     (@I0_instN n) (@succ0_instN n) T').
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => x x' param_x.
apply param_abstr => A As param_A.
rewrite /foldl_diag.
eapply param_apply; [|exact param_x].
eapply param_apply.
{ rewrite -/iteri_ord_ssr.
  by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
rewrite !paramE in param_f, param_s; rewrite param_f param_s paramE.
apply f_equal, paramP; do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_all_diag :
  param (Logic.eq ==> Rseqmx ==> Logic.eq)
  (@all_diag _ _ _ (@fun_of_ssr _) n.+1 (@I0_ssr n) (@succ0_ssr n))
  (@all_diag _ _ seqmatrix'
     (@fun_of_seqmx _ (@zero_instFI fs)) n.+1 (@I0_instN n)
     (@succ0_instN n)).
Proof.
apply param_abstr => f f' param_f; rewrite paramE in param_f; rewrite param_f.
apply param_abstr => A As param_A.
rewrite /all_diag.
eapply param_apply; [|exact param_A].
do 2 (eapply param_apply; [|apply param_eq_refl]).
apply param_foldl_diag.
Qed.

Lemma param_max_diag :
  param (Rseqmx ==> Logic.eq)
  (@max_diag _ _ _ (FI0 fs)
     (@fun_of_ssr (FI fs)) n.+1 (@I0_ssr n) (@succ0_ssr n)
     (@leq_instFI fs))
  (@max_diag _ _ seqmatrix' (FI0 fs)
     (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1 (@I0_instN n)
     (@succ0_instN n) leq_instFI).
Proof.
apply param_abstr => A As param_A.
rewrite /max_diag.
eapply param_apply; [|exact param_A].
do 2 (eapply param_apply; [|apply param_eq_refl]).
apply param_foldl_diag.
Qed.

Lemma param_compute_c_aux :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@compute_c_aux _ _ _ (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs))
  (@compute_c_aux _ _ seqmatrix' (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1
     (@I0_instN n) (@succ0_instN n) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => x x' param_x.
rewrite paramE /compute_c_aux; apply f_equal2; apply f_equal; [|apply f_equal].
{ apply paramP; eapply param_apply; [|exact param_A].
  rewrite /tr_up; do 2 (eapply param_apply; [|apply param_eq_refl]).
  apply param_foldl_diag. }
by move: param_x; rewrite paramE.
Qed.

Lemma param_compute_c :
  param (Rseqmx ==> Logic.eq)
  (@compute_c (FI fs) _ _
     (@zero_instFI fs) (@one_instFI fs) (@opp_instFI fs)
     (@fun_of_ssr (FI fs)) n.+1 (@I0_ssr n)
     (@succ0_ssr n) (@leq_instFI fs) (@lt_instFI fs) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs) (@is_finite fs))
  (@compute_c _ _ seqmatrix'
     zero_instFI one_instFI opp_instFI
     (@fun_of_seqmx _ zero_instFI) n.+1 (@I0_instN n)
     (@succ0_instN n) leq_instFI lt_instFI (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /compute_c /C.
case (_ && _) => //.
set cc := compute_c_aux _ _ A _.
set cc' := compute_c_aux _ _ As _.
have Hcccc' : cc = cc'; [rewrite /cc /cc'|by rewrite Hcccc'].
apply paramP; apply (param_apply (R:=Logic.eq)).
{ eapply param_apply; [apply param_compute_c_aux|exact param_A]. }
eapply param_apply; [apply param_max_diag|exact param_A].
Qed.

Lemma param_map_diag :
  param ((Logic.eq ==> Logic.eq) ==> Rseqmx ==> Rseqmx)
  (@map_diag _ _ _
     (@fun_of_ssr (FI fs)) (@store_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n))
  (@map_diag _ _ seqmatrix'
     (@fun_of_seqmx _ zero_instFI) (@store_seqmx _) n.+1
     (@I0_instN n) (@succ0_instN n)).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => A As param_A.
rewrite /map_diag.
eapply param_apply; [|exact param_A].
eapply param_apply.
{ by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_i]).
  eapply param_apply; [apply param_store_seqmx|exact param_s]. }
eapply param_apply; first exact: param_f.
do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_posdef_check :
  param (Rseqmx ==> Logic.eq)
  (@posdef_check_ssr fs n)
  (posdef_check_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /posdef_check_ssr /posdef_check_seqmx /posdef_check.
repeat f_equal =>//.
{ by apply param_eq; eapply param_apply; [apply param_is_sym|exact param_A]. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set c := compute_c _ _ _ A.
set c' := compute_c _ _ _ As.
have Hcc' : c = c'; [|rewrite -Hcc'; case c => // {c c' Hcc'} c].
{ rewrite /c /c'; apply paramP.
  eapply param_apply; [apply param_compute_c|exact param_A]. }
set R := cholesky _; set Rs := cholesky _; apply paramP.
suff param_R : param Rseqmx R Rs; [|rewrite /R /Rs].
{ rewrite paramE; apply f_equal2; apply paramP.
  { eapply param_apply; [|exact param_R].
    eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
  rewrite /pos_diag; eapply param_apply; [|exact param_R].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set At := map_diag _ A; set Ats := map_diag _ As.
suff: param Rseqmx At Ats; [|rewrite /At /Ats].
{ rewrite -/cholesky_seqmx -/cholesky_ssr; apply param_apply, param_cholesky. }
eapply param_apply; [|exact param_A].
eapply param_apply; [exact param_map_diag|].
by eapply param_fun_eq; rewrite paramE.
Qed.

Lemma param_posdef_check_itv :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@posdef_check_itv_ssr fs n)
  (posdef_check_itv_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite paramE /posdef_check_itv_ssr /posdef_check_itv_seqmx /posdef_check_itv /posdef_check.
repeat apply f_equal2 =>//.
{ apply param_eq; eapply param_apply; first by apply param_is_sym.
  eapply param_apply; last by tc.
  eapply param_apply; first exact: param_map_diag.
  (* This could be simplified with a param lemma for sub_down *)
  rewrite paramE => a b Hab; repeat f_equal =>//. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply.
  eapply param_apply; [by apply param_all_diag|apply param_eq_refl].
  eapply param_apply; last exact: param_A.
  eapply param_apply; first eapply param_map_diag.
  rewrite paramE => a b Hab; repeat f_equal =>//. }
set c := compute_c _ _ _ (_ _ A).
set c' := compute_c _ _ _ (map_diag _ As).
have Hcc' : c = c'; [|rewrite -Hcc'; case c => // {c c' Hcc'} c].
{ rewrite /c /c'; apply paramP.
  eapply param_apply; [by apply param_compute_c|].
  eapply param_apply; last exact: param_A.
  eapply param_apply; first exact param_map_diag.
  rewrite paramE => a b Hab; repeat f_equal => //. }
set R := cholesky _; set Rs := cholesky _; apply paramP.
suff param_R : param Rseqmx R Rs; [|rewrite /R /Rs].
{ rewrite paramE; apply f_equal2; apply paramP.
  { eapply param_apply; [|exact param_R].
    eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
  rewrite /pos_diag; eapply param_apply; [|exact param_R].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set At := map_diag _ A; set Ats := map_diag _ As.
suff HA : param Rseqmx At Ats; [|rewrite /At /Ats].
{ rewrite -/cholesky_seqmx -/cholesky_ssr.
  eapply param_apply; first exact: param_cholesky.
  eapply param_apply; last exact: HA.
  eapply param_apply; [eapply param_map_diag|].
  by apply param_fun_eq, param_eq_refl. }
eapply param_apply; last exact: param_A.
eapply param_apply; first exact: param_map_diag.
rewrite paramE => a b Hab; repeat f_equal => //.
Qed.

(** Version of [Rseqmx_map_seqmx] not assuming identical input and return types for [f] *)
Lemma param_map_mx m n'' T T' :
  param (Logic.eq ==> Rseqmx ==> Rseqmx)
    (@map_mx_ssr T T' m n'')
    (@map_mx_seqmx T T' m n'').
Proof.
rewrite paramE => f _ <- x a rxa.
apply /refines_seqmxP=> [|i lt_im|i j].
{ by rewrite !sizeE. }
{ by rewrite (nth_map [::]) !sizeE. }
rewrite mxE (nth_map [::]) ?sizeE //.
by rewrite (nth_map (x i j)) ?sizeE // refines_nth.
Qed.

Lemma param_posdef_check_F :
  param (Rseqmx ==> Logic.eq)
  (@posdef_check_F_ssr fs n _ F2FI)
  (posdef_check_F_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
rewrite /posdef_check_F_ssr /posdef_check_F_seqmx /posdef_check_F.
eapply param_apply; [apply param_posdef_check|].
eapply param_apply; [|apply param_A].
eapply param_apply; [apply param_map_mx|apply param_eq_refl].
Qed.

(* FIXME: to rename *)

Definition posdef_check_itv_F5 := @posdef_check_itv_F_ssr fs n _ F2FI.

Lemma param_posdef_check_itv_F :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@posdef_check_itv_F_ssr fs n _ F2FI)
  (posdef_check_itv_F_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite /posdef_check_itv_F_ssr /posdef_check_itv_F_seqmx /posdef_check_itv_F.
eapply param_apply; [|apply param_eq_refl].
eapply param_apply; [apply param_posdef_check_itv|].
eapply param_apply; [|apply param_A].
eapply param_apply; [apply param_map_mx|apply param_eq_refl].
Qed.

End refinement_cholesky_2.

(* FIXME: to move *)
Require Import BigQ.
Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_xreal.
(*Module F := SpecificFloat BigIntRadix2.*)
Local Open Scope bigZ_scope.
Require Import coqinterval_infnan.
Require Import Interval.Interval_missing.

Notation toR := (fun f => proj_val (F.toX f)).

(** *** 3.2 Data refinement with CoqInterval datatypes *)
Section refinement_cholesky_3.

Let fis := coqinterval_infnan.coqinterval_infnan.

Definition eps_inv := Eval compute in (2 ^ 53)%bigZ.

Lemma eps_inv_correct : (Z2R [eps_inv]%bigZ <= / eps fis)%Re.
Proof. by rewrite /= /flx64.eps /= Rinv_involutive; [right|lra]. Qed.

Definition F2FI_val (f : F.type) : F.type :=
  match f with
    | Interval_specific_ops.Fnan => Interval_specific_ops.Fnan
    | Interval_specific_ops.Float m e =>
      if (BigZ.abs m <? eps_inv)%bigZ then f else Interval_specific_ops.Fnan
  end.

Lemma F2FI_proof (x : F.type) : mantissa_bounded (F2FI_val x).
Proof.
unfold mantissa_bounded, x_bounded, F2FI_val.
case x; [now left|intros m e].
set (c := BigZ.ltb _ _); case_eq c; intro Hc; [right|now left].
exists (@F2R radix2 {| Fnum := [m]%bigZ; Fexp := [e]%bigZ |}).
{ unfold F.toX, FtoX, F.toF.
  assert (Hm := Bir.mantissa_sign_correct m); revert Hm.
  set (s := _ m); case_eq s; unfold Bir.MtoZ, F2R.
  { now intros Hs Hm; rewrite Hm; rewrite Rmult_0_l. }
  intros s' p Hp (Hm, Hm'); rewrite Hm; simpl; unfold Bir.EtoZ, FtoR, bpow.
  case [e]%bigZ.
  { now rewrite Rmult_1_r; case s'. }
  { now intro p'; rewrite Z2R_mult; case s'. }
  now intro p'; case s'. }
revert Hc; unfold c; clear c; rewrite BigZ.ltb_lt; intro Hm.
apply FLX_format_generic; [exact refl_equal|].
set (f := {| Fnum := _; Fexp := _ |}).
apply generic_format_F2R' with f; [reflexivity|intro Hf].
unfold canonic_exp, FLX_exp; rewrite Z.le_sub_le_add_r; apply ln_beta_le_bpow.
{ exact Hf. }
unfold F2R, f; simpl.
rewrite Rabs_mult; rewrite (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
apply (Rmult_lt_reg_r (bpow radix2 (-[e]%bigZ))); [now apply bpow_gt_0|].
rewrite Rmult_assoc; rewrite <- !bpow_plus.
replace (_ + - _)%Z with Z0 by ring; rewrite Rmult_1_r.
replace (_ + _)%Z with 53%Z by ring.
rewrite <- Z2R_abs; unfold bpow; apply Z2R_lt.
now revert Hm; unfold eps_inv, Z.pow_pos; simpl; rewrite <- BigZ.spec_abs.
Qed.

Definition F2FI (f : F.type) : FI := Build_FI _ (F2FI_proof f).

Lemma real_FtoX_toR f : F.real f -> F.toX f = Xreal (toR f).
Proof. by rewrite FtoX_real; rewrite /X_real; case: F.toX. Qed.

Lemma F2FI_correct (f : F.type) : finite (F2FI f) -> FI2F (F2FI f) = toR f :> R.
Proof.
case f => // m e.
rewrite /finite FtoX_real /FI2F.
case (FI_prop (F2FI (Float m e))) => Hf; [by rewrite Hf|].
destruct Hf as (r, Hr, Hr'); move=> HF /=.
suff: Xreal r = Xreal (proj_val (F.toX (Float m e))).
{ by move=> H; inversion H. }
by move: HF; rewrite -real_FtoX_toR // -Hr /F2FI /=; case (_ <? _).
Qed.

(* Erik: A little test to know which FI are in play:

Goal zero FI.
Fail by tc.
change FI with (float_infnan_spec.FI coqinterval_infnan.coqinterval_infnan).
tc.
Qed.
*)

(* Let's override FI for now...! *)
Local Notation FI := (float_infnan_spec.FI coqinterval_infnan.coqinterval_round_up_infnan).

(* FIXME: to rename *)
Definition posdef_check4_coqinterval' (M : seq (seq FI)) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) M.

Definition posdef_check_F4_coqinterval' (M : seq (seq F.type)) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_F_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) F2FI M.

Definition posdef_check_itv4_coqinterval' (M : seq (seq FI)) (r : FI) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_itv_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) M r.

Definition posdef_check_itv_F4_coqinterval' (M : seq (seq F.type)) (r : F.type) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_itv_F_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) F2FI M r.

Definition prec := 53%bigZ.

Definition BigQ2F (q : bigQ) : F.type * F.type :=
  match q with
  | BigQ.Qz m => let m0 := Interval_specific_ops.Float m Bir .exponent_zero in (m0, m0)
  | BigQ.Qq m n => let m0 := Interval_specific_ops.Float m Bir.exponent_zero in
                   let n0 := Interval_specific_ops.Float (BigZ.Pos n) Bir.exponent_zero in
                   (F.div rnd_DN prec m0 n0, F.div rnd_UP prec m0 n0)
  end.

Lemma toR_Float (m e : bigZ) : toR (Float m e) = (Z2R [m]%bigZ * bpow F.radix [e])%Re.
Proof.
rewrite /F.toX /F.toF /=.
have := Bir.mantissa_sign_correct m.
case E_m: (Bir.mantissa_sign m) => [|s m']; last case.
  by rewrite /Bir.MtoZ =>-> /=; rewrite Rsimpl.
rewrite /proj_val /FtoX.
rewrite (FtoR_split radix2 s (Bir.MtoP m') ((* Bir.EtoZ *) [e])).
rewrite /F2R /= /cond_Zopp => H1 H2; congr Rmult.
move: H1; case: (s) => H1.
by rewrite Pos2Z.opp_pos -H1.
by rewrite -H1.
Qed.

Definition test_posdef_check_itv (M : seq (seq F.type)) (r : bigQ) : bool :=
  posdef_check_itv_F4_coqinterval' M (snd (BigQ2F r)).

(* Remark: ultimately, we'll have to check that mat does not contain NaNs *)

(*
Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (@mx_of_seqmx_val _ R0 m m (map (map toR) mat)).
*)

Instance : zero F.type := F.zero.

Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (matrix.map_mx toR (mx_of_seqmx_val m m mat)).

(* First attempt
Context `{mx : Type -> nat -> nat -> Type, !map_mx_class mx}.
Context `{!heq (mx FI)}.
Context `{!transpose_class (mx FI)}.
Context `{ordT : nat -> Type, !fun_of FI ordT (mx FI)}.
Context `{!row_class ordT (mx FI)}.
Typeclasses eauto := debug.
*)

Lemma posdef_check_F_correct_inst (A : seqmatrix F.type) :
  posdef_check_F4_coqinterval' A ->
  posdef_seqF A.
Proof.
case: A => [|A0 A1].
{ by move=> _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> Hmain.
eapply (@posdef_check_F_correct coqinterval_round_up_infnan).
{ by apply F2FI_correct. }
rewrite /posdef_check_F4_coqinterval' in Hmain.
have /andP[Hall Hmain'] := Hmain.
rewrite /is_true -Hmain' /posdef_check_F4_coqinterval'.
apply paramP.
eapply param_apply; first exact: param_posdef_check_F.
move/all_nthP in Hall.
apply/trivial_param/refines_seqmxP; rewrite -/(seq.size _); first done.
by move=> i Hi; move/(_ [::] i Hi)/eqP in Hall.
move=> [i Hi] j /=; rewrite !mxE.
apply: set_nth_default.
by move/(_ [::] i Hi)/eqP: Hall =>->.
Qed.

Definition posdef_itv_seqF (mat : seqmatrix F.type) (r : F.type) : Prop :=
  let m := seq.size mat in
  forall Xt : 'M_m,
  Mabs (Xt - matrix.map_mx toR (@mx_of_seqmx_val _ _ m m mat))
    <=m: matrix.const_mx (toR r) ->
  posdef Xt.

Lemma posdef_check_itv_F_correct_inst (A : seqmatrix F.type) (r : F.type) :
  let m := seq.size A in
  posdef_check_itv_F4_coqinterval' A r ->
  posdef_itv_seqF A r.
Proof.
case: A => [|A0 A1].
{ by move=> _ _ Xt _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> m Hmain Xt.
set mA := mx_of_seqmx_val _ _ _.
change (proj_val (F.toX r)) with (toR r).
apply (posdef_check_itv_F_correct (fs := coqinterval_round_up_infnan) (F2FI := F2FI)).
- exact: F2FI_correct.
- rewrite /posdef_check_F4_coqinterval' in Hmain.
  have /andP[Hall Hmain'] := Hmain.
  rewrite /is_true -Hmain' /posdef_check_F4_coqinterval'.
  apply paramP.
  eapply param_apply; [eapply param_apply|exact: param_eq_refl].
  { exact: param_posdef_check_itv_F. }
  move/all_nthP in Hall.
  apply/trivial_param/refines_seqmxP; rewrite -/(seq.size _); first done.
  by move=> i Hi; move/(_ [::] i Hi)/eqP in Hall.
  move=> [i Hi] j /=; rewrite !mxE.
  apply: set_nth_default.
  by move/(_ [::] i Hi)/eqP: Hall =>->.
Qed.

Require Import QArith.
Local Coercion RMicromega.IQR : Q >-> R.
Local Coercion BigQ.to_Q : bigQ >-> Q.

Definition posdef_itv_seqF_bigQ (mat : seqmatrix F.type) (r : bigQ) : Prop :=
  let m := seq.size mat in
  forall Xt : 'M_m,
  Mabs (Xt - matrix.map_mx toR (@mx_of_seqmx_val _ _ m m mat))
    <=m: matrix.const_mx (r : R) ->
  posdef Xt.

Lemma test_posdef_check_itv_correct (A : seqmatrix F.type) (r : bigQ) :
  let m := seq.size A in
  test_posdef_check_itv A r ->
  posdef_itv_seqF_bigQ A r.
Admitted.

End refinement_cholesky_3.

Ltac prove_posdef :=
  (by apply posdef_check_F_correct_inst; abstract (vm_cast_no_check (erefl true)))
  || fail "Numerical evaluation failed to prove positive-definiteness".

Ltac prove_posdef_itv :=
  (by apply posdef_check_itv_F_correct_inst; abstract (vm_cast_no_check (erefl true)))
  || fail "Numerical evaluation failed to prove positive-definiteness".

Require Import testsuite.

Lemma test_m12 : posdef_seqF m12.
Time prove_posdef.
Qed.

Lemma test_m12_r : posdef_itv_seqF m12 (Float 1%bigZ (-10)%bigZ).
Time prove_posdef_itv.
Qed.
