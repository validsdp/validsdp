(** * Bounds on the rounding error of dotproduct $c - \sum_{i=0}^k a_i b_i$#c - \sum_{i=0}^k a_i b_i#

    Notations are similar to the one in [fsum]. *)

Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import binary64_infnan.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.
Require Import binary64_infnan.

Require Import ZArith.
Require Import Flocq.Core.Fcore Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.

(** Tip to leverage a Boolean condition *)
Definition optb (b : bool) : option (is_true b) :=
  if b then Some erefl else None.
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true
  then left erefl else right erefl.

(* Slow!

Definition fhalf : full_float :=
  F754_finite false 1 (-1).
Print valid_binary.
Definition bhalf : binary64 :=
  (* FF2B 53 1024 fhalf (refl_equal true). *)
  binary_normalize 53 1024 (refl_equal Lt) (refl_equal Lt) mode_NE 1 (-1) false.
Compute b64_mult mode_NE bhalf bhalf.
*)

Definition b64_normalize (f : float radix2) :=
  binary_normalize 53 1024 (refl_equal Lt) (refl_equal Lt) mode_NE (Fnum f) (Fexp f) false.

Definition B2F {p emax} (x : binary_float p emax) : float radix2 :=
  match x with
  | B754_finite s m e _ => Float radix2 (cond_Zopp s (Zpos m)) e
  | _ => Float radix2 0 0
  end.

Definition Z2B (n : Z) := b64_normalize (Float radix2 n 0).

(*
Definition b64_finite_pos {p emax} (x : binary_float p emax) : bool :=
  match x with
  | B754_finite s m e _ =>
  | _ => false
  end.
*)

Require Import Flocq.Calc.Fcalc_ops.

Definition half := b64_normalize (Float radix2 1 (-1)).
Definition one := b64_plus mode_NE half half.
(**
Time Eval vm_compute in B2F one.

Time Eval vm_compute in B2F (fisqrt (Z2B 4)).

Time Eval vm_compute in is_finite _ _ (b64_normalize (Float radix2 1 4096)).

Time Eval vm_compute in is_nan _ _ (fisqrt (b64_normalize (Float radix2 (-1) 0))).
*)
Definition F64 := binary64_infnan.


(** This could (should) be generalized *)
Let prec := 53%Z.
Let emax := 1024%Z.

Notation emin := (3 - emax - prec)%Z (only parsing).
Notation fexp := (FLT_exp emin prec) (only parsing).

Arguments B754_zero [prec] [emax] _.
Arguments B754_infinity [prec] [emax] _.
Arguments B754_nan [prec] [emax] _ _.
Arguments B754_finite [prec] [emax] _ _ _ _.

(* Check (FF2B, B2FF, FF2B_B2FF, B2FF_inj, valid_binary_B2FF). *)

Arguments FF2B [prec] [emax] _ _.
Arguments B2FF [prec] [emax] _.

Definition FF2B' prec emax x : binary_float prec emax :=
  match sumb (valid_binary prec emax x) with
  | left prf => FF2B x prf
  | right _ => (* DUMMY *) B754_zero false
  end.

Arguments FF2B' [prec] [emax] _.

Lemma non_pl_inj (n : Z) (p1 p2 : nan_pl n) :
  proj1_sig p1 = proj1_sig p2 -> p1 = p2.
Proof.
intros H; destruct p1 as [r1 H1]; destruct p2 as [r2 H2].
simpl in H; revert H1; rewrite H; intros H1; f_equal.
now apply eqbool_irrelevance.
Qed.

Lemma FF2B'_B2FF : (@FF2B' prec emax) \o (@B2FF prec emax) =1 id.
Proof.
case=>//.
- simpl=> b [p Hp]; rewrite /FF2B'.
  case: sumb => prf.
  - congr B754_nan.
    exact: non_pl_inj.
  - rewrite /valid_binary in prf.
    by rewrite Hp in prf.
- move=> b m e Hme /=; rewrite /FF2B'.
  case: sumb => prf /=.
  - congr B754_finite; exact: eqbool_irrelevance.
  - rewrite /valid_binary in prf.
    by rewrite Hme in prf.
Qed.

(********************************************************************)
(** Test #1 (Function) & #2 (Fixpoint) using [binary_float 53 1024] *)
(********************************************************************)

Section seq_cholesky.

Fixpoint seq_stilde0 k c a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => seq_stilde0 k (fiplus c (fiopp (fimult a1 b1))) a2 b2
  end.

Definition seq_ytilded0 k c a b bk := fidiv (seq_stilde0 k c a b) bk.

Definition seq_ytildes0 k c a := fisqrt (seq_stilde0 k c a a).

Fixpoint seq_store0 T s n (v : T) :=
  match n, s with
    | _, [::] => [::]
    | O, _ :: t => v :: t
    | S n, h :: t => h :: seq_store0 t n v
  end.

Fixpoint store0 T m i j (v : T) :=
  match i, m with
    | _, [::] => [::]
    | O, h :: t => seq_store0 h j v :: t
    | S i, h :: t => h :: store0 t i j v
  end.

Definition m_id := [:: [:: one; FI0]; [:: FI0; one]].
Definition m_0 := [:: [:: FI0; FI0]; [:: FI0; FI0]].

(** Time Eval vm_compute in map (map B2F) (store m_id 0 1 half). *)

Require Import Recdef.

(* note: R is transposed with respect to cholesky.v *)
Section InnerLoop.
Variable j : nat.
Function inner_loop1 A R (i : nat)
         {measure (fun i => (j - i)%N) i} :=
  if (i < j)%N then
    let R := store0 R j i (seq_ytilded0 i (nth FI0 (nth [::] A i) j)
                                      (nth [::] R i) (nth [::] R j)
                                      (nth FI0 (nth [::] R i) i)) in
    inner_loop1 A R (i + 1)
  else
    R.
move=> _ _ i H; apply /ltP; rewrite addn1 subnSK //.
Defined.

Fixpoint inner_loop_rec2 (k : nat) A R (i : nat) {struct k} :=
  match k with
  | O (* i >= j) *) => R
  | S k => let R := store0 R j i (seq_ytilded0 i (nth FI0 (nth [::] A i) j)
                                             (nth [::] R i) (nth [::] R j)
                                             (nth FI0 (nth [::] R i) i)) in
           inner_loop_rec2 k A R (S i)
  end.
Definition inner_loop2 A R i := inner_loop_rec2 (j - i) A R i.
End InnerLoop.

Section OuterLoop.
Variable n : nat.
Function outer_loop1 A R (j : nat)
         {measure (fun i => (n - j)%N) j} :=
  if (j < n)%N then
    let R := inner_loop1 j A R 0 in
    let R := store0 R j j (seq_ytildes0 j (nth FI0 (nth [::] A j) j)
                                      (nth [::] R j)) in
    outer_loop1 A R (j + 1)
  else
    R.
move=> _ _ j H; apply /ltP; rewrite addn1 subnSK //.
Defined.

Fixpoint outer_loop_rec2 k A R (j : nat) {struct k} :=
  match k with
  | O (* j >= n *) => R
  | S k =>
    let R := inner_loop2 j A R 0 in
    let R := store0 R j j (seq_ytildes0 j (nth FI0 (nth [::] A j) j)
                                      (nth [::] R j)) in
    outer_loop_rec2 k A R (j + 1)
  end.
Definition outer_loop2 A R j := outer_loop_rec2 (n - j) A R j.
End OuterLoop.

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky1 A :=
  let sz := size A in
  outer_loop1 sz A A 0.
Definition cholesky2 A :=
  let sz := size A in
  outer_loop2 sz A A 0.

End seq_cholesky.

(** Time Eval vm_compute in map (map B2F) (cholesky1 m_id). *)

Definition m2 := [:: [:: Z2B 2; Z2B (-3); Z2B 1]; [:: Z2B (-3); Z2B 5; Z2B 0]; [:: Z2B 1; Z2B 0; Z2B 5]].

(** Time Eval vm_compute in map (map B2F) (cholesky1 m2). *)

(* returns approx:

[ sqrt 2,  -3,     1;
  -2.1213, 0.7071, 0;
  0.7071,  2.1213, 0 ]

then R is almost:

1 / sqrt 2 * [ 2, -3, 1;
               0,  1, 3;
               0,  0, 0 ]
*)

Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Module F := SpecificFloat BigIntRadix2.
Require Import BigZ.
(* Print Module F. *)
Local Open Scope bigZ_scope.

(* Time Eval vm_compute in map (map B2F) (cholesky2 (map64 m8')). (* ~13 s *) *)
(* Time Eval vm_compute in let res := map (map B2F) (cholesky2 (map64 m8')) in tt. (* ~12.7 s *) *)
(* (* [Time Eval vm_compute in let res := _ in tt] to skip pretty-printing time *) *)

(* Time Eval vm_compute in let res := map (map FF2F) (cholesky3 (mapFF m8')) in tt. (* ~12 s *) *)
(* Time Eval vm_compute in let res := cholesky3 (mapFF m8') in tt. (* ~11.8 s *) *)

Section test_CoqInterval_0.

Definition F2bigF (f : float radix2) :=
  Float (BigZ.of_Z (Fnum f)) (BigZ.of_Z (Fexp f)).

End test_CoqInterval_0.

(********************************************************************)
(** Test #3 using CoqEAL and operational Type Classes               *)
(********************************************************************)

Require Import mathcomp.algebra.matrix.
Require Import CoqEAL_refinements.seqmatrix.
Require Import CoqEAL_refinements.refinements.

Import Refinements.Op.

Class sqrt T := sqrt_op : T -> T.

Class store_class A I B :=
  store : forall (m n : nat), B m n -> I m -> I n -> A -> B m n.

Class dotmulB0_class A I B :=
  dotmulB0 : forall n : nat, I n -> A -> B 1%nat n -> B 1%nat n -> A.

Implicit Types n : nat.

Class I0_class I n := I0 : I n.
Class succ0_class I n := succ0 : I n -> I n.
(*
Example of instantiation for SSR matrices:

Definition succ0 (n : nat) (i : 'I_n.+1) : 'I_n.+1 :=
  match sumb ((val i).+1 < n.+1)%N with
  | left prf => Ordinal prf
  | right _ => ord0
  end.
*)
Class nat_of_class I n := nat_of : I n -> nat.

(*
Local Open Scope ring_scope.
Open Scope computable_scope.
Open Scope hetero_computable_scope.
*)

Section generic_algos.
Context {T : Type} {ordT : nat -> Type} {mxT : nat -> nat -> Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !mul T, !div T, !sqrt T}.
Context `{!fun_of T ordT mxT, !row_class ordT mxT, !store_class T ordT mxT, !dotmulB0_class T ordT mxT}.
Context {n : nat}.
Context `{!I0_class ordT n, !succ0_class ordT n, !nat_of_class ordT n}.

Local Open Scope nat_scope.

Definition ytilded3 (k : ordT n) c a b bk := (dotmulB0 k c a b / bk)%C.

Definition ytildes3 (k : ordT n) c a := (sqrt_op (dotmulB0 k c a a)).

(*
Definition m_id_v3 : seq (seq T) := [:: [:: 1%C; 0%C]; [:: 0%C; 1%C]].
Definition m_0_v3 := [:: [:: 0%C; 0%C]; [:: 0%C; 0%C]].
*)

(** Time Eval vm_compute in map (map B2F) (store m_id 0 1 half). *)

Hypothesis Hsucc0 : forall i : ordT n, (nat_of i).+1 < n -> nat_of (succ0 i) = (nat_of i).+1.

(* note: R is transposed with respect to cholesky.v *)
Section InnerLoop.
Variable j : ordT n.

Fixpoint inner_loop_rec3 (k : nat) A R (i : ordT n) {struct k} :=
  match k with
  | O (* i >= j *) => R
  | S k => let R := store R j i (ytilded3 i (fun_of_matrix A i j)
                                          (row i R) (row j R)
                                          (fun_of_matrix R i i)) in
           inner_loop_rec3 k A R (succ0 i)
  end.
Definition inner_loop3 A R i := inner_loop_rec3 (nat_of j - nat_of i) A R i.
End InnerLoop.

Section OuterLoop.
Fixpoint outer_loop_rec3 k A R (j : ordT n) {struct k} :=
  match k with
  | O (* j >= n *) => R
  | S k =>
    let R := inner_loop3 j A R I0 in
    let R := store R j j (ytildes3 j (fun_of_matrix A j j)
                                    (row j R)) in
    outer_loop_rec3 k A R (succ0 j)
  end.
Definition outer_loop3 A R j := outer_loop_rec3 (n - nat_of j) A R j.
End OuterLoop.

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky3 A := outer_loop3 A A I0.

End generic_algos.

Section inst_ssr_matrix.

Context {n : nat}.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !div T, !mul T, !sqrt T}.

Let ordT (n : nat) := 'I_n.
Let mxT (m n : nat) := 'M[T]_(m, n).

Instance ssr_fun_of : fun_of T ordT mxT := fun m n => @matrix.fun_of_matrix T m n.

Instance ssr_row : row_class ordT mxT := @matrix.row T.

Fixpoint gen_fsum_l2r_rec n (c : T) : T ^ n -> T :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => gen_fsum_l2r_rec (c + (a ord0))%C [ffun i => a (lift ord0 i)]
  end.

Definition gen_stilde3 n (c : T) (a b : T ^ n) : T :=
  gen_fsum_l2r_rec c [ffun i => (- ((a i) * (b i)))%C].

Definition gen_ytilded3 n (c : T) (a b : T ^ n) (bk : T) : T :=
  (gen_stilde3 c a b / bk)%C.

Definition gen_ytildes3 n (c : T) (a : T ^ n) : T :=
  sqrt_op (gen_stilde3 c a a).

Instance ssr_dotmulB0 : dotmulB0_class T ordT mxT :=
  fun n =>
    match n with
      | 0%N => fun i c a b => c
      | n'.+1 => fun i c a b => gen_stilde3 c
                                            [ffun k : 'I_i => a ord0 (inord k)]
                                            [ffun k : 'I_i => b ord0 (inord k)]
    end.

(* Erik: to rename ?
   Pierre : oui, n'hésite pas, mes noms sont assez pourris. *)
Definition ssr_store3 m n (M : 'M[T]_(m, n)) (i : 'I_m) (j : 'I_n) v :=
  \matrix_(i', j')
    if ((nat_of_ord i' == i) && (nat_of_ord j' == j))%N then v else M i' j'.

Instance : store_class T ordT mxT := ssr_store3.

Instance : I0_class ordT n.+1 := ord0.
Instance ssr_succ0 : succ0_class ordT n.+1 := fun i => inord i.+1.
Instance ssr_nat_of : nat_of_class ordT n.+1 := @nat_of_ord n.+1.

Definition ytilded5 : 'I_n.+1 -> T -> 'M[T]_(1, n.+1) -> 'M[T]_(1, n.+1) -> T ->
                      T :=
  @ytilded3 T ordT mxT _ _ _.

Definition ytildes5 : 'I_n.+1 -> T -> 'M[T]_(1, n.+1) -> T :=
  @ytildes3 T ordT mxT _ _ _.

Definition inner_loop5 : 'I_n.+1 -> 'M[T]_n.+1 -> 'M[T]_n.+1 -> 'I_n.+1 ->
  'M[T]_n.+1 :=
  @inner_loop3 T ordT mxT _ _ _ _ _ _ _ _.

Definition outer_loop5 : 'M[T]_n.+1 -> 'M[T]_n.+1 -> 'I_n.+1 ->
  'M[T]_n.+1 :=
  @outer_loop3 T ordT mxT _ _ _ _ _ _ _ _ _ _.

Definition cholesky5 : 'M[T]_n.+1 -> 'M[T]_n.+1 :=
  @cholesky3 T ordT mxT _ _ _ _ _ _ _ _ _ _.

End inst_ssr_matrix.

Section proof_inst_ssr_matrix.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !div T, !mul T, !sqrt T}.

Variable n : nat.

Lemma ssr_store3_eq (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  nat_of_ord i' = i -> nat_of_ord j' = j -> (ssr_store3 M i j v) i' j' = v.
Proof. by move=> Hi Hj; rewrite mxE Hi Hj !eq_refl. Qed.

Lemma ssr_store3_lt1 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (nat_of_ord i' < i)%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE (ltn_eqF Hi). Qed.

Lemma ssr_store3_lt2 (M : 'M[T]_n.+1) (i j : 'I_n.+1) v i' j' :
  (nat_of_ord j' < j)%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. by move=> Hj; rewrite mxE (ltn_eqF Hj) Bool.andb_false_r. Qed.

Lemma ssr_succ0_spec :
  forall (i : 'I_n.+1), (i.+1 < n.+1 -> ssr_succ0 i = i.+1 :> nat)%N.
Proof. by move=> i Hi; rewrite inordK. Qed.

Lemma gen_fsum_l2r_rec_eq k (c1 : T) (a1 : T ^ k)
      (c2 : T) (a2 : T ^ k) :
  c1 = c2 -> (forall i, a1 i = a2 i) ->
  gen_fsum_l2r_rec c1 a1 = gen_fsum_l2r_rec c2 a2.
Proof.
elim: k c1 a1 c2 a2 => [//|k IHk] c1 a1 c2 a2 Hc Ha.
by apply IHk; [rewrite /fplus Hc Ha|move=> i; rewrite !ffunE].
Qed.

Lemma gen_stilde3_eq k
      (c1 : T) (a1 b1 : T ^ k)
      (c2 : T) (a2 b2 : T ^ k) :
  c1 = c2 -> (forall i, a1 i = a2 i) ->
  (forall i, b1 i = b2 i) ->
  gen_stilde3 c1 a1 b1 = gen_stilde3 c2 a2 b2.
Proof.
move=> Hc Ha Hb.
rewrite /gen_stilde3; apply gen_fsum_l2r_rec_eq; [by []|move=> i].
by rewrite !ffunE; apply f_equal, f_equal2.
Qed.

Lemma gen_ytilded3_eq k
      (c1 : T) (a1 b1 : T ^ k) (bk1 : T)
      (c2 : T) (a2 b2 : T ^ k) (bk2 : T) :
  c1 = c2 -> (forall i, a1 i = a2 i) ->
  (forall i, b1 i = b2 i) -> (bk1 = bk2) ->
  gen_ytilded3 c1 a1 b1 bk1 = gen_ytilded3 c2 a2 b2 bk2.
Proof.
move=> Hc Ha Hb Hbk.
by rewrite /gen_ytilded3; apply f_equal2; [apply gen_stilde3_eq|].
Qed.

Lemma gen_ytildes3_eq k (c1 : T) (a1 : T ^ k) (c2 : T) (a2 : T ^ k) :
  c1 = c2 -> (forall i, a1 i = a2 i) ->
  gen_ytildes3 c1 a1 = gen_ytildes3 c2 a2.
Proof.
by move=> Hc Ha; rewrite /gen_ytildes3; apply f_equal, gen_stilde3_eq.
Qed.

Definition gen_cholesky_spec A R : Prop :=
  (forall (j i : 'I_n.+1),
     (i < j)%N ->
     (R i j = gen_ytilded3 (A i j)
                           [ffun k : 'I_i => R (inord k) i]
                           [ffun k : 'I_i => R (inord k) j]
                           (R i i)))
  /\ (forall (j : 'I_n.+1),
        (R j j = gen_ytildes3 (A j j)
                              [ffun k : 'I_j => R (inord k) j])).

(** *** Loop invariants. *)

Definition outer_loop_inv (A R : 'M[T]_n.+1) j : Prop :=
  (forall (j' i' : 'I_n.+1),
     (j' < j)%N ->
     (i' < j')%N ->
     (R j' i' = gen_ytilded3 (A i' j')
                  [ffun k : 'I_i' => R i' (inord k)]
                  [ffun k : 'I_i' => R j' (inord k)]
                  (R i' i')))
  /\ (forall (j' : 'I_n.+1),
        (j' < j)%N ->
        (R j' j' = gen_ytildes3 (A j' j') [ffun k : 'I_j' => R j' (inord k)])).

Definition inner_loop_inv (A R : 'M[T]_n.+1) j i : Prop :=
  outer_loop_inv A R j /\
  (forall (j' i' : 'I_n.+1),
        nat_of_ord j' = j ->
        (i' < i)%N ->
        (i' < j)%N ->
        (R j' i' = gen_ytilded3 (A i' j')
                     [ffun k : 'I_i' => R i' (inord k)]
                     [ffun k : 'I_i' => R j' (inord k)]
                     (R i' i'))).

Lemma inner_loop_correct (A Rt : 'M_n.+1) (j i : 'I_n.+1) :
  inner_loop_inv A Rt j i -> inner_loop_inv A (inner_loop5 j A Rt i) j n.+1.
Proof.
move=> H.
unfold inner_loop5, inner_loop3, nat_of, ssr_nat_of.
set (k := (j - i)%N).
have Hk : k = (j - i)%N; [by []|].
move: i k Hk Rt H => i k; move: i; induction k => i Hk Rt H; simpl.
{ split; [by apply H|]; move=> j' i' Hj' Hi' Hi'j.
  apply H => //; apply (leq_trans Hi'j).
  by rewrite -(addn0 i) -leq_subLR Hk. }
have Hij : (i < j)%N by rewrite -(addn0 i) -ltn_subRL -Hk.
have Hsisn : (i.+1 < n.+1)%N; [by move: (ltn_ord j); apply leq_ltn_trans|].
apply IHk => {IHk}; destruct H as (Ho, Hi).
{ apply /eqP; rewrite -(eqn_add2r 1) addn1 Hk.
  by rewrite ssr_succ0_spec // -(addn1 i) subnDA subnK // ltn_subRL addn0. }
split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
{ rewrite ssr_store3_lt1 // (proj1 Ho _ _ Hj' Hi').
  apply gen_ytilded3_eq => // [i''|i''|]; try rewrite !ffunE.
  { by rewrite ssr_store3_lt1 //; apply (ltn_trans Hi'). }
  { by rewrite ssr_store3_lt1. }
  by rewrite ssr_store3_lt1 //; apply (ltn_trans Hi'). }
{ rewrite ssr_store3_lt1 // (proj2 Ho _ Hj').
  by apply gen_ytildes3_eq => // i''; rewrite !ffunE ssr_store3_lt1. }
move=> j' i' Hj' Hi' Hi'j; case (ltnP i' i) => Hii'.
{ rewrite ssr_store3_lt2 // (Hi _ _ Hj' Hii' Hi'j).
  apply gen_ytilded3_eq => // [i''|i''|]; try rewrite !ffunE.
  { by rewrite ssr_store3_lt1. }
  { rewrite ssr_store3_lt2 //; apply ltn_trans with i'; [|by []].
    have Hi'' := ltn_ord i''.
    rewrite inordK //; apply (ltn_trans Hi''), ltn_ord. }
    by rewrite ssr_store3_lt2. }
have Hi'i : nat_of_ord i' = i.
{ apply anti_leq; rewrite Hii' Bool.andb_true_r -ltnS.
  by rewrite (ssr_succ0_spec Hsisn) in Hi'. }
rewrite ssr_store3_eq // Hi'i.
have Hini : inord i = i'; [by rewrite -Hi'i inord_val|].
have Hinj : inord j = j'; [by rewrite -Hj' inord_val|].
rewrite /ytilded3 /dotmulB0 /ssr_dotmulB0 /gen_ytilded3.
apply f_equal2; [apply gen_stilde3_eq => [|i''|i'']|]; try rewrite !ffunE.
{ by rewrite -Hini -Hinj !inord_val. }
{ by rewrite ssr_store3_lt1 // mxE -Hini inord_val. }
{ rewrite ssr_store3_lt2; [by rewrite mxE -Hinj inord_val|].
  have Hi'' := ltn_ord i''.
  rewrite inordK //; apply (ltn_trans Hi''); rewrite -Hi'i; apply ltn_ord. }
by rewrite ssr_store3_lt1 -Hini inord_val.
Qed.

Lemma outer_loop_correct (A Rt : 'M_n.+1) (j : 'I_n.+1) :
  outer_loop_inv A Rt j -> outer_loop_inv A (outer_loop5 A Rt j) n.+1.
Proof.
move=> H.
unfold outer_loop5, outer_loop3, nat_of, ssr_nat_of.
set (k := (n.+1 - j)%N).
have Hk : k = (n.+1 - j)%N; [by []|].
move: j k Hk Rt H => j k; move: j; induction k => j Hk Rt H; simpl.
{ by move: (ltn_ord j); rewrite -(addn0 j) -ltn_subRL Hk ltnn. }
have Hin_0 : inner_loop_inv A Rt j (@ord0 n); [by []|].
have Hin_n := inner_loop_correct Hin_0.
have Aux :
  outer_loop_inv A
    (ssr_store3 (inner_loop5 j A Rt ord0) j j
       (ytildes5 j (ssr_fun_of A j j) (ssr_row j (inner_loop5 j A Rt ord0))))
    j.+1.
{ split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
  { case (ltnP j' j) => Hjj'.
    { rewrite ssr_store3_lt1 // (proj1 (proj1 Hin_n) _ _ Hjj' Hi').
      apply gen_ytilded3_eq => // [i''|i''|]; try rewrite !ffunE.
      { by rewrite ssr_store3_lt1 //; apply (ltn_trans Hi'). }
      { by rewrite ssr_store3_lt1. }
      by rewrite ssr_store3_lt1 //; apply (ltn_trans Hi'). }
    have Hj'j : nat_of_ord j' = j.
    { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
    have Hi'j : (i' < j)%N; [by move: Hi'; rewrite Hj'j|].
    rewrite ssr_store3_lt2 // (proj2 Hin_n _ _ Hj'j (ltn_ord i') Hi'j).
    apply gen_ytilded3_eq => // [i''|i''|]; try rewrite !ffunE.
    { by rewrite ssr_store3_lt1. }
    { have Hi'' := ltn_ord i''.
      rewrite ssr_store3_lt2 //; move: Hi'j; apply ltn_trans; rewrite inordK //.
      apply ltn_trans with i'; apply ltn_ord. }
    by rewrite ssr_store3_lt2. }
  case (ltnP j' j) => Hjj'.
  { rewrite ssr_store3_lt2 // (proj2 (proj1 Hin_n) _ Hjj').
    apply gen_ytildes3_eq => // j''; try rewrite !ffunE.
    by rewrite ssr_store3_lt1. }
  have Hj'j : nat_of_ord j' = j.
  { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS. }
  have Hinjj' : inord j = j'; [by rewrite -Hj'j inord_val|].
  rewrite ssr_store3_eq //.
  rewrite /ytildes5 /ytildes3 /dotmulB0 /ssr_dotmulB0 /gen_ytildes3 Hj'j.
  apply /f_equal /gen_stilde3_eq => [|j''|j'']; try rewrite !ffunE.
  { by apply f_equal2; apply ord_inj. }
  { rewrite ssr_store3_lt2; [by rewrite mxE -Hinjj' inord_val|].
    have Hj'' := ltn_ord j''.
    rewrite inordK //; apply (ltn_trans Hj''); rewrite -Hj'j; apply ltn_ord. }
  rewrite ssr_store3_lt2; [by rewrite mxE -Hinjj' inord_val|].
  have Hj'' := ltn_ord j''.
  rewrite inordK //; apply (ltn_trans Hj''); rewrite -Hj'j; apply ltn_ord. }
case (ltnP j n) => Hjn.
{ have Hsjsn : (j.+1 < n.+1)%N by rewrite -(ltn_add2r 1) !addn1.
  apply IHk => {IHk}.
  { apply /eqP; rewrite -(eqn_add2r 1) addn1 Hk.
      by rewrite ssr_succ0_spec // -(addn1 j) subnDA subnK // ltn_subRL addn0. }
  rewrite (ssr_succ0_spec Hsjsn); apply Aux. }
have Hj : (j = n :> nat).
{ apply anti_leq; rewrite Hjn Bool.andb_true_r -ltnS; apply ltn_ord. }
have Hk0 : k = 0%N.
{ move: Hk; rewrite Hj subSnn -(add0n 1%N) -addn1 => Hk.
  by apply /eqP; rewrite -(eqn_add2r 1%N); apply /eqP. }
by rewrite Hk0 /=; move: Aux; rewrite Hj.
Qed.

(** *** The implementation satisfies the specification used in cholesky.v. *)

Lemma cholesky5_correct (A : 'M[T]_n.+1) : gen_cholesky_spec A (cholesky5 A)^T.
Proof.
split; [move=> j i Hij|move=> j]; rewrite !mxE.
{ replace ((cholesky5 A) j i)
  with (gen_ytilded3 (A i j)
                     [ffun k : 'I_i => (cholesky5 A) i (inord k)]
                     [ffun k : 'I_i => (cholesky5 A) j (inord k)]
                     ((cholesky5 A) i i)).
  { by apply /gen_ytilded3_eq => [|i'|i'|]; try rewrite !ffunE mxE. }
  by apply sym_eq, outer_loop_correct; [|apply ltn_ord|]. }
replace ((cholesky5 A) j j)
with (gen_ytildes3 (A j j)
                   [ffun k : 'I_j => (cholesky5 A) j (inord k)]).
{ by apply /gen_ytildes3_eq => // j'; rewrite !ffunE mxE. }
by apply sym_eq, outer_loop_correct; [|apply ltn_ord].
Qed.

End proof_inst_ssr_matrix.

Section proof_inst_ssr_matrix_float_infnan.

Require Import float_infnan_spec cholesky_infnan.

Variable fs : Float_infnan_spec.

Instance add_infnan : add (FI fs) := @fiplus fs.
Instance mul_infnan : mul (FI fs) := @fimult fs.
Instance sqrt_infnan : sqrt (FI fs) := @fisqrt fs.
Instance div_infnan : div (FI fs) := @fidiv fs.
Instance opp_infnan : opp (FI fs) := @fiopp fs.
Instance zero_infnan : zero (FI fs) := @FI0 fs.
Instance one_infnan : one (FI fs) := firnd fs 1.

Lemma gen_stilde3_correct k (c : FI fs) (a b : FI fs ^ k) :
  gen_stilde3 c a b = stilde_infnan c a b.
Proof.
elim: k c a b => [|k IHk] c a b; [by rewrite /gen_stilde3|].
rewrite /gen_stilde3 /= -IHk.
by apply gen_fsum_l2r_rec_eq; [|move=> i]; rewrite !ffunE.
Qed.

Lemma gen_ytilded3_correct k (c : FI fs) (a b : FI fs ^ k) (bk : FI fs) :
  gen_ytilded3 c a b bk = ytilded_infnan c a b bk.
Proof.
rewrite /gen_ytilded3 /ytilded_infnan; apply f_equal2 => //.
apply gen_stilde3_correct.
Qed.

Lemma gen_ytildes3_correct k (c : FI fs) (a : FI fs ^ k) :
  gen_ytildes3 c a = ytildes_infnan c a.
Proof.
rewrite /gen_ytildes3 /ytildes_infnan; apply f_equal => //.
apply gen_stilde3_correct.
Qed.

Lemma gen_cholesky_spec_correct n (A R : 'M[FI fs]_n.+1) :
  gen_cholesky_spec A R -> cholesky_spec_infnan A R.
Proof.
move=> H; split.
{ by move=> j i Hij; rewrite (proj1 H) // gen_ytilded3_correct. }
by move=> j; rewrite (proj2 H) // gen_ytildes3_correct.
Qed.

(** If [A] contains no infinity or NaN, then [MFI2F A] = [A] and
    [posdef (MF2R (MFI2F A))] means that [A] is positive definite. *)
Lemma gen_corollary_2_4_with_c_upper_bound_infnan :
  forall n,
  4 * INR n.+2 * eps (fis fs) < 1 ->  (* need a small program to check *)
  forall A : 'M[FI fs]_n.+1,
  A^T = A ->  (* need a small program to check *)
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->  (* need a small program to check *)
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->  (* need a small program to compute *)
  forall c : R,
  (/2 * gamma (fis fs) (2 * n.+2) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->  (* need a small program to comute (with directed rounding) *)
  forall At : 'M[FI fs]_n.+1, At^T = At ->
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, (MFI2F At) i i <= (MFI2F A) i i - c)) ->  (* need a small program to compute (with directed rounding) *)
  let Rt := cholesky5 At in
  (forall i, (0 < FI2F (Rt i i))%Re) ->  (* need a small program to check *)
  real_matrix.posdef (cholesky.MF2R (MFI2F A)).
Proof.
move=> n H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At SymAt HAt Rt HARt.
apply corollary_2_4_with_c_upper_bound_infnan with maxdiag c At Rt^T;
  try assumption; split; [|by move=> i; rewrite mxE].
apply gen_cholesky_spec_correct, cholesky5_correct.
Qed.

End proof_inst_ssr_matrix_float_infnan.

Section inst_seq.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !div T, !mul T, !sqrt T}.

Let ordT (n : nat) := nat.
Let mxT (m n : nat) := seq (seq T).

Instance : fun_of T ordT mxT := fun m n => fun_of_seqmx m n.

Instance : row_class ordT mxT := @rowseqmx T.

(* seq_stilde3 *)
Fixpoint seq_stilde3 k c a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => seq_stilde3 k (c + (- (a1 * b1)))%C a2 b2
  end.

Instance : dotmulB0_class T ordT mxT :=
  fun n k c a b => seq_stilde3 k c (head [::] a) (head [::] b).

Fixpoint seq_store3 T s n (v : T) :=
  match n, s with
    | _, [::] => [::]
    | O, _ :: t => v :: t
    | S n, h :: t => h :: seq_store3 t n v
  end.

Fixpoint store3 T m i j (v : T) :=
  match i, m with
    | _, [::] => [::]
    | O, h :: t => seq_store3 h j v :: t
    | S i, h :: t => h :: store3 t i j v
  end.

Instance : store_class T ordT mxT :=
  fun m n M i j v =>
  store3 M i j v.

Variable M : seq (seq T).
Let n := seq.size M.
Instance : I0_class ordT n := O.
Instance : succ0_class ordT n := S.
Instance : nat_of_class ordT n := id.

Definition cholesky4 : seq (seq T) :=
  @cholesky3 T ordT mxT _ _ _ _ _ _ n O S id M.

End inst_seq.

Section data_refinement.
(* Aim: refinement proofs using seqmatrix.v *)

Require Import CoqEAL_theory.hrel.

(* Abstract types *)
Context {A : Type}.
Local Notation ordA := ordinal.
Local Notation mxA := (fun m n => 'M[A]_(m, n)).
Context `{!zero A, !one A, !add A, !opp A, (* !sub A, *) !mul A, !div A, !sqrt A}.

(* Concrete types *)
Context {C : Type}.
Local Notation ordC := (fun _ : nat => nat).
Local Notation mxC := (fun _ _ : nat => seq (seq C)).
Context `{!zero C, !one C, !add C, !opp C, (* !sub C, *) !mul C, !div C, !sqrt C}.
Context `{!fun_of C ordC mxC, !row_class ordC mxC, !store_class C ordC mxC, !dotmulB0_class C ordC mxC}.
Context {n : nat}.
Context `{!I0_class ordC n, !succ0_class ordC n, !nat_of_class ordC n}.

Context {RC : A -> C -> Prop}.

Context {RmxC : forall {m n}, mxA m n -> mxC m n -> Prop}.
Arguments RmxC {m n} _ _. (* maximal implicit arguments *)

Context {RordC : forall m, 'I_m -> ordC m -> Prop}.
Arguments RordC {m} _ _.

Context `{forall m n, param (RmxC ==> RordC ==> RordC ==> RC)
  (@matrix.fun_of_matrix A m n) (@fun_of_matrix _ _ _ _ m n)}.

Context `{forall m n, param (RordC ==> RmxC ==> RmxC)
  (@matrix.row A m n) (@row _ _ _ m n)}.

Context `{forall m n, param (RmxC ==> RordC ==> RordC ==> RC ==> RmxC)
  (@ssr_store3 A m n) (@store _ _ _ _ m n)}.

Context `{forall n, param (RordC ==> RC ==> RmxC ==> RmxC ==> RC)
  (@ssr_dotmulB0 A _ _ _ n) (@dotmulB0 _ _ _ _ n)}.

Global Instance param_cholesky n :
  param (RmxC ==> RmxC)%rel (cholesky5 (n := n)) cholesky4.
Proof.
eapply param_abstr => m s param_ms; rewrite /cholesky5 /cholesky4.
rewrite /cholesky3 /outer_loop3.
Admitted.
(*
Ingredients:
exact: get_param.
eapply param_abstr=> a c param_ac.
rewrite paramE.
eapply param_apply.
by tc.
*)

End data_refinement.

(* ================================================================ *)
(* Require Import String. Eval compute in "Début des tests."%string. *)
(* Goal True. idtac "Début des tests". done. Qed. *)
(* ================================================================ *)

(* Load "testsuite". *)
Require Import testsuite.

Section test_CoqInterval.

Local Notation T := (s_float BigZ.t_ BigZ.t_).

Instance add'' : add T := F.add rnd_NE 53%bigZ.
Instance mul'' : mul T := F.mul rnd_NE 53%bigZ.
Instance sqrt'' : sqrt T := F.sqrt rnd_NE 53%bigZ.
Instance div'' : div T := F.div rnd_NE 53%bigZ.
Instance opp'' : opp T := F.neg.
Instance zero'' : zero T := F.zero.
Instance one'' : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.
(* 6.7 s on Erik's laptop *)

End test_CoqInterval.

Section test_CoqInterval_add.

Local Notation T := F.type.

Instance : add T := fun a b =>
  let r1 := F.add rnd_NE 53%bigZ a b in
  let r2 := F.add rnd_NE 53%bigZ a b in
  r2.
Instance : mul T := F.mul rnd_NE 53%bigZ.
Instance : sqrt T := F.sqrt rnd_NE 53%bigZ.
Instance : div T := F.div rnd_NE 53%bigZ.
Instance : opp T := F.neg.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_add". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_add.

Section test_CoqInterval_mul.

Local Notation T := F.type.

Instance : mul T := fun a b =>
  let r1 := F.mul rnd_NE 53%bigZ a b in
  let r2 := F.mul rnd_NE 53%bigZ a b in
  r2.
Instance : add T := F.add rnd_NE 53%bigZ.
Instance : sqrt T := F.sqrt rnd_NE 53%bigZ.
Instance : div T := F.div rnd_NE 53%bigZ.
Instance : opp T := F.neg.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_mul". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_mul.

Section test_CoqInterval_div.

Local Notation T := F.type.

Instance : add T := F.add rnd_NE 53%bigZ.
Instance : mul T := F.mul rnd_NE 53%bigZ.
Instance : sqrt T := F.sqrt rnd_NE 53%bigZ.
Instance : div T := fun a b =>
  let r1 := F.div rnd_NE 53%bigZ a b in
  let r2 := F.div rnd_NE 53%bigZ a b in
  r2.
Instance : opp T := F.neg.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_div". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_div.

Section test_CoqInterval_sqrt.

Local Notation T := F.type.

Instance : add T := F.add rnd_NE 53%bigZ.
Instance : mul T := F.mul rnd_NE 53%bigZ.
Instance : sqrt T := fun a =>
  let r1 := F.sqrt rnd_NE 53%bigZ a in
  let r2 := F.sqrt rnd_NE 53%bigZ a in
  r2.
Instance : div T := F.div rnd_NE 53%bigZ.
Instance : opp T := F.neg.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_sqrt". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_sqrt.

Section test_CoqInterval_opp.

Local Notation T := F.type.

Instance : add T := F.add rnd_NE 53%bigZ.
Instance : mul T := F.mul rnd_NE 53%bigZ.
Instance : opp T := fun a =>
  let r1 := F.neg a in
  let r2 := F.neg a in
  r2.
Instance : div T := F.div rnd_NE 53%bigZ.
Instance : sqrt T := F.sqrt rnd_NE 53%bigZ.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_opp". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_opp.

Section test_CoqInterval_all.

Local Notation T := F.type.

Instance : add T := fun a b =>
  let r1 := F.add rnd_NE 53%bigZ a b in
  let r2 := F.add rnd_NE 53%bigZ a b in
  r2.
Instance : mul T := fun a b =>
  let r1 := F.mul rnd_NE 53%bigZ a b in
  let r2 := F.mul rnd_NE 53%bigZ a b in
  r2.
Instance : opp T := fun a =>
  let r1 := F.neg a in
  let r2 := F.neg a in
  r2.
Instance : div T := fun a b =>
  let r1 := F.div rnd_NE 53%bigZ a b in
  let r2 := F.div rnd_NE 53%bigZ a b in
  r2.
Instance : sqrt T := fun a =>
  let r1 := F.sqrt rnd_NE 53%bigZ a in
  let r2 := F.sqrt rnd_NE 53%bigZ a in
  r2.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_all". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_all.

Section test_CoqInterval_none.

Local Notation T := F.type.

Instance : add T := fun a b =>
  a.
Instance : mul T := fun a b =>
  a.
Instance : opp T := fun a =>
  a.
Instance : div T := fun a b =>
  a.
Instance : sqrt T := fun a =>
  a.
Instance : zero T := F.zero.
Instance : one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_none". done. Qed.
Time Eval vm_compute in let res := cholesky4 m12 in tt.

End test_CoqInterval_none.
