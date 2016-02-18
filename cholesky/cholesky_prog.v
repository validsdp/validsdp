(** * Application: program for Cholesky decomposition. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg matrix bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum fcmdotprod real_matrix cholesky.

Require Import Recdef.

Section Cholesky_prog.

Variable fs : Float_spec.

(** [store M i j v] returns the matrix [M] with all fields untouched
    except the field at row [i], column [j] which is replaced by [v]. *)
Definition store n (M : 'M_n) (i j : nat) (v : F fs) :=
  \matrix_(i', j')
    if ((nat_of_ord i' == i) && (nat_of_ord j' == j))%N then v else M i' j'.

Lemma store_eq n (M : 'M_n) i j v i' j' :
  nat_of_ord i' = i -> nat_of_ord j' = j -> (store M i j v) i' j' = v.
Proof. by move=> Hi Hj; rewrite mxE Hi Hj !eq_refl. Qed.

Lemma store_lt1 n (M : 'M_n) i j v i' j' :
  (nat_of_ord i' < i)%N -> (store M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE (ltn_eqF Hi). Qed.

Lemma store_lt2 n (M : 'M_n) i j v i' j' :
  (nat_of_ord j' < j)%N -> (store M i j v) i' j' = M i' j'.
Proof. by move=> Hj; rewrite mxE (ltn_eqF Hj) Bool.andb_false_r. Qed.

(** ** An implementation of Cholesky decomposition. *)
Section Prog.

Variable n : nat.

Variable A : 'M[F fs]_n.+1.

Section InnerLoop.
Variable j : nat.
Definition RT := 'M[F fs]_n.+1.  (** Otherwise Function won't generate
                                     induction schemes *)
Function inner_loop (R : RT) (i : nat)
         {measure (fun i => (j - i)%N) i} :=
  if (i < j)%N then
    let R := store R i j (ytilded (A (inord i) (inord j))
                            [ffun k : 'I_i => R (inord k) (inord i)]
                            [ffun k : 'I_i => R (inord k) (inord j)]
                            (R (inord i) (inord i))) in
    inner_loop R (i + 1)
  else
    R.
move=> _ i H; apply /ltP; rewrite addn1 subnSK //.
Defined.
End InnerLoop.

Section OuterLoop.
Function outer_loop (R : RT) (j : nat)
         {measure (fun i => (n.+1 - j)%N) j} :=
  if (j < n.+1)%N then
    let R := inner_loop j R 0 in
    let R := store R j j (ytildes (A (inord j) (inord j))
                            [ffun k : 'I_j => R (inord k) (inord j)]) in
    outer_loop R (j + 1)
  else
    R.
move=> _ j H; apply /ltP; rewrite addn1 subnSK //.
Defined.
End OuterLoop.

Definition cholesky :=
  let R := const_mx (F0 fs) in
  outer_loop R 0.

End Prog.

(** *** Loop invariants. *)

Definition outer_loop_inv n (A Rt : 'M[F fs]_n.+1) j : Prop :=
  (forall (j' i' : 'I_n.+1),
     (j' < j)%N ->
     (i' < j')%N ->
     (Rt i' j' = ytilded (A i' j')
                   [ffun k : 'I_i' => Rt (inord k) i']
                   [ffun k : 'I_i' => Rt (inord k) j']
                   (Rt i' i') :> R))
  /\ (forall (j' : 'I_n.+1),
        (j' < j)%N ->
        (Rt j' j' = ytildes (A j' j') [ffun k : 'I_j' => Rt (inord k) j'] :> R)).

Definition inner_loop_inv n (A Rt : 'M[F fs]_n.+1) j i : Prop :=
  outer_loop_inv A Rt j /\
  (forall (j' i' : 'I_n.+1),
        nat_of_ord j' = j ->
        (i' < i)%N ->
        (i' < j)%N ->
        (Rt i' j' = ytilded (A i' j')
                     [ffun k : 'I_i' => Rt (inord k) i']
                     [ffun k : 'I_i' => Rt (inord k) j']
                     (Rt i' i') :> R)).

Lemma inner_loop_correct n (A Rt : 'M_n.+1) j i :
  inner_loop_inv A Rt j i -> inner_loop_inv A (inner_loop A j Rt i) j n.+1.
Proof.
move=> H.
functional induction (inner_loop A j Rt i).
{ apply IHr => {IHr}; destruct H as (Ho, Hi).
  split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
  { rewrite store_lt2 // (proj1 Ho _ _ Hj' Hi').
    apply ytilded_eq => // [i''|i''|]; try rewrite !ffunE.
    { by rewrite store_lt2 //; apply (ltn_trans Hi'). }
    { by rewrite store_lt2. }
    by rewrite store_lt2 //; apply (ltn_trans Hi'). }
  { rewrite store_lt2 // (proj2 Ho _ Hj').
    by apply ytildes_eq => // i''; rewrite !ffunE store_lt2. }
  move=> j' i' Hj' Hi' Hi'j; case (ltnP i' i) => Hii'.
  { rewrite store_lt1 // (Hi _ _ Hj' Hii' Hi'j).
    apply ytilded_eq => // [i''|i''|]; try rewrite !ffunE.
    { by rewrite store_lt2. }
    { rewrite store_lt1 //; apply ltn_trans with i'; [|by []].
      have Hi'' := ltn_ord i''.
      rewrite inordK //; apply (ltn_trans Hi''), ltn_ord. }
    by rewrite store_lt1. }
  have Hi'i : nat_of_ord i' = i.
  { by apply anti_leq; rewrite Hii' Bool.andb_true_r -ltnS -(addn1 i). }
  rewrite store_eq // Hi'i.
  have Hini : inord i = i'; [by rewrite -Hi'i inord_val|].
  have Hinj : inord j = j'; [by rewrite -Hj' inord_val|].
  apply ytilded_eq => [|i''|i''|]; try rewrite !ffunE.
  { by apply f_equal, f_equal2. }
  { by rewrite store_lt2 // Hini. }
  { rewrite Hinj store_lt1 //.
    have Hi'' := ltn_ord i''.
    rewrite inordK //; apply (ltn_trans Hi''); rewrite -Hi'i; apply ltn_ord. }
  by rewrite Hini store_lt2. }
case (ltnP i j) => Hij.
{ by casetype False; move: y; rewrite Hij. }
split; [by apply H|]; move=> j' i' Hj' Hi' Hi'j.
by apply H => //; apply (leq_trans Hi'j).
Qed.

Lemma outer_loop_correct n (A Rt : 'M_n.+1) j :
  outer_loop_inv A Rt j -> outer_loop_inv A (outer_loop A Rt j) n.+1.
Proof.
move=> H.
functional induction (outer_loop A Rt j).
{ apply IHr => {IHr}.
  have Hin_0 : inner_loop_inv A R j 0; [by []|].
  have Hin_n := inner_loop_correct Hin_0.
  split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
  { case (ltnP j' j) => Hjj'.
    { rewrite store_lt2 // (proj1 (proj1 Hin_n) _ _ Hjj' Hi').
      apply ytilded_eq => // [i''|i''|]; try rewrite !ffunE.
      { by rewrite store_lt2 //; apply (ltn_trans Hi'). }
      { by rewrite store_lt2. }
      by rewrite store_lt2 //; apply (ltn_trans Hi'). }
    have Hj'j : nat_of_ord j' = j.
    { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS -(addn1 j). }
    have Hi'j : (i' < j)%N; [by move: Hi'; rewrite Hj'j|].
    rewrite store_lt1 // (proj2 Hin_n _ _ Hj'j (ltn_ord i') Hi'j).
    apply ytilded_eq => // [i''|i''|]; try rewrite !ffunE.
    { by rewrite store_lt2. }
    { have Hi'' := ltn_ord i''.
      rewrite store_lt1 //; move: Hi'j; apply ltn_trans; rewrite inordK //.
      apply ltn_trans with i'; apply ltn_ord. }
    by rewrite store_lt1. }
  case (ltnP j' j) => Hjj'.
  { rewrite store_lt1 // (proj2 (proj1 Hin_n) _ Hjj').
    apply ytildes_eq => // j''; try rewrite !ffunE.
    by rewrite store_lt2. }
  have Hj'j : nat_of_ord j' = j.
  { by apply anti_leq; rewrite Hjj' Bool.andb_true_r -ltnS -(addn1 j). }
  have Hinjj' : inord j = j'; [by rewrite -Hj'j inord_val|].
  rewrite store_eq // Hj'j Hinjj'; apply ytildes_eq => // j''.
  rewrite !ffunE store_lt1 //; move: (ltn_ord j''); apply leq_ltn_trans.
  apply eq_leq; rewrite inordK //; apply (ltn_trans (ltn_ord j'')).
  rewrite -Hj'j; apply ltn_ord. }
case (ltnP j n.+1) => Hjn.
{ by casetype False; move: y; rewrite Hjn. }
split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
{ have Hj'j : (j' < j)%N; [by apply leq_ltn_trans with n|].
  by apply H. }
have Hj'j : (j' < j)%N; [by apply leq_ltn_trans with n|].
by apply H.
Qed.

(** *** The implementation satisfies the specification used elsewhere. *)

Lemma cholesky_correct n (A : 'M[F fs]_n.+1) : cholesky_spec A (cholesky A).
Proof. by split; [move=> j i Hij|move=> j]; apply outer_loop_correct. Qed.

End Cholesky_prog.
