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

Context `{!heq mxT}.
Context `{!transpose_class mxT}.

Definition is_sym (A : mxT n n) : bool := (A^T == A)%HC.
(* TODO : en fait, ce dont on a besoin, c'est de prouver 
   MF2R (MFI2F A^T) = MF2R (MFI2F A) *)

Fixpoint all_diag_rec f k (A : mxT n n) b (i : ordT n) {struct k} : bool :=
  match k with
  | O => b
  | S k => all_diag_rec f k A (b && f (fun_of_matrix A i i)) (succ0 i)
  end.
Definition all_diag f A := all_diag_rec f n A true I0.

Context `{!leq T}.

Definition noneg_diag := all_diag (fun x => 0 <= x)%C.

Context `{!lt T}.

Definition pos_diag := all_diag (fun x => 0 < x)%C.

Fixpoint foldl_diag_rec (T' : Type) f z k (A : mxT n n) (i : ordT n)
{struct k} : T' :=
  match k with
  | O => z
  | S k => foldl_diag_rec T' f (f z (fun_of_matrix A i i)) k A (succ0 i)
  end.
Definition foldl_diag T' f (z : T') A := foldl_diag_rec f z n A I0.

Definition max_diag A :=
  foldl_diag (fun m c => if (m <= c)%C then c else m) 0%C A.

Fixpoint map_diag_rec f k (A R : mxT n n) (i : ordT n) {struct k} : mxT n n :=
  match k with
  | O => R
  | S k =>
    let R := store R i i (f (fun_of_matrix A i i)) in
    map_diag_rec f k A R (succ0 i)
  end.
Definition map_diag f A := map_diag_rec f n A A I0.

Section directed_rounding.

(* upward rounded operations *)
Context `{!add T, !mul T, !div T}.  (* @Érik: on pourrait pas les nommer ? *)
Context `{!one T}.

Definition tr_up A := foldl_diag add1 0%C A.

(* get a float overapprox of n *)
Definition float_of_nat_up n := iter _ n (fun x => add1 x one1) 0%C.

(* [compute_c n A maxdiag] overapproximates
   /2 gamma (2 (n + 1)) \tr A + 4 eta n * (2 (n + 1) + maxdiag) *)
Definition compute_c_aux (eps eta : T)  (* overapproximations of eps and eta *)
  (A : mxT n n) (maxdiag : T) : T :=
let np1 := float_of_nat_up n.+1 in
let dnp1 := float_of_nat_up (2 * n.+1)%N in
let tnp1 := mul1 dnp1 eps in
let g := div1 (mul1 np1 eps) (- (add1 tnp1 (-1%C)))%C in
add1
  (mul1 g (tr_up A))
  (mul1
    (mul1 (mul1 (float_of_nat_up 4) eta) (float_of_nat_up n))
    (add1 dnp1 maxdiag)).

Definition compute_c (is_finite : T -> bool) (eps eta : T) (A : mxT n n) :
  option T :=
  let nem1 := add1 (mul1 ((float_of_nat_up (2 * n.+1)%N)) eps) (-1%C)%C in
  if is_finite nem1 && (nem1 < 0)%C then
    let c := compute_c_aux eps eta A (max_diag A) in
    if is_finite c then Some c else None
  else None.

(* subtraction rounded downward *)
Definition sub_down x y := (- (add1 y (- x)%C))%C.

End directed_rounding.

Definition posdef_check
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)         
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mxT n n) : bool :=
test_n n && is_sym A && all_diag is_finite A && noneg_diag A &&
  (match compute_c is_finite eps eta A with
     | None => false
     | Some c =>
       let A' := map_diag (fun x => sub_down x c) A in
       let R := cholesky3 A' in
       all_diag is_finite R && pos_diag R
   end).

End generic_algos.

Section succ0_theory.
Variables (ordT : nat -> Type) (n : nat).
Context `{!succ0_class ordT n, !nat_of_class ordT n}.
Class succ0_correct :=
  succ0_prop :
  forall i : ordT n, ((nat_of i).+1 < n)%N -> nat_of (succ0 i) = (nat_of i).+1.
End succ0_theory.
Arguments succ0_correct _ _ {succ0_class0} {nat_of_class0}.

Section I0_theory.
Variables (ordT : nat -> Type) (n : nat).
Context `{!I0_class ordT n, !nat_of_class ordT n}.
Class I0_correct := I0_prop : nat_of I0 = 0%N.
End I0_theory.
Arguments I0_correct _ _ {I0_class0} {nat_of_class0}.

Section nat_of_theory.
Variables (ordT : nat -> Type) (n : nat).
Context `{!nat_of_class ordT n}.
Class nat_of_correct := nat_of_prop :
  forall i j : ordT n, nat_of i = nat_of j -> i = j.
End nat_of_theory.
Arguments nat_of_correct _ _ {nat_of_class0}.

Section generic_ind.
Context {ordT : nat -> Type} {n' : nat}.
Let n := n'.+1.
Context `{!I0_class ordT n, !succ0_class ordT n, !nat_of_class ordT n}.
Context `{!I0_correct ordT n, !succ0_correct ordT n, !nat_of_correct ordT n}.

Lemma trec_ind M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) :
  forall j, (j <= n)%N ->
  (forall i s, G 0%N i s = s) ->
  (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) ->
  (forall (i : ordT n) s,
    (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall (i : ordT n) s,
    (nat_of i <= j)%N -> P (nat_of i) s -> P j (G (j - nat_of i)%N i s).
Proof.
move=> j Hj HG0 HGS Hind i s Hi H.
set (k := (j - nat_of i)%N).
have Hk : k = (j - nat_of i)%N; [by []|].
move: i Hi k Hk s H => i Hi k; move: i Hi; induction k => i Hi Hk s H.
{ rewrite HG0; replace j with (nat_of i); [by []|].
  by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. }
case (ltnP (nat_of i) j); [move=> Hij|by rewrite /ssrnat.leq -Hk].
rewrite HGS; case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
    apply IHk; erewrite (succ0_prop Hsisn) =>//.
    by rewrite subnS -Hk.
    by apply Hind; [apply leqW|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi' : nat_of i = n'.
{ apply anti_leq; rewrite Hjn Bool.andb_true_r.
    by apply (@leq_trans j.-1); [apply /leP /Nat.lt_le_pred /leP|rewrite Hj']. }
have Hk' : k = 0%N.
{ move: Hk; rewrite Hi' Hj' subSnn; apply eq_add_S. }
  by rewrite Hk' HG0 Hj' /n -Hi'; apply Hind; [rewrite Hi'|].
Qed.

(* above lemma for P j s := forall i, nat_of i < j -> P i s *)
Lemma trec_ind' M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) :
  (forall i s, G 0%N i s = s) ->
  (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) ->
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ordT n), (nat_of j < (nat_of i).+1)%N -> P j (f i s)) ->
  forall (i : ordT n) s, (nat_of i < n)%N -> P i (G n I0 s).
Proof.
move=> HG0 HGS Hind i s Hi.
set P' := fun j s => forall (i : ordT n), (nat_of i < j)%N -> P i s.
suff: P' n (G n I0_class0 s); [by move=> H; eapply H, Hi|].
have P0 : P' O s; [by []|move: (leq0n n) P0].
replace (G _ _ _) with (G (n - nat_of I0)%N I0 s); [|by rewrite I0_prop].
replace O with (nat_of I0); move=> HI0 HP0.
by apply (@trec_ind _ P' _ f).
Qed.

Lemma trec_ind'_case M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) :
  (forall i s, G 0%N i s = s) ->
  (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) ->
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ordT n), (nat_of j < nat_of i)%N -> P j (f i s)) ->
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) -> P i (f i s)) ->
  forall (i : ordT n) s, (nat_of i < n)%N -> P i (G n I0 s).
Proof.
move=> HG0 HGS H1 H2; apply trec_ind' with (f := f) => // i s Hi H j Hj.
case (ltnP (nat_of j) (nat_of i)) => Hji.
{ by apply H1. }
have H' : j = i.
{ apply (@nat_of_prop _ _ nat_of_class0) => //; apply anti_leq.
  rewrite Hji Bool.andb_true_r; apply Hj. }
rewrite -H'; apply H2; rewrite H' //.
Qed.

Context {ordT' : nat -> Type}.
Context `{!I0_class ordT' n, !succ0_class ordT' n, !nat_of_class ordT' n}.
Context `{!succ0_correct ordT' n}.

Lemma trec_ind2 M M' P (G : nat -> ordT n -> M -> M)
  (G' : nat -> ordT' n -> M' -> M')
  (f : ordT n -> M -> M)
  (f' : ordT' n -> M' -> M') :
  forall j, (j <= n)%N ->
  (forall i s, G 0%N i s = s) ->
  (forall i s, G' 0%N i s = s) ->
  (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) ->
  (forall k i s, G' k.+1 i s = G' k (succ0 i) (f' i s)) ->
  (forall (i : ordT n) (i' : ordT' n) s s',
    (nat_of i <= n)%N ->
    nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall (i : ordT n) (i' : ordT' n) s s',
    (nat_of i <= j)%N ->
    nat_of i' = nat_of i ->
    P s s' ->
    P (G (j - nat_of i)%N i s) (G' (j - nat_of i')%N i' s').
Proof.
move=> j Hj HG0 HG'0 HGS HG'S Hind i i' s s' Hi Hi' H.
rewrite Hi'.
move Hk: (j - nat_of i)%N => k.
elim: k i i' Hi Hi' Hk s s' H => [|k IHk] i i' Hi Hi' Hk s s' H.
{ rewrite HG0 HG'0; replace j with (nat_of i); [by []|].
  by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. }
case (ltnP (nat_of i) j); last by rewrite /ssrnat.leq Hk.
move=> Hij.
rewrite HGS HG'S; case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
    apply: IHk; first by rewrite succ0_prop.
    rewrite !succ0_prop ?Hi' //.
    by rewrite succ0_prop // subnS Hk.
    apply Hind; by [apply: leq_trans Hi Hj|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi'n : nat_of i = n'.
{ apply anti_leq; rewrite Hjn Bool.andb_true_r.
  by apply (@leq_trans j.-1); [apply /leP /Nat.lt_le_pred /leP|rewrite Hj']. }
have Hk' : k = 0%N.
{ by rewrite Hi'n Hj' subSnn in Hk; case: Hk. }
rewrite Hk' HG0 HG'0.
apply: Hind =>//.
exact: leq_trans Hi Hj.
Qed.

End generic_ind.

Section inst_ssr_matrix.

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

Context {n' : nat}.
Let n := n'.+1.
Instance ssr_I0 : I0_class ordT n := ord0.
Instance ssr_succ0 : succ0_class ordT n := fun i => inord i.+1.
Instance ssr_nat_of : nat_of_class ordT n := @nat_of_ord n.

Definition ytilded5 : 'I_n -> T -> 'M[T]_(1, n) -> 'M[T]_(1, n) -> T -> T :=
  @ytilded3 T ordT mxT _ _ _.

Definition ytildes5 : 'I_n -> T -> 'M[T]_(1, n) -> T :=
  @ytildes3 T ordT mxT _ _ _.

Definition inner_loop5 : 'I_n -> 'M[T]_n -> 'M[T]_n -> 'I_n -> 'M[T]_n :=
  @inner_loop3 T ordT mxT _ _ _ _ _ _ _ _.

Definition outer_loop5 : 'M[T]_n -> 'M[T]_n -> 'I_n -> 'M[T]_n :=
  @outer_loop3 T ordT mxT _ _ _ _ _ _ _ _ _ _.

Definition cholesky5 : 'M[T]_n -> 'M[T]_n :=
  @cholesky3 T ordT mxT _ _ _ _ _ _ _ _ _ _.

Section proof.

Lemma ssr_store3_eq (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  nat_of_ord i' = i -> nat_of_ord j' = j -> (ssr_store3 M i j v) i' j' = v.
Proof. by move=> Hi Hj; rewrite mxE Hi Hj !eq_refl. Qed.

Lemma ssr_store3_lt1 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (nat_of_ord i' < i)%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE (ltn_eqF Hi). Qed.

Lemma ssr_store3_lt2 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (nat_of_ord j' < j)%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. by move=> Hj; rewrite mxE (ltn_eqF Hj) Bool.andb_false_r. Qed.

Lemma ssr_store3_gt1 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (i < nat_of_ord i')%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. by move=> Hi; rewrite mxE eq_sym (ltn_eqF Hi). Qed.

Lemma ssr_store3_gt2 (M : 'M[T]_n) (i j : 'I_n) v i' j' :
  (j < nat_of_ord j')%N -> (ssr_store3 M i j v) i' j' = M i' j'.
Proof. 
move=> Hj.
by rewrite mxE (@eq_sym _ (nat_of_ord j')) (ltn_eqF Hj) Bool.andb_false_r.
Qed.

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
  (forall (j i : 'I_n),
     (i < j)%N ->
     (R i j = gen_ytilded3 (A i j)
                           [ffun k : 'I_i => R (inord k) i]
                           [ffun k : 'I_i => R (inord k) j]
                           (R i i)))
  /\ (forall (j : 'I_n),
        (R j j = gen_ytildes3 (A j j)
                              [ffun k : 'I_j => R (inord k) j])).

(** *** Loop invariants. *)

Definition outer_loop_inv (A R : 'M[T]_n) j : Prop :=
  (forall (j' i' : 'I_n),
     (j' < j)%N ->
     (i' < j')%N ->
     (R j' i' = gen_ytilded3 (A i' j')
                  [ffun k : 'I_i' => R i' (inord k)]
                  [ffun k : 'I_i' => R j' (inord k)]
                  (R i' i')))
  /\ (forall (j' : 'I_n),
        (j' < j)%N ->
        (R j' j' = gen_ytildes3 (A j' j') [ffun k : 'I_j' => R j' (inord k)])).

Definition inner_loop_inv (A R : 'M[T]_n) j i : Prop :=
  outer_loop_inv A R j /\
  (forall (j' i' : 'I_n),
        nat_of_ord j' = j ->
        (i' < i)%N ->
        (i' < j)%N ->
        (R j' i' = gen_ytilded3 (A i' j')
                     [ffun k : 'I_i' => R i' (inord k)]
                     [ffun k : 'I_i' => R j' (inord k)]
                     (R i' i'))).

Global Instance ord_succ0 : succ0_correct ordT n.
Proof. by move=> i H; rewrite /nat_of /ssr_nat_of inordK. Qed.

Global Instance ord_I0 : I0_correct ordT n.
Proof. by []. Qed.

Global Instance ord_nat_of : nat_of_correct ordT n.
Proof. apply ord_inj. Qed.

Lemma inner_loop_correct (A R : 'M_n) (j i : 'I_n) :
  inner_loop_inv A R j i -> inner_loop_inv A (inner_loop5 j A R i) j n.
Proof.
move=> H; cut (inner_loop_inv A (inner_loop5 j A R i) j j).
{ by move=> {H} [Ho Hi]; split; [|move=> j' i' Hj' _ Hi'; apply Hi]. }
move: H; case (leqP i j).
{ move: i R.
  eapply trec_ind with
    (G := fun k (i : 'I_n) s => inner_loop_rec3 j k A s i)
    (P := fun i R => inner_loop_inv A R j i)
    (f := fun i R => store R j i (ytilded3 i (A i j) (row i R) (row j R)
                                           (fun_of_matrix R i i))) =>//.
  { apply ltnW, ltn_ord. }
  move=> i R _(*!*) [Ho Hi]; split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
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
  { apply anti_leq; rewrite Hii' Bool.andb_true_r -ltnS //. }
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
  rewrite ssr_store3_lt1 -Hini inord_val //.
  exact: leq_ltn_trans Hii' _. }
move=> Hji [Ho Hi]; rewrite /inner_loop5 /inner_loop3.
have Hjsi : (nat_of j - nat_of i = 0)%N; [by apply /eqP /ltnW|rewrite Hjsi /=].
by split; [|move=> j' i' Hj' _ Hi'; apply Hi; [|apply (ltn_trans Hi')|]].
Qed.

Lemma outer_loop_correct (A R : 'M_n) (j : 'I_n) :
  outer_loop_inv A R j -> outer_loop_inv A (outer_loop5 A R j) n.
Proof.
move: j R (ltnW (ltn_ord j)); unfold outer_loop5.
eapply trec_ind with
  (G := fun k (j : 'I_n) s => outer_loop_rec3 k A s j)
  (P := fun j R => outer_loop_inv A R j)
  (f := fun j R => let R := inner_loop3 j A R I0 in
                   store R j j (ytildes3 j (A j j) (row j R))) =>//.
move=> j R _(*!*) H.
have Hin_0 : inner_loop_inv A R j (@ord0 n'); [by []|].
have Hin_n := inner_loop_correct Hin_0.
split; [move=> j' i' Hj' Hi'|move=> j' Hj'].
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
rewrite inordK //; apply (ltn_trans Hj''); rewrite -Hj'j; apply ltn_ord.
Qed.

(** *** The implementation satisfies the specification used in cholesky.v. *)

Lemma cholesky5_correct (A : 'M[T]_n) : gen_cholesky_spec A (cholesky5 A)^T.
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

(* TODO : is_sym_correct:
   is_sym A = true -> MF2R (MFI2F A^T) = MF2R (MFI2F A) *)

Definition ssr_all_diag : (T -> bool) -> 'M[T]_n -> bool :=
  @all_diag _ _ _ ssr_fun_of _ _ ssr_succ0.

Lemma all_diag_correct f (A : 'M[T]_n) :
  ssr_all_diag f A = true -> forall i, f (A i i) = true.
Proof.
move=> Had i; move: (ltn_ord i) Had; change (nat_of_ord i) with (nat_of i).
set P := fun i b => b = true -> f (A i i) = true.
rewrite -/(P i (ssr_all_diag f A)).
apply trec_ind'_case with (G := fun k i b => all_diag_rec f k A b i)
  (f0 := fun i b => b && f (fun_of_matrix A i i)) => // j s Hj H.
{ move=> j' Hj'.
  by rewrite /P Bool.andb_true_iff => Hb; elim Hb => Hb' _; apply H. }
by rewrite /P Bool.andb_true_iff => Hb; elim Hb.
Qed.

Definition ssr_foldl_diag (T' : Type) : (T' -> T -> T') -> T' -> 'M[T]_n -> T' :=
  @foldl_diag _ _ _ ssr_fun_of _ _ ssr_succ0 T'.

Lemma foldl_diag_correct (T' : Type) (f : T' -> T -> T') (z : T') (A : 'M[T]_n) :
  forall (P : nat -> T' -> Type),
  (forall (i : 'I_n) z, P i z -> P i.+1 (f z (A i i))) ->
  P O z -> P n (ssr_foldl_diag f z A).
Proof.
move=> P Hind.
rewrite /ssr_foldl_diag /foldl_diag.
set G := fun j i s => foldl_diag_rec f s j A i; rewrite -/(G _ _ _).
replace (G _ _ _) with (G (n - nat_of I0)%N ord0 z); [|by rewrite I0_prop].
rewrite -I0_prop.
by eapply trec_ind => // i s Hi HPi; apply Hind.
Qed.

Definition ssr_map_diag : (T -> T) -> 'M[T]_n -> 'M[T]_n :=
  @map_diag _ _ _ ssr_fun_of _ _ _ ssr_succ0.

Lemma map_diag_correct_ndiag f (A : 'M[T]_n) :
  forall i j : 'I_n, (i < j)%N -> (map_diag f A) i j = A i j.
Proof.
move=> i j Hij.
rewrite /map_diag.
suff H : forall k R i', (matrix.fun_of_matrix
  (@map_diag_rec _ _ _ ssr_fun_of ssr_store3 _ ssr_succ0 f k A R i')
    i j = R i j) => //; elim => // k IHk R i' /=.
rewrite IHk; case (ltnP i' j) => Hi'j.
{ rewrite ssr_store3_gt2 //. }
by rewrite ssr_store3_lt1 //; apply (leq_trans Hij).
Qed.

Lemma map_diag_correct_diag f (A : 'M[T]_n) :
  forall i, (map_diag f A) i i = f (A i i).
Proof.
move=> i; move: (ltn_ord i); change (nat_of_ord i) with (nat_of i).
set P := fun i s => s i i = f (A i i); rewrite -/(P i _) /map_diag.
eapply trec_ind'_case with (i0 := i)
  (G := fun k i b => map_diag_rec f k A b i) => //.
{ move=> j s Hj Hind j' Hj' _.
  rewrite /P ssr_store3_lt1 //; apply Hind => //; apply ltn_ord. }
{ move=> j s Hj Hind _; rewrite /P ssr_store3_eq //. }
apply ltn_ord.
Qed.

End proof.

End inst_ssr_matrix.

Section proof_inst_ssr_matrix_float_infnan.

Context {n' : nat}.
Let n := n'.+1.

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

Lemma gen_cholesky_spec_correct (A R : 'M[FI fs]_n) :
  gen_cholesky_spec A R -> cholesky_spec_infnan A R.
Proof.
move=> H; split.
{ by move=> j i Hij; rewrite (proj1 H) // gen_ytilded3_correct. }
by move=> j; rewrite (proj2 H) // gen_ytildes3_correct.
Qed.

(** If [A] contains no infinity or NaN, then [MFI2F A] = [A] and
    [posdef (MF2R (MFI2F A))] means that [A] is positive definite. *)
Lemma gen_corollary_2_4_with_c_upper_bound_infnan :
  4 * INR n.+1 * eps (fis fs) < 1 ->  (* need a small program to check *)
  forall A : 'M[FI fs]_n,
  cholesky.MF2R (MFI2F A^T) = cholesky.MF2R (MFI2F A) ->  (* need a small program to check *)
  (forall i : 'I_n, 0 <= (MFI2F A) i i) ->  (* need a small program to check *)
  forall maxdiag : R, (forall i : 'I_n, (MFI2F A) i i <= maxdiag) ->  (* need a small program to compute *)
  forall c : R,
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + maxdiag)
   <= c)%Re ->  (* need a small program to compute (with directed rounding) *)
  forall At : 'M[FI fs]_n,
  ((forall i j : 'I_n, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n, (MFI2F At) i i <= (MFI2F A) i i - c)) ->  (* need a small program to compute (with directed rounding) *)
  let R := cholesky5 At in
  (forall i, (0 < (MFI2F R) i i)%Re) ->  (* need a small program to check *)
  real_matrix.posdef (cholesky.MF2R (MFI2F A)).
Proof.
move=> H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt R HAR.
apply corollary_2_4_with_c_upper_bound_infnan with maxdiag c At R^T;
  try assumption; split; [|by move=> i; move: (HAR i); rewrite !mxE].
apply gen_cholesky_spec_correct, cholesky5_correct.
Qed.

Variable eps_inv : BigZ.t_.

(* Example:
 * Definition eps_inv := Eval vm_compute in (2^53)%bigZ. *)

Hypothesis eps_inv_spec : Z2R [eps_inv] <= / eps (fis fs).

Definition test_n : bool :=
  (4 * (BigZ.of_Z (Z.of_nat n) + 1) <? eps_inv)%bigZ.

Lemma test_n_correct : test_n = true ->
  4 * INR n.+1 * eps (fis fs) < 1.
Proof.
unfold test_n; intro H.
case (Req_dec (eps (fis fs)) 0); intro Heps; [rewrite Heps; lra|].
rewrite <- (Rinv_l _ Heps) at 5.
apply Rmult_lt_compat_r; [assert (H' := eps_pos (fis fs)); lra|].
revert eps_inv_spec; apply Rlt_le_trans.
rewrite S_INR INR_IZR_INZ -Z2R_IZR.
change 4 with (Z2R 4); rewrite -(Z2R_plus _ 1) -Z2R_mult.
apply Z2R_lt; revert H; rewrite Zlt_is_lt_bool BigZ.spec_ltb.
by rewrite BigZ.spec_mul BigZ.spec_add BigZ.spec_of_Z.
Qed.

Instance leq_infnan : leq (FI fs) := @file fs.

Instance lt_infnan : lt (FI fs) := @filt fs.

Definition gen_max_diag (A : 'M[FI fs]_n) : FI fs :=
  @max_diag _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0 _ A.

Lemma max_diag_correct (A : 'M[FI fs]_n) : (forall i, finite (A i i)) ->
  forall i, (MFI2F A) i i <= FI2F (gen_max_diag A).
Proof.
move=> HF; rewrite /gen_max_diag /max_diag -/(ssr_foldl_diag _ _ _).
rewrite /zero_op /zero_infnan.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
move=> i; move: i (ltn_ord i).
set P' := fun j (s : FI fs) => forall (i : 'I_n), (i < j)%N ->
  (MFI2F A) i i <= FI2F s; rewrite -/(P' _ _).
suff : (finite (ssr_foldl_diag f (FI0 fs) A)
        /\ P' n (ssr_foldl_diag f (FI0 fs) A)).
{ by move=> H; elim H. }
set P := fun j s => finite s /\ P' j s; rewrite -/(P _ _).
apply foldl_diag_correct; rewrite /P /P'.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by case (fimax_spec_eq z (A i i)) => H; rewrite /f -/(fimax _ _) H. }
  move=> j Hj; case (ltnP j i) => Hji.
  { rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ (Hind' _ Hji)).
    by apply fimax_spec_lel. }
  have H' : j = i.
  { by apply ord_inj, anti_leq; rewrite Hji Bool.andb_true_r. }
  by rewrite H' /f -/(fimax _ _) mxE; apply fimax_spec_ler. }
by split; [apply finite0|].
Qed.

Lemma max_diag_pos (A : 'M[FI fs]_n) : (forall i, finite (A i i)) ->
  0 <= FI2F (gen_max_diag A).
Proof.
move=> HF; rewrite /gen_max_diag /max_diag -/(ssr_foldl_diag _ _ _).
rewrite /zero_op /zero_infnan.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
suff : (finite (ssr_foldl_diag f (FI0 fs) A)
        /\ 0 <= FI2F (ssr_foldl_diag f (FI0 fs) A)).
{ by move=> H; elim H. }
set P := fun (j : nat) s => @finite fs s /\ 0 <= FI2F s.
apply foldl_diag_correct with (P0 := P); rewrite /P.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by case (fimax_spec_eq z (A i i)) => H; rewrite /f -/(fimax _ _) H. }
  by rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ Hind'), fimax_spec_lel. }
by split; [apply finite0|rewrite FI2F0; right].
Qed.

(* addition with upward rounding *)
Variable add_up : FI fs -> FI fs -> FI fs.

Instance add_up_infnan : add (FI fs) := add_up.

Hypothesis add_up_spec : forall x y, finite (add_up x y) ->
  (FI2F x + FI2F y <= FI2F (add_up x y))%R.
Hypothesis add_up_spec_fl : forall x y, finite (add_up x y) -> finite x.
Hypothesis add_up_spec_fr : forall x y, finite (add_up x y) -> finite y.

Definition gen_tr_up (n : nat) (A : 'M[FI fs]_n.+1) : FI fs :=
  @tr_up _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0 add_up_infnan A.

Lemma tr_up_correct (A : 'M[FI fs]_n) : finite (gen_tr_up A) ->
  \tr (cholesky.MF2R (MFI2F A)) <= FI2F (gen_tr_up A).
Proof.
rewrite /gen_tr_up /tr_up -/(ssr_foldl_diag _ _ _) /zero_op /zero_infnan.
replace (\tr _) with (\sum_(i < n) (FI2F (A (inord i) (inord i)) : R));
  [|by apply eq_big => // i _; rewrite !mxE inord_val].
set P := fun j (s : FI fs) => finite s ->
  (\sum_(i < j) (FI2F (A (inord i) (inord i)) : R)) <= FI2F s.
rewrite -/(P _ _); apply foldl_diag_correct; rewrite /P.
{ move=> i z Hind Fa; move: (add_up_spec Fa); apply Rle_trans.
  rewrite big_ord_recr /= /GRing.add /= inord_val.
  apply Rplus_le_compat_r, Hind, (add_up_spec_fl Fa). }
move=> _; rewrite big_ord0 FI2F0; apply Rle_refl.
Qed.

Variable one_up : FI fs.  (* TODO: extend float_infnan_spec *)

Instance one_up_infnan : one (FI fs) := one_up.

Hypothesis one_up_spec : 1 <= FI2F one_up.
Hypothesis one_up_spec' : FI2F 1%C <= 1.

Lemma float_of_nat_up_correct k : finite (float_of_nat_up k) ->
  INR k <= FI2F (float_of_nat_up k).
Proof.
rewrite /float_of_nat_up.
elim: k => [|k IHk].
{ move=> _; rewrite FI2F0; apply Rle_refl. }
move=> Fa; move: (add_up_spec Fa); apply Rle_trans; rewrite S_INR.
apply Rplus_le_compat => //; apply IHk.
move: Fa => /=; apply add_up_spec_fl.
Qed.

(* multiplication with upward rounding *)
Variable mul_up : FI fs -> FI fs -> FI fs.

Instance mul_up_infnan : mul (FI fs) := mul_up.

Hypothesis mul_up_spec : forall x y, finite (mul_up x y) ->
  (FI2F x * FI2F y <= FI2F (mul_up x y))%R.
Hypothesis mul_up_spec_fl : forall x y, finite (mul_up x y) -> finite x.
Hypothesis mul_up_spec_fr : forall x y, finite (mul_up x y) -> finite y.

(* division with upward rounding *)
Variable div_up : FI fs -> FI fs -> FI fs.

Instance div_up_infnan : div (FI fs) := div_up.

Hypothesis div_up_spec : forall x y, finite (div_up x y) -> finite y ->
  (FI2F x / FI2F y <= FI2F (div_up x y))%R.
Hypothesis div_up_spec_fl : forall x y, finite (div_up x y) -> finite y ->
  finite x.

Definition gen_compute_c_aux (eps eta : FI fs) (A : 'M[FI fs]_n)
  (maxdiag : FI fs) : FI fs := 
  @compute_c_aux _ _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0 add_up_infnan
    mul_up_infnan div_up_infnan one_up_infnan eps eta A maxdiag.

Lemma compute_c_aux_correct (eps' eta' : FI fs) (A : 'M[FI fs]_n) maxdiag :
  eps (fis fs) <= FI2F eps' -> eta (fis fs) <= FI2F eta' ->
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (finite (add_up_infnan
             (mul_up_infnan ((float_of_nat_up (2 * n.+1)%N)) eps')
             (- (1)))%C) ->
  (FI2F (add_up_infnan
             (mul_up_infnan ((float_of_nat_up (2 * n.+1)%N)) eps')
             (- (1)))%C < 0) ->
  (forall i, 0 <= FI2F (A i i)) ->
  (0 <= FI2F maxdiag) ->
  finite (gen_compute_c_aux eps' eta' A maxdiag) ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F maxdiag)
  <= FI2F (gen_compute_c_aux eps' eta' A maxdiag))%R.
Proof.
have Pnp2 := pos_INR (n.+1)%N.
have P2np2 := pos_INR (2 * n.+1)%N.
have Pe := eps_pos (fis fs).
move=> Heps' Heta' Heps Fnem1 Nnem1 Pdiag Pmaxdiag Fc.
rewrite /gen_compute_c_aux /compute_c_aux.
move: (add_up_spec Fc); apply Rle_trans, Rplus_le_compat.
{ have Fl := add_up_spec_fl Fc.
  move: (mul_up_spec Fl); apply Rle_trans, Rmult_le_compat.
  { by apply Rmult_le_pos; [lra|apply gamma_pos]. }
  { by apply big_sum_pos_pos => i; rewrite !mxE. }
  { rewrite /gamma mult_INR -!(Rmult_assoc (/2)) Rinv_l; [|lra].
    rewrite Rmult_1_l.
    have Fll := mul_up_spec_fl Fl.
    have F1mne := fiopp_spec_f Fnem1.
    move: (div_up_spec Fll F1mne); apply Rle_trans, Rmult_le_compat.
    { apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
    { apply Rlt_le, Rinv_0_lt_compat; rewrite -mult_INR.
      by set ne := Rmult _ _; apply (Rplus_lt_reg_r ne); ring_simplify. }
    { have Flr := div_up_spec_fl Fll F1mne.
      move: (mul_up_spec Flr); apply /Rle_trans /Rmult_le_compat => //.
      apply float_of_nat_up_correct, (mul_up_spec_fl Flr). }
    rewrite (fiopp_spec F1mne) -mult_INR; apply Rinv_le.
    { by rewrite -Ropp_0; apply Ropp_lt_contravar. }
    rewrite -Ropp_minus_distr; apply Ropp_le_contravar.
    move: (add_up_spec Fnem1); apply Rle_trans; apply Rplus_le_compat.
    { have Fne := add_up_spec_fl Fnem1.
      move: (mul_up_spec Fne); apply /Rle_trans /Rmult_le_compat => //.
      apply float_of_nat_up_correct, (mul_up_spec_fl Fne). }
    rewrite (fiopp_spec (add_up_spec_fr Fnem1)); apply Ropp_le_contravar.
    apply one_up_spec'. }
  apply tr_up_correct, (mul_up_spec_fr Fl). }
have Fr := add_up_spec_fr Fc.
move: (mul_up_spec Fr); apply Rle_trans; apply Rmult_le_compat.
{ apply Rmult_le_pos; [|by apply pos_INR]; apply Rmult_le_pos; [lra|].
  apply Rlt_le, eta_pos. }
{ apply Rplus_le_le_0_compat; [|apply Pmaxdiag].
  apply Rmult_le_pos; [lra|apply pos_INR]. }
{ move: (mul_up_spec (mul_up_spec_fl Fr)); apply Rle_trans.
  have Frl := mul_up_spec_fl Fr.
  apply Rmult_le_compat.
  { apply Rmult_le_pos; [lra|apply Rlt_le, eta_pos]. }
  { apply pos_INR. }
  { have Frll := mul_up_spec_fl Frl.
    move: (mul_up_spec Frll); apply Rle_trans.
    apply Rmult_le_compat; [lra|apply Rlt_le, eta_pos| |apply Heta'].
    replace 4 with (INR 4); [|by simpl; lra].
    apply float_of_nat_up_correct, (mul_up_spec_fl Frll). }
  apply float_of_nat_up_correct, (mul_up_spec_fr Frl). }
have Frr := mul_up_spec_fr Fr.
move: (add_up_spec Frr); apply Rle_trans, Rplus_le_compat_r.
have Frrl := add_up_spec_fl Frr.
by change 2 with (INR 2); rewrite -mult_INR; apply float_of_nat_up_correct.
Qed.

Definition gen_compute_c (eps eta : FI fs) (A : 'M[FI fs]_n) :
  option (FI fs) := 
  @compute_c _ _ _ zero_infnan opp_infnan ssr_fun_of _ ssr_I0 ssr_succ0
    leq_infnan lt_infnan
    add_up_infnan mul_up_infnan div_up_infnan one_up_infnan
    (@is_finite fs) eps eta A.

Lemma compute_c_correct (eps' eta' : FI fs) (A : 'M[FI fs]_n) :
  (eps (fis fs) <= FI2F eps')%R -> (eta (fis fs) <= FI2F eta')%R ->
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (forall i, finite (A i i)) ->
  (forall i, (0 <= FI2F (A i i))%R) ->
  forall c : FI fs, gen_compute_c eps' eta' A = Some c ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F (gen_max_diag A))
   <= FI2F c)%R.
Proof.
move=> Heps' Heta' Heps Fdiag Pdiag c.
rewrite /gen_compute_c /compute_c.
set nem1 := add_up_infnan _ _.
case_eq (is_finite nem1 && (nem1 < 0)%C); [|by []].
rewrite Bool.andb_true_iff => H; elim H => Fnem1 Nnem1.
set c' := compute_c_aux _ _ _ _.
case_eq (is_finite c') => Hite'; [|by []]; move=> Hc'.
have Hc'' : c' = c by injection Hc'.
rewrite -Hc''; apply compute_c_aux_correct => //.
{ apply (Rlt_le_trans _ (FI2F 0%C)); [|by right; rewrite FI2F0].
  apply filt_spec => //; apply finite0. }
by apply max_diag_pos.
Qed.  

(*

(* subtraction rounded downward *)
Definition sub_down x y := (- (add1 y (- x)%C))%C.

*)

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

Context {n : nat}.
Instance : I0_class ordT n.+1 := O.
Instance : succ0_class ordT n.+1 := S.
Instance : nat_of_class ordT n.+1 := id.

Instance : succ0_correct ordT n.+1.
Proof. done. Qed.

Definition cholesky4 (M : seq (seq T)) : seq (seq T) :=
  @cholesky3 T ordT _ _ _ _ _ _ _ n.+1 _ _ _ M.

Definition outer_loop_rec4 :=
  @outer_loop_rec3 T _ _ _ _ _ _ _ _ n.+1 _ _ _.

Definition inner_loop_rec4 :=
  @inner_loop_rec3 T _ _ _ _ _ _ _ n.+1 _.

Definition outer_loop4 :=
  @outer_loop3 T _ _ _ _ _ _ _ _ n.+1 _ _ _.

Definition inner_loop4 :=
  @inner_loop3 T _ _ _ _ _ _ _ n.+1 _.

Lemma size_store3 :
  forall s i j x,
  seq.size (@store3 T s j i x) = seq.size s.
Proof.
move=> s i j x.
elim: s j => [|a s IHs] j; first by case: j.
case: j IHs => [|j] IHs //=.
by rewrite -(IHs j).
Qed.

Lemma size_inner_loop_rec4 :
  forall A j i R,
  (nat_of i <= nat_of j)%N ->
  (nat_of j <= n.+1)%N ->
  seq.size R = n.+1 ->
  seq.size (inner_loop_rec3 (T := T) (ordT := ordT) (n := n.+1)
    j (nat_of j - nat_of i) A R i) = n.+1.
Proof.
move=> A j i R Hi Hj.
eapply trec_ind with
  (G := fun k (i : ordT n.+1) R => inner_loop_rec3 j k A R i) =>//.
by move=> i0 s Hs /=; rewrite size_store3.
Qed.

Lemma size_outer_loop_rec4 :
  forall A R (j : ordT n.+1),
  (nat_of j <= n.+1)%N ->
  seq.size R = n.+1 ->
  seq.size (outer_loop_rec3 (T := T) (ordT := ordT) (mxT := mxT) (n := n.+1)
    (nat_of n.+1 - nat_of j) A R j) = n.+1.
Proof.
move=> A R j Hj HRs.
eapply trec_ind with
  (G := fun k (i : ordT n.+1) R => outer_loop_rec3 k A R i) =>//.
move=> i s Hle Hs /=; rewrite size_store3.
exact: size_inner_loop_rec4.
Qed.

Lemma size_cholesky4 M :
  seq.size M = n.+1 ->
  seq.size (cholesky4 M) = n.+1.
Proof.
move=> HM.
exact: size_outer_loop_rec4.
Qed.

Lemma size_seq_store3 :
  forall s i x,
  seq.size (@seq_store3 T s i x) = seq.size s.
Proof.
move=> s i x.
elim: s i => [|a s IHs] i; first by case: i.
case: i IHs => [|i] IHs //=.
by rewrite -(IHs i).
Qed.

Lemma size_nth_store3 :
  forall s i j k x,
  seq.size (nth [::] (@store3 T s j i x) k) = seq.size (nth [::] s k).
Proof.
move=> s i j k x.
elim: s j k => [|a s IHs] j k; first by case: j.
case: j IHs => [|j] IHs //=; case: k IHs => [|k] IHs //=.
by rewrite size_seq_store3.
Qed.

Lemma size_nth_inner_loop_rec4 :
  forall A j i k R,
  (nat_of i <= nat_of j)%N ->
  (nat_of j <= n.+1)%N ->
  seq.size (nth [::] R k) = n.+1 ->
  seq.size (nth [::] (inner_loop_rec3 (T := T) (ordT := ordT) (n := n.+1)
    j (nat_of j - nat_of i) A R i) k) = n.+1.
Proof.
move=> A j i k R Hi Hj.
eapply trec_ind with
  (G := fun k (i : ordT n.+1) R => inner_loop_rec3 j k A R i) =>//.
by move=> i0 s Hle Hs; rewrite size_nth_store3.
Qed.

Lemma size_nth_outer_loop_rec4 :
  forall A R (i : nat) j,
  (i < n.+1)%N ->
  (nat_of j <= n.+1)%N ->
  seq.size (nth [::] R i) = n.+1 ->
  seq.size (nth [::] (outer_loop_rec3 (T := T) (ordT := ordT) (mxT := mxT) (n := n.+1)
    (nat_of n.+1 - nat_of j) A R j) i) = n.+1.
Proof.
move=> A R i j Hi Hj HRs.
eapply trec_ind with
  (G := fun k (i : ordT n.+1) R => outer_loop_rec3 k A R i) =>//.
move=> i0 s Hle Hs; rewrite size_nth_store3.
by apply size_nth_inner_loop_rec4.
Qed.

Lemma size_nth_cholesky4 M :
  forall i : nat, (i < n.+1)%N ->
  seq.size (nth [::] M i) = n.+1 ->
  seq.size (nth [::] (cholesky4 M) i) = n.+1.
Proof.
by move=> *; apply: size_nth_outer_loop_rec4.
Qed.

End inst_seq.

Section Rseqmx_aux.
(* Aim: refinement proofs using seqmatrix.v *)
Require Import CoqEAL_theory.hrel.

Context {A : Type}. (* {ordC : nat -> Type} {mxC : nat -> nat -> Type}. *)
Context `{!zero A}.
(*
Local Notation ordA := (fun _ : nat => nat) (only parsing).
Local Notation mxA := (fun _ _ : nat => seqmatrix A) (only parsing).
Context `{!zero A, !one A, !add A, !opp A, (* !sub A, *) !mul A, !div A, !sqrt A}.
Context `{!fun_of A ordA mxA, !row_class ordA mxA}.
*)

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

Section data_refinement.

(*
(* Abstract types *)
Context {A : Type}. (* {ordA : nat -> Type} {mxA : nat -> nat -> Type}. *)
Local Notation ordA := ordinal (only parsing).
Local Notation mxA := (fun m n => 'M[A]_(m, n)) (only parsing).
Context `{!zero A, !one A, !add A, !opp A, (* !sub A, *) !mul A, !div A, !sqrt A}.
*)

(* Concrete types *)
Context {C : Type}. (* {ordC : nat -> Type} {mxC : nat -> nat -> Type}. *)
Local Notation ordC := (fun _ : nat => nat) (only parsing).
Local Notation mxC := (fun _ _ : nat => seqmatrix C) (only parsing).
Context `{!zero C, !one C, !add C, !opp C, (* !sub C, *) !mul C, !div C, !sqrt C}.
Context `{!fun_of C ordC mxC, !row_class ordC mxC, !store_class C ordC mxC, !dotmulB0_class C ordC mxC}.
Context {n : nat}.
Context `{!I0_class ordC n.+1, !succ0_class ordC n.+1, !nat_of_class ordC n.+1}.
Context `{!succ0_correct ordC n.+1}.

Local Notation ordA := ordinal (only parsing).
Local Notation mxA := (fun m n => 'M[C]_(m, n)) (only parsing).

(* Context {RmxC : forall {m n}, mxA m n -> mxC m n -> Prop}.
Arguments RmxC {m n} _ _. (* maximal implicit arguments *)

Context {RordC : forall m, ordA m -> ordC m -> Prop}.
Arguments RordC {m} _ _. *)

(*
Context {RC : A -> C -> Prop}.
Let RmxC := (@RseqmxA A C RC).
Arguments RmxC {m n} _ _. (* maximal implicit arguments *)
*)

Local Notation RmxC := Rseqmx (only parsing). (* from seqmatrix.v *)

Local Notation RordC := Rord (only parsing).
Arguments RordC {n} _ _.

(*
Context `{forall m n, param (RmxC ==> RordC ==> RordC ==> Logic.eq)
  (@matrix.fun_of_matrix _ m n) (@fun_of_matrix _ _ mxC _ m n)}.

Context `{forall m n, param (RordC ==> RmxC ==> RmxC)
  (@matrix.row _ m n) (@row _ _ _ m n)}.
*)

Context `{!param (RmxC ==> RordC ==> RordC ==> Logic.eq ==> RmxC)
  (ssr_store3 (m := n.+1) (n := n.+1)) (@store3 C)}.

Context `{forall n, param (RordC ==> Logic.eq ==> RmxC ==> RmxC ==> Logic.eq)
  (@ssr_dotmulB0 _ _ _ _ n) (@dotmulB0 C _ _ _ n)}.

Global Instance param_outer_loop :
  param (RmxC ==> RmxC ==> RordC ==> RmxC)
  (outer_loop5 (n := n)) (outer_loop4 (n := n)).
Proof.
eapply param_abstr => A As param_A.
eapply param_abstr => R Rs param_R.
eapply param_abstr => j js param_j.
rewrite /outer_loop5 /outer_loop4 paramE.
rewrite paramE /Rord in param_j.
rewrite /outer_loop3.
rewrite -/outer_loop_rec4.
rewrite paramE in param_R.
eapply trec_ind2 with
  (G := fun k (i : 'I_n.+1) R => outer_loop_rec3 k A R i)
  (G' := fun k (i : ordC n.+1) Rs => outer_loop_rec4 k As Rs i)
  (P := fun R Rs => Rseqmx R Rs) =>//.
done. done. done. done. done.
3: by rewrite -param_j.
2: exact/ltnW/ltn_ord.
move=> i i' s s' Hi Hi' param_s /=.
rewrite /store.
rewrite /store_class_instance_0 /store_class_instance_1.
apply paramP.
eapply param_apply.
eapply param_apply.
eapply param_apply.
eapply param_apply.
by tc.
admit.
by rewrite paramE.
by rewrite paramE.
eapply param_apply.
eapply param_apply.
admit.
eapply param_apply.
eapply param_apply.
eapply param_apply.
eapply Rseqmx_fun_of_seqmx'.
done.
by rewrite paramE.
by rewrite paramE.
eapply param_apply.
eapply param_apply.
eapply Rseqmx_rowseqmx'.
by rewrite paramE.
admit. (* again *)
Unshelve. (* FIXME: this should be automatically discharged *)
apply: ord_succ0.
by tc.
Admitted.

(*
Ingredients:
exact: get_param.
eapply param_abstr=> a c param_ac.
rewrite paramE.
eapply param_apply.
by tc.
*)

(*
exact: param_R.
apply: refines_seqmxP.
- { rewrite size_outer_loop_rec4 //.
    rewrite -param_j.
    exact/ltnW/ltn_ord.
    by rewrite sizeE.
  }
- { move=> i Hi; rewrite size_nth_outer_loop_rec4 //.
    rewrite -param_j.
    exact/ltnW/ltn_ord.
    by rewrite !sizeE.
  }
- move=> i k.
  rewrite -(inord_val j) param_j.
  rewrite /outer_loop3.
  set mo := (outer_loop_rec3 (n.+1 - nat_of (inord js)) A R (inord js)).
  eapply trec_ind2 with
    (G := fun k (i : ordT n.+1) R => outer_loop_rec3 k A R i)
    (G' := fun k (i : ordT n.+1) R => outer_loop_rec3 k As Rs i).
*)

Global Instance param_cholesky :
  param (RmxC ==> RmxC)%rel (cholesky5 (n := n)) (cholesky4 (n := n)).
Proof.
eapply param_abstr => m s param_ms; rewrite /cholesky5 /cholesky4.
rewrite paramE.
apply: refines_seqmxP.
- by rewrite size_cholesky4 ?sizeE.
- by move=> i Hi; rewrite size_nth_cholesky4 ?sizeE.
- move=> i j; rewrite /cholesky3 /=.
  eapply refines_nth.
  eapply param_apply; try by tc.
  by rewrite paramE.
Qed.

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
