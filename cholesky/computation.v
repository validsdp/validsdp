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

Require Import CoqEAL_theory.hrel.

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

(* when j <= n, [for_ord i j f x] returns
 *
 * for k : ordT n from 0 to (j - 1) do
 *   x := f k x
 * done;
 * x *)
Fixpoint iteri_ord_rec T k i (f : ordT n -> T -> T) (x : T) :=
  match k with
    | O => x
    | S k => iteri_ord_rec k (succ0 i) f (f i x)
  end.
Definition iteri_ord T j (f : ordT n -> T -> T) x := iteri_ord_rec j I0 f x.

Definition inner_loop3 j A R :=
  iteri_ord (nat_of j)
            (fun i R => store R j i (ytilded3 i (fun_of_matrix A i j)
                                              (row i R) (row j R)
                                              (fun_of_matrix R i i)))
            R.

(* Section InnerLoop. *)
(* Variable j : ordT n. *)
(* Fixpoint inner_loop_rec3 (k : nat) A R (i : ordT n) {struct k} := *)
(*   match k with *)
(*   | O (* i >= j *) => R *)
(*   | S k => let R := store R j i (ytilded3 i (fun_of_matrix A i j) *)
(*                                           (row i R) (row j R) *)
(*                                           (fun_of_matrix R i i)) in *)
(*            inner_loop_rec3 k A R (succ0 i) *)
(*   end. *)
(* Definition inner_loop3 A R i := inner_loop_rec3 (nat_of j - nat_of i) A R i. *)
(* End InnerLoop. *)

Definition outer_loop3 A R :=
  iteri_ord n
            (fun j R =>
               let R := inner_loop3 j A R in
               store R j j (ytildes3 j (fun_of_matrix A j j)
                                     (row j R)))
            R.

(* Section OuterLoop. *)
(* Fixpoint outer_loop_rec3 k A R (j : ordT n) {struct k} := *)
(*   match k with *)
(*   | O (* j >= n *) => R *)
(*   | S k => *)
(*     let R := inner_loop3 j A R I0 in *)
(*     let R := store R j j (ytildes3 j (fun_of_matrix A j j) *)
(*                                     (row j R)) in *)
(*     outer_loop_rec3 k A R (succ0 j) *)
(*   end. *)
(* Definition outer_loop3 A R j := outer_loop_rec3 (n - nat_of j) A R j. *)
(* End OuterLoop. *)

(* note: the result is transposed with respect to cholesky.v *)
Definition cholesky3 A := outer_loop3 A A.

Context `{!heq mxT}.
Context `{!transpose_class mxT}.

Definition is_sym (A : mxT n n) : bool := (A^T == A)%HC.

Definition all_diag f A :=
  iteri_ord n (fun i b => b && f (fun_of_matrix A i i)) true.

(* Fixpoint all_diag_rec f k (A : mxT n n) b (i : ordT n) {struct k} : bool := *)
(*   match k with *)
(*   | O => b *)
(*   | S k => all_diag_rec f k A (b && f (fun_of_matrix A i i)) (succ0 i) *)
(*   end. *)
(* Definition all_diag f A := all_diag_rec f n A true I0. *)

Context `{!leq T}.

Definition noneg_diag := all_diag (fun x => 0 <= x)%C.

Context `{!lt T}.

Definition pos_diag := all_diag (fun x => 0 < x)%C.

Definition foldl_diag T' f (z : T') A :=
  iteri_ord n (fun i z => f z (fun_of_matrix A i i)) z.

(* Fixpoint foldl_diag_rec (T' : Type) f z k (A : mxT n n) (i : ordT n) *)
(* {struct k} : T' := *)
(*   match k with *)
(*   | O => z *)
(*   | S k => foldl_diag_rec T' f (f z (fun_of_matrix A i i)) k A (succ0 i) *)
(*   end. *)
(* Definition foldl_diag T' f (z : T') A := foldl_diag_rec f z n A I0. *)

Definition max_diag A :=
  foldl_diag (fun m c => if (m <= c)%C then c else m) 0%C A.

Definition map_diag f A :=
  iteri_ord n (fun i A' => store A' i i (f (fun_of_matrix A i i))) A.

(* Fixpoint map_diag_rec f k (A R : mxT n n) (i : ordT n) {struct k} : mxT n n := *)
(*   match k with *)
(*   | O => R *)
(*   | S k => *)
(*     let R := store R i i (f (fun_of_matrix A i i)) in *)
(*     map_diag_rec f k A R (succ0 i) *)
(*   end. *)
(* Definition map_diag f A := map_diag_rec f n A A I0. *)

Section directed_rounding.

(* upward rounded operations *)
Variable add1 mul1 div1 : T -> T -> T.
(* @Érik: idéalement, on aimerait utiliser des typeclasses,
   mais je galère trop, on verra ça ensemble. *)

Definition tr_up A := foldl_diag add1 0%C A.

(* get a float overapprox of n *)
Definition float_of_nat_up n := iter _ n (fun x => add1 x 1%C) 0%C.

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

Definition posdef_check
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mxT n n) : bool :=
test_n n && is_sym A && noneg_diag A &&
  (match compute_c is_finite eps eta A with
     | None => false
     | Some c =>
       let A' := map_diag (fun x => sub_down x c) A in
       let R := cholesky3 A' in
       all_diag is_finite R && pos_diag R
   end).

End directed_rounding.

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

Section nat_of_theory2.
Variable n : nat.
Let ordT (n : nat) := nat.
Instance : nat_of_class ordinal n := @nat_of_ord n.
Instance : nat_of_class ordT n := id.
Local Notation RordC := Rord (only parsing).
Arguments RordC {n} _ _. (* maximal implicit arguments *)
Global Instance param_nat_of :
  param (RordC ==> Logic.eq) nat_of nat_of.
Proof.
eapply param_abstr => i i' param_i.
rewrite paramE /Rord in param_i.
rewrite -param_i.
by rewrite paramE.
Qed.
End nat_of_theory2.

Section generic_ind.
Context {ordT : nat -> Type} {n' : nat}.
Let n := n'.+1.
Context `{!I0_class ordT n, !succ0_class ordT n, !nat_of_class ordT n}.
Context `{!I0_correct ordT n, !succ0_correct ordT n, !nat_of_correct ordT n}.

Lemma iteri_ord_rec_ind M P (f : ordT n -> M -> M) :
  forall j, (j <= n)%N ->
  (forall (i : ordT n) s,
    (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall (i : ordT n) s, (nat_of i <= j)%N ->
    P (nat_of i) s -> P j (iteri_ord_rec (j - nat_of i)%N i f s).
Proof.
move=> j Hj Hind i s Hi H.
move Hk: (j - nat_of i)%N => k.
move: i Hi Hk s H; elim: k => [|k IHk] i Hi Hk s H /=.
{ replace j with (nat_of i); [by []|].
  by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. }
case (ltnP (nat_of i) j) => [Hij|]; [|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply IHk; erewrite (succ0_prop Hsisn) =>//.
  { by rewrite subnS Hk. }
  by apply Hind; [apply leqW|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi' : nat_of i = n'.
{ apply anti_leq; rewrite Hjn Bool.andb_true_r.
  by apply (@leq_trans j.-1); [apply /leP /Nat.lt_le_pred /leP|rewrite Hj']. }
have Hk' : k = 0%N.
{ apply sym_eq; move: Hk; rewrite Hi' Hj' subSnn; apply eq_add_S. }
by rewrite Hk' Hj' /n /= -Hi'; apply Hind; [rewrite Hi'|].
Qed.

Lemma iteri_ord_ind M P (f : ordT n -> M -> M) :
  forall j, (j <= n)%N ->
  (forall (i : ordT n) s,
    (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall s, P 0%N s -> P j (iteri_ord j f s).
Proof.
move=> j Hj Hind s HP; rewrite /iteri_ord.
replace j with (j - nat_of I0)%N at 2; [|by rewrite I0_prop subn0].
by apply iteri_ord_rec_ind => //; rewrite I0_prop.
Qed.

(* Lemma trec_ind M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) : *)
(*   forall j, (j <= n)%N -> *)
(*   (forall i s, G 0%N i s = s) -> *)
(*   (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) -> *)
(*   (forall (i : ordT n) s, *)
(*     (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) -> *)
(*   forall (i : ordT n) s, *)
(*     (nat_of i <= j)%N -> P (nat_of i) s -> P j (G (j - nat_of i)%N i s). *)
(* Proof. *)
(* move=> j Hj HG0 HGS Hind i s Hi H. *)
(* set (k := (j - nat_of i)%N). *)
(* have Hk : k = (j - nat_of i)%N; [by []|]. *)
(* move: i Hi k Hk s H => i Hi k; move: i Hi; induction k => i Hi Hk s H. *)
(* { rewrite HG0; replace j with (nat_of i); [by []|]. *)
(*   by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. } *)
(* case (ltnP (nat_of i) j); [move=> Hij|by rewrite /ssrnat.leq -Hk]. *)
(* rewrite HGS; case (ltnP (nat_of i) n') => Hjn. *)
(* { have Hsisn : ((nat_of i).+1 < n)%N. *)
(*   { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. } *)
(*     apply IHk; erewrite (succ0_prop Hsisn) =>//. *)
(*     by rewrite subnS -Hk. *)
(*     by apply Hind; [apply leqW|]. } *)
(* have Hj' : j = n. *)
(* { by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). } *)
(* have Hi' : nat_of i = n'. *)
(* { apply anti_leq; rewrite Hjn Bool.andb_true_r. *)
(*     by apply (@leq_trans j.-1); [apply /leP /Nat.lt_le_pred /leP|rewrite Hj']. } *)
(* have Hk' : k = 0%N. *)
(* { move: Hk; rewrite Hi' Hj' subSnn; apply eq_add_S. } *)
(*   by rewrite Hk' HG0 Hj' /n -Hi'; apply Hind; [rewrite Hi'|]. *)
(* Qed. *)

(* above lemma for P j s := forall i, nat_of i < j -> P i s *)
Lemma iteri_ord_ind' M P (f : ordT n -> M -> M) :
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ordT n), (nat_of j < (nat_of i).+1)%N -> P j (f i s)) ->
  forall (i : ordT n) s, (nat_of i < n)%N -> P i (iteri_ord n f s).
Proof.
move=> Hind i s Hi.
set P' := fun j s => forall (i : ordT n), (nat_of i < j)%N -> P i s.
set io := _ _ _ _; suff: P' n io; [by move=> H; apply H, Hi|]; rewrite /io.
by have P0 : P' O s; [|move: P0; apply iteri_ord_ind].
Qed.

(* (* above lemma for P j s := forall i, nat_of i < j -> P i s *) *)
(* Lemma trec_ind' M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) : *)
(*   (forall i s, G 0%N i s = s) -> *)
(*   (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) -> *)
(*   (forall (i : ordT n) s, (nat_of i < n)%N -> *)
(*    (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) -> *)
(*    forall (j : ordT n), (nat_of j < (nat_of i).+1)%N -> P j (f i s)) -> *)
(*   forall (i : ordT n) s, (nat_of i < n)%N -> P i (G n I0 s). *)
(* Proof. *)
(* move=> HG0 HGS Hind i s Hi. *)
(* set P' := fun j s => forall (i : ordT n), (nat_of i < j)%N -> P i s. *)
(* suff: P' n (G n I0_class0 s); [by move=> H; eapply H, Hi|]. *)
(* have P0 : P' O s; [by []|move: (leq0n n) P0]. *)
(* replace (G _ _ _) with (G (n - nat_of I0)%N I0 s); [|by rewrite I0_prop]. *)
(* replace O with (nat_of I0); move=> HI0 HP0. *)
(* by apply (@trec_ind _ P' _ f). *)
(* Qed. *)

Lemma iteri_ord_ind'_case M P (f : ordT n -> M -> M) :
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ordT n), (nat_of j < nat_of i)%N -> P j (f i s)) ->
  (forall (i : ordT n) s, (nat_of i < n)%N ->
   (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) -> P i (f i s)) ->
  forall (i : ordT n) s, (nat_of i < n)%N -> P i (iteri_ord n f s).
Proof.
move=> H1 H2; apply iteri_ord_ind' with (f := f) => // i s Hi H j Hj.
case (ltnP (nat_of j) (nat_of i)) => Hji; [by apply H1|].
have H' : j = i.
{ apply (@nat_of_prop _ _ nat_of_class0) => //; apply anti_leq.
  rewrite Hji Bool.andb_true_r; apply Hj. }
rewrite -H'; apply H2; rewrite H' //.
Qed.

(* Lemma trec_ind'_case M P (G : nat -> ordT n -> M -> M) (f : ordT n -> M -> M) : *)
(*   (forall i s, G 0%N i s = s) -> *)
(*   (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) -> *)
(*   (forall (i : ordT n) s, (nat_of i < n)%N -> *)
(*    (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) -> *)
(*    forall (j : ordT n), (nat_of j < nat_of i)%N -> P j (f i s)) -> *)
(*   (forall (i : ordT n) s, (nat_of i < n)%N -> *)
(*    (forall (j : ordT n), (nat_of j < nat_of i)%N -> P j s) -> P i (f i s)) -> *)
(*   forall (i : ordT n) s, (nat_of i < n)%N -> P i (G n I0 s). *)
(* Proof. *)
(* move=> HG0 HGS H1 H2; apply trec_ind' with (f := f) => // i s Hi H j Hj. *)
(* case (ltnP (nat_of j) (nat_of i)) => Hji. *)
(* { by apply H1. } *)
(* have H' : j = i. *)
(* { apply (@nat_of_prop _ _ nat_of_class0) => //; apply anti_leq. *)
(*   rewrite Hji Bool.andb_true_r; apply Hj. } *)
(* rewrite -H'; apply H2; rewrite H' //. *)
(* Qed. *)

Context {ordT' : nat -> Type}.
Context `{!I0_class ordT' n, !succ0_class ordT' n, !nat_of_class ordT' n}.
Context `{!I0_correct ordT' n, !succ0_correct ordT' n}.

Lemma iteri_ord_rec_ind2 M M' P
      (f : ordT n -> M -> M) (f' : ordT' n -> M' -> M') :
  forall (j : nat), (j <= n)%N ->
  (forall (i : ordT n) (i' : ordT' n) s s',
    (nat_of i <= n)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall (i : ordT n) (i' : ordT' n) s s',
    (nat_of i <= j)%N -> nat_of i' = nat_of i ->
    P s s' ->
    P (iteri_ord_rec (j - nat_of i)%N i f s)
      (iteri_ord_rec (j - nat_of i')%N i' f' s').
Proof.
move=> j Hj Hind i i' s s' Hi Hi' H; rewrite Hi'.
move Hk: (j - nat_of i)%N => k.
elim: k i i' Hi Hi' Hk s s' H => // k IHk i i' Hi Hi' Hk s s' H /=.
case (ltnP (nat_of i) j); [move=> Hij|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply: IHk; first by rewrite succ0_prop.
  { rewrite !succ0_prop ?Hi' //. }
  { by rewrite succ0_prop // subnS Hk. }
  apply Hind; by [apply: leq_trans Hi Hj|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi'n : nat_of i = n'.
{ apply anti_leq; rewrite Hjn andbT.
  apply (@leq_trans j.-1); last by rewrite Hj'.
  by apply /leP /Nat.lt_le_pred /leP. }
have Hk' : k = 0%N.
{ by rewrite Hi'n Hj' subSnn in Hk; case: Hk. }
by rewrite Hk'; apply: Hind =>//; apply (leq_trans Hi).
Qed.

Lemma iteri_ord_ind2 M M' P (f : ordT n -> M -> M) (f' : ordT' n -> M' -> M') :
  forall (j : nat), (j <= n)%N ->
  (forall (i : ordT n) (i' : ordT' n) s s',
    (nat_of i <= n)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall s s', P s s' -> P (iteri_ord j f s) (iteri_ord j f' s').
Proof.
move=> j Hj Hind s s' HP; rewrite /iteri_ord.
replace j with (j - @nat_of ordT _ _ I0)%N at 1; [|by rewrite I0_prop subn0].
replace j with (j - nat_of I0)%N at 2; [|by rewrite I0_prop subn0].
by apply iteri_ord_rec_ind2 => //; rewrite I0_prop.
Qed.
  
(* Lemma trec_ind2 M M' P (G : nat -> ordT n -> M -> M) *)
(*   (G' : nat -> ordT' n -> M' -> M') *)
(*   (f : ordT n -> M -> M) *)
(*   (f' : ordT' n -> M' -> M') : *)
(*   forall (j : nat), (j <= n)%N -> *)
(*   (forall i s, G 0%N i s = s) -> *)
(*   (forall i s, G' 0%N i s = s) -> *)
(*   (forall k i s, G k.+1 i s = G k (succ0 i) (f i s)) -> *)
(*   (forall k i s, G' k.+1 i s = G' k (succ0 i) (f' i s)) -> *)
(*   (forall (i : ordT n) (i' : ordT' n) s s', *)
(*     (nat_of i <= n)%N -> *)
(*     nat_of i' = nat_of i -> *)
(*     P s s' -> P (f i s) (f' i' s')) -> *)
(*   forall (i : ordT n) (i' : ordT' n) s s', *)
(*     (nat_of i <= j)%N -> *)
(*     nat_of i' = nat_of i -> *)
(*     P s s' -> *)
(*     P (G (j - nat_of i)%N i s) (G' (j - nat_of i')%N i' s'). *)
(* Proof. *)
(* move=> j Hj HG0 HG'0 HGS HG'S Hind i i' s s' Hi Hi' H. *)
(* rewrite Hi'. *)
(* move Hk: (j - nat_of i)%N => k. *)
(* elim: k i i' Hi Hi' Hk s s' H => [|k IHk] i i' Hi Hi' Hk s s' H. *)
(*   by rewrite HG0 HG'0. *)
(* case (ltnP (nat_of i) j); last by rewrite /ssrnat.leq Hk. *)
(* move=> Hij. *)
(* rewrite HGS HG'S; case (ltnP (nat_of i) n') => Hjn. *)
(* { have Hsisn : ((nat_of i).+1 < n)%N. *)
(*   { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. } *)
(*     apply: IHk; first by rewrite succ0_prop. *)
(*     rewrite !succ0_prop ?Hi' //. *)
(*     by rewrite succ0_prop // subnS Hk. *)
(*     apply Hind; by [apply: leq_trans Hi Hj|]. } *)
(* have Hj' : j = n. *)
(* { by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). } *)
(* have Hi'n : nat_of i = n'. *)
(* { apply anti_leq; rewrite Hjn andbT. *)
(*   apply (@leq_trans j.-1); last by rewrite Hj'. *)
(*   by apply /leP /Nat.lt_le_pred /leP. *)
(* } *)
(* have Hk' : k = 0%N. *)
(* { by rewrite Hi'n Hj' subSnn in Hk; case: Hk. } *)
(* rewrite Hk' HG0 HG'0. *)
(* apply: Hind =>//. *)
(* exact: leq_trans Hi Hj. *)
(* Qed. *)

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
(* TODO: Global *) Instance ssr_nat_of : nat_of_class ordT n := @nat_of_ord n.

Definition ytilded5 : 'I_n -> T -> 'M[T]_(1, n) -> 'M[T]_(1, n) -> T -> T :=
  @ytilded3 T ordT mxT _ _ _.

Definition ytildes5 : 'I_n -> T -> 'M[T]_(1, n) -> T :=
  @ytildes3 T ordT mxT _ _ _.

Definition iteri_ord5 : forall T, nat -> ('I_n -> T -> T) -> T -> T :=
  @iteri_ord ordT _ _ _.

Definition inner_loop5 : 'I_n -> 'M[T]_n -> 'M[T]_n -> 'M[T]_n :=
  @inner_loop3 T ordT mxT _ _ _ _ _ _ _ _ _.

Definition outer_loop5 : 'M[T]_n -> 'M[T]_n -> 'M[T]_n :=
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
  c1 = c2 -> (forall i : 'I_k, a1 i = a2 i) ->
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

Lemma inner_loop_correct (A R : 'M_n) (j : 'I_n) :
  inner_loop_inv A R j 0 -> inner_loop_inv A (inner_loop5 j A R) j n.
Proof.
move=> H; cut (inner_loop_inv A (inner_loop5 j A R) j j).
{ by move=> {H} [Ho Hi]; split; [|move=> j' i' Hj' _ Hi'; apply Hi]. }
rewrite /inner_loop5 /inner_loop3 /nat_of /ssr_nat_of.
set f := fun _ _ => _.
set P := fun i s => inner_loop_inv A s j i; rewrite -/(P _ _).
apply iteri_ord_ind => //.
{ apply /ltnW /(ltn_ord j). }
move=> i R' _ [Ho Hi]; split; [split; [move=> j' i' Hj' Hi'|move=> j' Hj']|].
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
by apply (leq_ltn_trans Hii').
Qed.

Lemma outer_loop_correct (A R : 'M_n) : outer_loop_inv A (outer_loop5 A R) n.
Proof.
rewrite /outer_loop5 /outer_loop3.
set f := fun _ _ => _.
set P := fun i s => outer_loop_inv A s i; rewrite -/(P _ _).
apply iteri_ord_ind => // j R' _ H.
have Hin_0 : inner_loop_inv A R' j 0; [by []|].
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
  by apply sym_eq, outer_loop_correct; [apply ltn_ord|]. }
replace ((cholesky5 A) j j)
with (gen_ytildes3 (A j j)
                   [ffun k : 'I_j => (cholesky5 A) j (inord k)]).
{ by apply /gen_ytildes3_eq => // j'; rewrite !ffunE mxE. }
apply sym_eq, outer_loop_correct, ltn_ord.
Qed.

Definition ssr_all_diag : (T -> bool) -> 'M[T]_n -> bool :=
  @all_diag _ _ _ ssr_fun_of _ _ ssr_succ0.

Lemma all_diag_correct f (A : 'M[T]_n) :
  ssr_all_diag f A = true -> forall i, f (A i i) = true.
Proof.
move=> Had i; move: (ltn_ord i) Had; change (nat_of_ord i) with (nat_of i).
set P := fun i b => b = true -> f (A i i) = true.
rewrite -/(P i (ssr_all_diag f A)).
apply iteri_ord_ind'_case.
{ move=> j' s Hj' H j'' Hj''.
  by rewrite /P Bool.andb_true_iff => Hb; elim Hb => Hb' _; apply H. }
by move=> j' s Hj' H; rewrite /P Bool.andb_true_iff => Hb; elim Hb.
Qed.

Definition ssr_foldl_diag (T' : Type) : (T' -> T -> T') -> T' -> 'M[T]_n -> T' :=
  @foldl_diag _ _ _ ssr_fun_of _ _ ssr_succ0 T'.

Lemma foldl_diag_correct (T' : Type) (f : T' -> T -> T') (z : T') (A : 'M[T]_n) :
  forall (P : nat -> T' -> Type),
  (forall (i : 'I_n) z, P i z -> P i.+1 (f z (A i i))) ->
  P O z -> P n (ssr_foldl_diag f z A).
Proof.
move=> P Hind; rewrite /ssr_foldl_diag /foldl_diag.
apply iteri_ord_ind => // i s Hi HPi; apply Hind.
by move: HPi; rewrite /nat_of /ssr_nat_of.
Qed.

Definition ssr_map_diag : (T -> T) -> 'M[T]_n -> 'M[T]_n :=
  @map_diag _ _ _ ssr_fun_of _ _ _ ssr_succ0.

Lemma map_diag_correct_ndiag f (A : 'M[T]_n) :
  forall i j : 'I_n, (i < j)%N -> (map_diag f A) i j = A i j.
Proof.
move=> i j Hij; rewrite /map_diag /iteri_ord; set f' := fun _ _ => _.
suff H : forall k R i',
           (matrix.fun_of_matrix (@iteri_ord_rec _ _ ssr_succ0 _ k i' f' R) i j
            = R i j) => //; elim => // k IHk R i' /=.
rewrite IHk; case (ltnP i' j) => Hi'j; [by rewrite ssr_store3_gt2|].
by rewrite ssr_store3_lt1 //; apply (leq_trans Hij).
Qed.

Lemma map_diag_correct_diag f (A : 'M[T]_n) :
  forall i, (map_diag f A) i i = f (A i i).
Proof.
move=> i; rewrite /map_diag.
set f' := fun _ _ => _.
set P := fun i s => s i i = f (A i i); rewrite -/(P i _).
apply iteri_ord_ind'_case with (i0 := i) => //.
{ move=> j s Hj Hind j' Hj'.
  rewrite /P /f' ssr_store3_lt1 //; apply Hind => //; apply ltn_ord. }
{ move=> j s Hj Hind; rewrite /P /f' ssr_store3_eq //. }
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
Instance one_infnan : one (FI fs) := @FI1 fs.

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

Definition test_n n'' : bool :=
  (4 * (BigZ.of_Z (Z.of_nat n'') + 1) <? eps_inv)%bigZ.

Lemma test_n_correct : test_n n = true ->
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

(*
Attempt to provide an eqType structure for (FI fs)

Lemma feqP : Equality.axiom feq.
move=> a b; apply: (iffP idP); rewrite /feq.
(* TODO: missing lemma for non-finite elts ? *)
Admitted.

Canonical FI_fs_eqMixin := EqMixin feqP.
Canonical FI_fs_eqType := Eval hnf in EqType (FI fs) FI_fs_eqMixin.

Instance fheq : @heq nat (fun n1 n2 => 'M[FI fs]_(n1, n2)) :=
  fun n1 n2 => @eqtype.eq_op (matrix_eqType FI_fs_eqType n1 n2).
*)

Instance fheq : @heq nat (matrix (FI fs)) :=
  fun n1 n2 a b => [forall i, [forall j, fieq (a i j) (b i j)]].

Instance : transpose_class (matrix (FI fs)) := @matrix.trmx (FI fs).

Lemma is_sym_correct (A : 'M[FI fs]_n) :
  is_sym A = true -> cholesky.MF2R (MFI2F A^T) = cholesky.MF2R (MFI2F A).
Proof.
rewrite /is_sym /heq_op /fheq => H.
apply/matrixP => i j; rewrite !mxE.
move/forallP/(_ i)/forallP/(_ j) in H.
by rewrite mxE in H; apply fieq_spec.
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

(* Instance add_up_infnan : add (FI fs) := add_up. *)

Hypothesis add_up_spec : forall x y, finite (add_up x y) ->
  (FI2F x + FI2F y <= FI2F (add_up x y))%R.
Hypothesis add_up_spec_fl : forall x y, finite (add_up x y) -> finite x.
Hypothesis add_up_spec_fr : forall x y, finite (add_up x y) -> finite y.

Definition gen_tr_up (n : nat) (A : 'M[FI fs]_n.+1) : FI fs :=
  @tr_up _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0 add_up A.

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

Definition gen_float_of_nat_up : nat -> FI fs := float_of_nat_up add_up.

Lemma float_of_nat_up_correct k : finite (gen_float_of_nat_up k) ->
  INR k <= FI2F (gen_float_of_nat_up k).
Proof.
rewrite /float_of_nat_up.
elim: k => [|k IHk].
{ move=> _; rewrite FI2F0; apply Rle_refl. }
move=> Fa; move: (add_up_spec Fa); apply Rle_trans; rewrite S_INR.
apply Rplus_le_compat; [|by rewrite FI2F1; right]; apply IHk.
move: Fa => /=; apply add_up_spec_fl.
Qed.

(* multiplication with upward rounding *)
Variable mul_up : FI fs -> FI fs -> FI fs.

(* Instance mul_up_infnan : mul (FI fs) := mul_up. *)

Hypothesis mul_up_spec : forall x y, finite (mul_up x y) ->
  (FI2F x * FI2F y <= FI2F (mul_up x y))%R.
Hypothesis mul_up_spec_fl : forall x y, finite (mul_up x y) -> finite x.
Hypothesis mul_up_spec_fr : forall x y, finite (mul_up x y) -> finite y.

(* division with upward rounding *)
Variable div_up : FI fs -> FI fs -> FI fs.

(* Instance div_up_infnan : div (FI fs) := div_up. *)

Hypothesis div_up_spec : forall x y, finite (div_up x y) -> finite y ->
  (FI2F x / FI2F y <= FI2F (div_up x y))%R.
Hypothesis div_up_spec_fl : forall x y, finite (div_up x y) -> finite y ->
  finite x.

Variable feps : FI fs.

Hypothesis feps_spec : eps (fis fs) <= FI2F feps.

Variable feta : FI fs.

Hypothesis feta_spec : eta (fis fs) <= FI2F feta.

Definition gen_compute_c_aux (A : 'M[FI fs]_n) (maxdiag : FI fs) : FI fs := 
  @compute_c_aux _ _ _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0 add_up mul_up div_up
    feps feta A maxdiag.

Lemma compute_c_aux_correct (A : 'M[FI fs]_n) maxdiag :
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (finite (add_up
             (mul_up ((gen_float_of_nat_up (2 * n.+1)%N)) feps)
             (- (1)))%C) ->
  (FI2F (add_up
             (mul_up ((gen_float_of_nat_up (2 * n.+1)%N)) feps)
             (- (1)))%C < 0) ->
  (forall i, 0 <= FI2F (A i i)) ->
  (0 <= FI2F maxdiag) ->
  finite (gen_compute_c_aux A maxdiag) ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F maxdiag)
  <= FI2F (gen_compute_c_aux A maxdiag))%R.
Proof.
have Pnp2 := pos_INR (n.+1)%N.
have P2np2 := pos_INR (2 * n.+1)%N.
have Pe := eps_pos (fis fs).
move=> Heps Fnem1 Nnem1 Pdiag Pmaxdiag Fc.
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
    by rewrite FI2F1; right. }
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
    apply Rmult_le_compat; [lra|apply Rlt_le, eta_pos| |by []].
    replace 4 with (INR 4); [|by simpl; lra].
    apply float_of_nat_up_correct, (mul_up_spec_fl Frll). }
  apply float_of_nat_up_correct, (mul_up_spec_fr Frl). }
have Frr := mul_up_spec_fr Fr.
move: (add_up_spec Frr); apply Rle_trans, Rplus_le_compat_r.
have Frrl := add_up_spec_fl Frr.
by change 2 with (INR 2); rewrite -mult_INR; apply float_of_nat_up_correct.
Qed.

Definition gen_compute_c (A : 'M[FI fs]_n) :
  option (FI fs) := 
  @compute_c _ _ _ _ _ _ ssr_fun_of _ ssr_I0 ssr_succ0
    leq_infnan lt_infnan add_up mul_up div_up
    (@is_finite fs) feps feta A.

Lemma compute_c_correct (A : 'M[FI fs]_n) :
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (forall i, finite (A i i)) ->
  (forall i, (0 <= FI2F (A i i))%R) ->
  forall c : FI fs, gen_compute_c A = Some c ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F (gen_max_diag A))
   <= FI2F c)%R.
Proof.
move=> Heps Fdiag Pdiag c.
rewrite /gen_compute_c /compute_c.
set nem1 := add_up _ _.
case_eq (is_finite nem1 && (nem1 < 0)%C); [|by []].
rewrite Bool.andb_true_iff => H; elim H => Fnem1 Nnem1.
set c' := compute_c_aux _ _ _ _ _ _ _.
case_eq (is_finite c') => Hite'; [|by []]; move=> Hc'.
have Hc'' : c' = c by injection Hc'.
rewrite -Hc''; apply compute_c_aux_correct => //.
{ apply (Rlt_le_trans _ (FI2F 0%C)); [|by right; rewrite FI2F0].
  apply filt_spec => //; apply finite0. }
by apply max_diag_pos.
Qed.

Definition gen_sub_down : FI fs -> FI fs -> FI fs :=
  @sub_down _ opp_infnan add_up.

Lemma sub_down_correct x y : finite (gen_sub_down x y) ->
  FI2F (gen_sub_down x y) <= FI2F x - FI2F y.
Proof.
move=> Fxy; rewrite /gen_sub_down /sub_down.
rewrite (fiopp_spec Fxy) -Ropp_minus_distr; apply Ropp_le_contravar.
have Fxy' := fiopp_spec_f1 Fxy.
move: (add_up_spec Fxy'); apply Rle_trans, Rplus_le_compat_l.
by rewrite (fiopp_spec (add_up_spec_fr Fxy')); right.
Qed.

Definition gen_posdef_check (A : 'M[FI fs]_n) : bool :=
  @posdef_check _ _ _ _ _ _ div_infnan _
    ssr_fun_of ssr_row ssr_store3 ssr_dotmulB0 _
    ssr_I0 ssr_succ0 ssr_nat_of fheq (@matrix.trmx (FI fs)) _ _
    add_up mul_up div_up feps feta (@is_finite fs) test_n A.

Lemma posdef_check_f1_diag A : gen_posdef_check A = true ->
  forall i, finite (A i i).
Proof.
rewrite /gen_posdef_check /posdef_check !Bool.andb_true_iff.
do 3 elim; move=> _ _ _.
set cc := compute_c _ _ _ _ _ _ _; case_eq cc => // c' Hc'.
rewrite Bool.andb_true_iff; elim.
set At := map_diag _ _.
move=> HtfRt _.
have HfRt := all_diag_correct HtfRt.
have Hfat : forall i, finite (At i i).
{ move=> i; move: (gen_cholesky_spec_correct (cholesky5_correct At)).
  elim=> _ Hs; move: (Hs i); rewrite mxE /cholesky5 => {Hs} Hs.
  move: (HfRt i); rewrite Hs /ytildes_infnan => H.
  move: (fisqrt_spec_f1 H); apply stilde_infnan_fc. }
move=> i; move: (Hfat i); rewrite map_diag_correct_diag => HAt.
by apply fiopp_spec_f1, (@add_up_spec_fr c' _), fiopp_spec_f1.
Qed.

Lemma posdef_check_correct A : gen_posdef_check A = true ->
  real_matrix.posdef (cholesky.MF2R (MFI2F A)).
Proof.
move=> H; have Hfdiag := posdef_check_f1_diag H; move: H.
rewrite /gen_posdef_check /posdef_check !Bool.andb_true_iff.
do 3 elim; move=> Hn Hsym Htpdiag.
apply test_n_correct in Hn.
have Hn' : 2 * INR n.+1 * eps (fis fs) < 1.
{ move: (neps_pos (fis fs) n.+1); rewrite !Rmult_assoc; lra. }
have Hn'' : INR (2 * n.+1) * eps (fis fs) < 1 by rewrite mult_INR.
apply is_sym_correct in Hsym.
set cc := compute_c _ _ _ _ _ _ _; case_eq cc => // c' Hc'.
rewrite Bool.andb_true_iff; elim.
set At := map_diag _ _; set Rt := cholesky3 _.
move=> HtfRt HtpRt.
have Htpdiag' := all_diag_correct Htpdiag.
have Hpdiag : forall i, 0 <= FI2F (A i i).
{ move=> i; apply (Rle_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  by apply file_spec => //; [apply finite0|apply Htpdiag']. }
have HfRt := all_diag_correct HtfRt.
have HtpRt' := all_diag_correct HtpRt.
have HpRt : forall i, 0 < (MFI2F Rt) i i.
{ move=> i; apply (Rle_lt_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  by rewrite mxE; apply filt_spec => //; [apply finite0|apply HtpRt']. }
move {Htpdiag HtfRt HtpRt Htpdiag' HtpRt'}.
apply gen_corollary_2_4_with_c_upper_bound_infnan with
 (maxdiag := FI2F (gen_max_diag A)) (c := FI2F c') (At := At) => //.
{ by move=> i; rewrite mxE. }
{ by apply max_diag_correct. }
{ by apply compute_c_correct. }
have Hfat : forall i, finite (At i i).
{ move=> i; move: (gen_cholesky_spec_correct (cholesky5_correct At)).
  elim=> _ Hs; move: (Hs i); rewrite mxE /cholesky5 => {Hs} Hs.
  move: (HfRt i); rewrite /Rt Hs /ytildes_infnan => H.
  move: (fisqrt_spec_f1 H); apply stilde_infnan_fc. }
split; move=> i; [move=> j Hij|].
{ by apply map_diag_correct_ndiag. }
move: (Hfat i); rewrite !mxE /At map_diag_correct_diag; apply sub_down_correct.
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

Global Instance seq_dotmulB0 : dotmulB0_class T ordT mxT :=
  fun n k c a b => seq_stilde3 k c (head [::] a) (head [::] b).

Fixpoint seq_store3 T s k (v : T) :=
  match s, k with
    | [::], _ => [::]
    | _ :: t, O => v :: t
    | h :: t, S k => h :: seq_store3 t k v
  end.

Fixpoint store3 T m i j (v : T) :=
  match m, i with
    | [::], _ => [::]
    | h :: t, O => seq_store3 h j v :: t
    | h :: t, S i => h :: store3 t i j v
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

Instance : I0_correct ordT n.+1.
Proof. done. Qed.

Definition ytilded4 :=
  @ytilded3 T ordT mxT _ _ n.+1.

Definition ytildes4 :=
  @ytildes3 T ordT mxT _ _ n.+1.

Definition cholesky4 (M : seq (seq T)) : seq (seq T) :=
  @cholesky3 T ordT _ _ _ _ _ _ _ n.+1 _ _ _ M.

Definition iteri_ord4 : forall T, nat -> (ordT n -> T -> T) -> T -> T :=
  @iteri_ord ordT _ O S.

Definition outer_loop4 :=
  @outer_loop3 T _ _ _ _ _ _ _ _ n.+1 _ _ _.

Definition inner_loop4 :=
  @inner_loop3 T _ _ _ _ _ _ _ n.+1 _ _ _.

Lemma size_store3 :
  forall s i j x,
  seq.size (@store3 T s j i x) = seq.size s.
Proof.
move=> s i j x.
elim: s j => [|a s IHs] j; first by case: j.
case: j IHs => [|j] IHs //=.
by rewrite -(IHs j).
Qed.

Lemma size_inner_loop4 :
  forall A j R, (nat_of j <= n.+1)%N ->
  seq.size R = n.+1 -> seq.size (inner_loop4 j A R) = n.+1.
Proof.
move=> A j R Hj H0; rewrite /inner_loop4 /inner_loop3.
by apply iteri_ord_ind => // i0 s Hs /=; rewrite size_store3.
Qed.

Lemma size_outer_loop4 :
  forall A R, seq.size R = n.+1 -> seq.size (outer_loop4 A R) = n.+1.
Proof.
move=> A R HRs; rewrite /outer_loop4 /outer_loop3.
set P := fun (i : nat) (s : seq (seq T)) => seq.size s = n.+1.
rewrite -/(P n.+1 _).
apply iteri_ord_ind => // i s Hle Hs /=; rewrite /P size_store3.
by apply size_inner_loop4 => //; apply ltnW.
Qed.

Lemma size_cholesky4 M : seq.size M = n.+1 -> seq.size (cholesky4 M) = n.+1.
Proof. apply size_outer_loop4. Qed.

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

Lemma size_nth_inner_loop4 :
  forall A j k R, (nat_of j <= n.+1)%N ->
  seq.size (nth [::] R k) = n.+1 ->
  seq.size (nth [::] (inner_loop4 j A R) k) = n.+1.
Proof.
move=> A j k R Hj; rewrite /inner_loop4 /inner_loop3.
apply iteri_ord_ind => //.
by move=> i0 s Hle Hs; rewrite size_nth_store3.
Qed.

Lemma size_nth_outer_loop4 :
  forall A R (i : nat), (i < n.+1)%N ->
  seq.size (nth [::] R i) = n.+1 ->
  seq.size (nth [::] (outer_loop4 A R) i) = n.+1.
Proof.
move=> A R i Hi HRs; rewrite /outer_loop4 /outer_loop3.
set P := fun (i : nat) (s : seq (seq T)) => seq.size (nth [::] s i) = n.+1.
rewrite -/(P _ _).
apply iteri_ord_ind => // i0 s Hle Hs; rewrite /P size_nth_store3.
by apply size_nth_inner_loop4 => //; apply ltnW.
Qed.

Lemma size_nth_cholesky4 M :
  forall i : nat, (i < n.+1)%N ->
  seq.size (nth [::] M i) = n.+1 ->
  seq.size (nth [::] (cholesky4 M) i) = n.+1.
Proof. by move=> *; apply: size_nth_outer_loop4. Qed.

Context `{eq T}.

Instance eq_mxT : @heq nat mxT := fun _ _ => eq_seq (eq_seq H).
(*  @eq_seqmx T H (* buggy (it ignores H and uses eq_op) *) *)

Instance : transpose_class mxT := fun m n => @trseqmx T.

Context `{!leq T, !lt T}.

Variable eps_inv : BigZ.t_.

(* arithmetic operations with directed rounding *)
Variable add1 mul1 div1 : T -> T -> T.
Variable feps feta : T.

Variable is_finite : T -> bool.

Definition posdef_check4 (M : seq (seq T)) : bool :=
  @posdef_check T ordT _ _ _ _ _ _ _ _ _ _ n.+1 _ _ _ _ _ _ _
    add1 mul1 div1 feps feta is_finite (test_n eps_inv) M.

End inst_seq.

Section Rseqmx_aux.
(* Aim: refinement proofs using seqmatrix.v *)

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
Context `{!zero C, (* !one C, *) !add C, !opp C, (* !sub C, *) !mul C, !div C, !sqrt C}.
Context {n : nat}.

Instance : nat_of_class (fun _ => nat) n.+1 := id.

Instance : I0_class [eta ordinal] n.+1 := ssr_I0.
Instance : succ0_class [eta ordinal] n.+1 := ssr_succ0.
Instance : nat_of_class [eta ordinal] n.+1 := ssr_nat_of.

Instance : I0_correct [eta ordinal] n.+1.
Proof. done. Qed.

Instance : succ0_correct [eta ordinal] n.+1.
Proof.
move=> i; rewrite /nat_of /nat_of_class_instance_4 /ssr_nat_of => Hi.
by rewrite /succ0 /succ0_class_instance_1 /ssr_succ0 inordK.
Qed.

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

Lemma param_seq_store3 n' : param (RmxC ==> RordC ==> Logic.eq ==> RmxC)
  (fun M j v => @ssr_store3 C 1 n' M ord0 j v)
  (fun M j v =>
     match M with
     | [::] => [::]
     | l :: _ => [:: @seq_store3 C l j v] end).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => j j' param_j.
apply param_abstr => v v' pv; rewrite -(param_eq pv) => {v' pv}.
move: (@refines_row_size _ _ _ _ _ param_M); case_eq M' => // l l' Hl _.
apply /trivial_param /refines_seqmxP => //.
{ move=> i Hi.
  have Hi' : i = 0%N by move: Hi; case i.
  rewrite Hi' /= size_seq_store3.
  change l with (nth [::] (l :: l') 0); rewrite -Hl -Hi'.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite Hi' Hl. }
move=> i j''; rewrite (ord_1_0 i) => /= {i}.
move: n' j' M M' param_M j param_j l l' Hl j''.
elim=> [|n' Hn'] j' M M' param_M j param_j l l' Hl j''; [by case j''|].
rewrite /ssr_store3 mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hl /=.
case_eq l => [|x t] Hxt; [by rewrite /seq_store3 nth_nil|].
have St : seq.size t = n'.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (x :: t)); rewrite -Hxt.
  change l with (nth [::] (l :: l') (@ord0 n'.+1)); rewrite -Hl.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hl. }
have Hj' : (j' = j :> nat); [by move: param_j; rewrite paramE|rewrite Hj'].
case_eq (nat_of_ord j'') => /= [|j'''] Hj'''; [by case (nat_of_ord j)|].
case_eq (nat_of_ord j) => [|j''''] Hj''''.
{ by apply set_nth_default; rewrite -Hj''' -(leq_add2r 1) !addn1 St. }
set M'' := \row_j nth zero0 t j : 'rV_n'.
specialize (Hn' j'''' M'' [:: t]).
have Hlj''' : (j''' < n')%N by rewrite -Hj''' -(leq_add2r 1) !addn1.
have Hlj'''' : (j'''' < n')%N by rewrite -Hj'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((ssr_store3 M'' ord0 (Ordinal Hlj'''') v) ord0 (Ordinal Hlj''')).
{ replace j''' with (nat_of_ord (Ordinal Hlj''')) at 2.
  { apply Hn' with (l' := [::]) => //.
    { rewrite paramE; apply refines_seqmxP => //; [by case|move=> i0 j0].
      by rewrite /M'' mxE (ord_1_0 i0) /=; apply set_nth_default; rewrite St. }
    by rewrite paramE /Rord; move: Hlj''''; case j''''. }
  by move: Hlj'''; case j'''. }
rewrite /ssr_store3 /M'' !mxE /= -(addn1 j''') -(addn1 j'''') eqn_add2r.
by rewrite (@set_nth_default _ _ (M ord0 j'')) // St.
Qed.

Lemma param_store3_aux m n' : param (RmxC ==> RordC ==> RordC ==> Logic.eq ==> RmxC)
  (@ssr_store3 C m n') (@store3 C).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => i i' param_i.
apply param_abstr => j j' param_j.
apply param_abstr => v v' param_v; rewrite -(param_eq param_v).
apply /trivial_param /refines_seqmxP => //.
{ rewrite size_store3; move: param_M; apply refines_row_size. }
{ move=> i'' Hi''; rewrite size_nth_store3.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
move: m M M' param_M i i' param_i.
elim=> [|m Hm] M M' param_M i i' param_i; [by case|move=> i'' j''].
rewrite /ssr_store3 mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
case_eq M' => [|l t] Hlt; [by rewrite !nth_nil|].
have Sl : seq.size l = n'.
{ change l with (nth [::] (l :: t) 0); rewrite -Hlt.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hlt. }
have St : seq.size t = m.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (l :: t)); rewrite -Hlt.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
have Hi' : (i' = i :> nat); [by move: param_i; rewrite paramE|rewrite Hi'].
case_eq (nat_of_ord i'') => /= [|i'''] Hi'''.
{ case (nat_of_ord i) => /= [|_].
  { set M'' := \row_j M ord0 j.
    have param_M'' : param Rseqmx M'' [:: l].
    { rewrite paramE; apply /refines_seqmxP => //; [by case|].
      move=> i0 j0; rewrite (ord_1_0 i0) /= /M'' mxE.
      rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
      by apply set_nth_default; rewrite Sl. }
    have H0 := param_apply (param_seq_store3 n') param_M''.
    have HM'' := param_apply (param_apply H0 param_j) param_v.
    rewrite -(param_eq param_v) in HM'' => {H0}.
    replace (if _ then _ else _) with ((ssr_store3 M'' ord0 j v) ord0 j'').
    { change (seq_store3 l j' v) with (nth [::] [:: seq_store3 l j' v] 0).
      by rewrite (@refines_nth _ _ _ _ _ _ _ HM''). }
    rewrite /ssr_store3 /M'' !mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
    rewrite Hlt /=; case (_ == _)%B => //.
    by apply set_nth_default; rewrite Sl. }
  by apply set_nth_default; rewrite Sl. }
have Slt : forall i, (i < m)%N -> seq.size (nth [::] t i) = n'.
{ move=> i0 Hi0; change (nth _ _ _) with (nth [::] (l :: t) i0.+1).
  rewrite -Hlt (@refines_nth_col_size _ _ _ _ _ param_M) => //.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
case_eq (nat_of_ord i) => [|i''''] Hi''''.
{ by apply set_nth_default; rewrite Slt // -Hi'''; move: (ltn_ord i''). }
set M'' := \matrix_(i, j) M (lift ord0 (i : 'I_m)) j.
specialize (Hm M'' t).
have Hli''' : (i''' < m)%N by rewrite -Hi''' -(leq_add2r 1) !addn1.
have Hli'''' : (i'''' < m)%N by rewrite -Hi'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((ssr_store3 M'' (Ordinal Hli'''') j v) (Ordinal Hli''') j'').
{ replace i''' with (nat_of_ord (Ordinal Hli''')) at 2.
  { apply Hm.
    { rewrite paramE; apply refines_seqmxP => // i0 j0.
      rewrite /M'' mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt.
      by apply set_nth_default => /=; rewrite Slt. }
    by rewrite paramE; move: Hli''''; case. }
  by move: Hli'''; case. }
rewrite /ssr_store3 /M'' !mxE /= -(addn1 i''') -(addn1 i'''') eqn_add2r.
rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
by rewrite (@set_nth_default _ _ (M i'' j'')) // Slt.
Qed.

Global Instance param_store3 :
  param (RmxC ==> RordC ==> RordC ==> Logic.eq ==> RmxC)
    (@ssr_store3 C n.+1 n.+1) (@store3 C).
Proof. apply param_store3_aux. Qed.

Global Instance param_dotmulB0 :
  param (RordC ==> Logic.eq ==> RmxC ==> RmxC ==> Logic.eq)
  (@ssr_dotmulB0 _ _ _ _ n.+1) (@dotmulB0 C ordC _ _ n.+1).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
rewrite paramE /dotmulB0 /= /gen_stilde3 /seq_dotmulB0.
case: k param_k => [k Hk] param_k.
rewrite paramE /Rord /= in param_k.
rewrite -{k'}param_k.
have := @refines_row_size _ _ _ _ _ param_a.
case Ea' : a' => [//|a'0 a'1].
case: a'1 Ea' =>// Ea' _.
have := @refines_row_size _ _ _ _ _ param_b.
case Eb' : b' => [//|b'0 b'1].
case: b'1 Eb' =>// Eb' _.
rewrite [RHS]/=.
elim: n k Hk a b c a' b' c' param_c a'0 param_a Ea' b'0 param_b Eb' => [|n' IHn']
  k Hk a b c a' b' c' param_c a'0 param_a Ea' b'0 param_b Eb'.
  rewrite /gen_fsum_l2r_rec /=.
  case: k Hk; last done.
  move=> _ /=.
  exact: param_eq.
have := @refines_nth_col_size _ _ _ _ _ param_a 0.
rewrite refines_row_size Ea'.
move/(_ erefl).
case Ea'0 : a'0 => [//|a'00 a'01] Ha'0; simpl in Ha'0.
have := @refines_nth_col_size _ _ _ _ _ param_b 0.
rewrite refines_row_size Eb'.
move/(_ erefl).
case Eb'0 : b'0 => [//|b'00 b'01] Hb'0; simpl in Hb'0.
case: k Hk => [|k] Hk; first exact: param_eq.
simpl.
set cc := (c + _)%C.
have Hk1 : (k < n'.+1)%N by rewrite -ltnS.
rewrite <-(IHn' k Hk1 (\row_(i < n'.+1) a ord0 (lift ord0 i))
                      (\row_(i < n'.+1) b ord0 (lift ord0 i)) cc
                      [:: behead a'0] [:: behead b'0]).
- apply gen_fsum_l2r_rec_eq =>//.
  move=> i; rewrite !ffunE.
  repeat f_equal.
    rewrite mxE.
    f_equal.
    apply: ord_inj.
    rewrite inordK /=.
      congr bump.
      rewrite inordK //.
      apply: (leq_trans _ Hk1).
      apply/leqW.
      by apply: ltn_ord.
    rewrite ltnS.
    now_show (i < n'.+1)%N.
    apply: (leq_trans _ Hk1).
    apply/leqW.
    by apply: ltn_ord.
  rewrite mxE.
  f_equal.
  apply: ord_inj.
  rewrite inordK /=.
    congr bump.
    rewrite inordK //.
    apply: (leq_trans _ Hk1).
    apply/leqW.
    by apply: ltn_ord.
  rewrite ltnS.
  now_show (i < n'.+1)%N.
  apply: (leq_trans _ Hk1).
  apply/leqW.
  by apply: ltn_ord.
- rewrite paramE {}/cc.
  f_equal.
  exact: param_eq.
- rewrite !ffunE.
  f_equal.
  f_equal.
  by rewrite -(@refines_nth _ _ _ _ _ _ _ param_a) Ea' Ea'0 inordK.
  by rewrite -(@refines_nth _ _ _ _ _ _ _ param_b) Eb' Eb'0 inordK.
- rewrite paramE; apply/refines_seqmxP =>//.
  + move=> i Hi.
    rewrite ltnS leqn0 in Hi; move/eqP in Hi.
    rewrite Hi /=.
    rewrite size_behead.
    have->: a'0 = (nth [::] a' 0) by rewrite Ea'.
    by rewrite (@refines_nth_col_size _ _ _ _ _ param_a) // Ea'.
  + move=> i j; rewrite !mxE.
    rewrite (ord_1_0 i) /= nth_behead.
    rewrite -[in RHS](@refines_nth _ _ _ _ _ _ _ param_a).
    f_equal.
    by rewrite Ea' // Ea'0.
- by rewrite Ea'0.
- rewrite paramE; apply/refines_seqmxP =>//.
  + move=> i Hi.
    rewrite ltnS leqn0 in Hi; move/eqP in Hi.
    rewrite Hi /=.
    rewrite size_behead.
    have->: b'0 = (nth [::] b' 0) by rewrite Eb'.
    by rewrite (@refines_nth_col_size _ _ _ _ _ param_b) // Eb'.
  + move=> i j; rewrite !mxE.
    rewrite (ord_1_0 i) /= nth_behead.
    rewrite -[in RHS](@refines_nth _ _ _ _ _ _ _ param_b).
    f_equal.
    by rewrite Eb' // Eb'0.
- by rewrite Eb'0.
Qed.

Global Instance param_ytilded :
  param (RordC ==> Logic.eq ==> RmxC ==> RmxC ==> Logic.eq ==> Logic.eq)
  (ytilded5 (n' := n)) (ytilded4 (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
eapply param_abstr => bk bk' param_bk.
rewrite /ytilded5 /ytilded4 /ytilded3.
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
  param (RordC ==> Logic.eq ==> RmxC ==> Logic.eq)
  (ytildes5 (n' := n)) (ytildes4 (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
rewrite /ytildes5 /ytildes4 /ytildes3.
eapply param_apply; last by tc.
by rewrite paramE; move=> ? ? ->.
Qed.

Lemma param_iteri_ord :
  forall T T', forall RT : T -> T' -> Prop,
  param ((fun j j' => j = j' /\ (j <= n.+1)%N) ==> (RordC ==> RT ==> RT) ==> RT
  ==> RT)
  (@iteri_ord5 n T) (@iteri_ord4 n.+1 T').
Proof.
move=> T T' RT.
apply param_abstr => j j' param_j.
rewrite paramE in param_j; destruct param_j as (Hj', Hj); rewrite -Hj'.
apply param_abstr => f f' param_f.
apply param_abstr => x x'.
rewrite /iteri_ord5 /iteri_ord4.
eapply (iteri_ord_ind2 (M := T) (M' := T') (j := j)) => //.
move=> i i' s s' Hi Hi'.
apply param_apply.
have: param Rord i i'.
{ move: Hi'; rewrite paramE /Rord /nat_of /nat_of_class_instance_4 /ssr_nat_of.
  by instantiate (1 := id). }
by apply param_apply.
Unshelve. (* FIXME: this should be automatically discharged *)
by tc.
by tc.
Qed.

Lemma param_inner_loop :
  param (RordC ==> RmxC ==> RmxC ==> RmxC)
  (inner_loop5 (n' := n)) (inner_loop4 (n := n)).
Proof.
apply param_abstr => j j' param_j.
rewrite paramE /Rord in param_j; rewrite -param_j => {j' param_j}.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /inner_loop5 /inner_loop4 /inner_loop3.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ eapply param_apply; [by apply param_iteri_ord|].
  rewrite paramE; split; [by []|].
  rewrite /nat_of /ssr_nat_of; apply ltnW, ltn_ord. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ eapply param_apply; [|exact param_i].
  eapply param_apply.
  { by eapply param_apply; [apply param_store3|]. }
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
  param (RmxC ==> RmxC ==> RmxC)
  (outer_loop5 (n' := n)) (outer_loop4 (n := n)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /outer_loop5 /outer_loop4 /outer_loop3.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => j j' param_j.
apply param_abstr => s s' param_s.
have Hin : param Rseqmx (inner_loop5 j A s) (inner_loop4 (n := n) j' As s').
{ eapply param_apply; [|exact param_s].
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_inner_loop|exact param_j]. }
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_j]).
  by eapply param_apply; [apply param_store3|]. }
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
  param (RmxC ==> RmxC) (cholesky5 (n' := n)) (cholesky4 (n := n)).
Proof.
apply param_abstr => A As param_A.
rewrite /cholesky5 /cholesky4 /cholesky3.
do 2 (eapply param_apply; [|exact param_A]).
apply param_outer_loop.
Qed.

End data_refinement.

Section data_refinement'.

Variable fs : Float_infnan_spec.

Let C := FI fs.

Instance : add (FI fs) := @fiplus fs.
Instance : mul (FI fs) := @fimult fs.
Instance : sqrt (FI fs) := @fisqrt fs.
Instance : div (FI fs) := @fidiv fs.
Instance : opp (FI fs) := @fiopp fs.
Instance : zero (FI fs) := @FI0 fs.
Instance : one (FI fs) := @FI1 fs.

Context {n : nat}.

Instance : nat_of_class (fun _ => nat) n.+1 := id.

Instance : I0_class [eta ordinal] n.+1 := ssr_I0.
Instance : succ0_class [eta ordinal] n.+1 := ssr_succ0.
Instance : nat_of_class [eta ordinal] n.+1 := ssr_nat_of.

Instance : I0_correct [eta ordinal] n.+1.
Proof. done. Qed.

Instance : succ0_correct [eta ordinal] n.+1.
Proof.
move=> i; rewrite /nat_of /nat_of_class_instance_6 /ssr_nat_of => Hi.
by rewrite /succ0 /succ0_class_instance_1 /ssr_succ0 inordK.
Qed.

Variable eps_inv : BigZ.t_.

Variable add1 mul1 div1 : C -> C -> C.
Variable feps feta : C.

Definition posdef_check5 :=
  gen_posdef_check (n':=n) eps_inv add1 mul1 div1 feps feta.

Instance : eq C := @fieq fs.
Instance : leq C := @file fs.
Instance : lt C := @filt fs.

Lemma param_heq_op :
  param (Rseqmx ==> Rseqmx ==> Logic.eq)
  (@heq_op _ _ (@fheq fs) n.+1 n.+1)
  (@heq_op _ _ (@eq_mxT C eq_instance_0) n.+1 n.+1).
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
rewrite paramE /heq_op /fheq /eq_mxT /eq_seqmx.
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
    rewrite /s nth_zip /= in Ha; [|by rewrite SA1s SA2s].
    rewrite nth_zip /= in Ha; [|by rewrite SA1si SA2si].
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

Lemma param_is_sym :
  param (Rseqmx ==> Logic.eq)
  (@is_sym _ n.+1 (@fheq fs) (@trmx C))
  (@is_sym _ n.+1 (@eq_mxT C eq_instance_0) transpose_class_instance_1).
Proof.
apply param_abstr => A As param_A.
rewrite /is_sym.
eapply param_apply; [|exact param_A].
eapply param_apply; [apply param_heq_op|].
eapply param_apply; [apply Rseqmx_trseqmx|exact param_A].
Qed.

Lemma param_all_diag :
  param (Logic.eq ==> Rseqmx ==> Logic.eq)
  (@all_diag _ _ _ (@ssr_fun_of C) n.+1 (@ssr_I0 n) (@ssr_succ0 n))
  (@all_diag _ _ _
     (@fun_of_instance_0 C zero_instance_0) n.+1 (@I0_class_instance_0 n)
     (@succ0_class_instance_0 n)).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => A As param_A.
rewrite /all_diag.
eapply param_apply; [|apply param_eq_refl].
eapply param_apply.
{ rewrite -/iteri_ord4 -/iteri_ord5.
  by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => b b' param_b.
rewrite !paramE in param_b, param_f; rewrite param_b param_f paramE.
do 2 apply f_equal; apply paramP; do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_foldl_diag :
  param (Logic.eq ==> Logic.eq ==> Rseqmx ==> Logic.eq)
  (@foldl_diag _ _ _ (@ssr_fun_of (FI fs)) n.+1
     (@ssr_I0 n) (@ssr_succ0 n) (FI fs))
  (@foldl_diag _ _ _ (@fun_of_instance_0 (FI fs) (FI0 fs)) n.+1
     (@I0_class_instance_0 n) (@succ0_class_instance_0 n) (FI fs)).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => x x' param_x.
apply param_abstr => A As param_A.
rewrite /foldl_diag.
eapply param_apply; [|exact param_x].
eapply param_apply.
{ rewrite -/iteri_ord4 -/iteri_ord5.
  by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
rewrite !paramE in param_f, param_s; rewrite param_f param_s paramE.
apply f_equal, paramP; do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_max_diag :
  param (Rseqmx ==> Logic.eq)
  (@max_diag _ _ _ (FI0 fs) 
     (@ssr_fun_of (FI fs)) n.+1 (@ssr_I0 n) (@ssr_succ0 n) 
     (@leq_infnan fs))
  (@max_diag _ _ _  (FI0 fs)
     (@fun_of_instance_0 (FI fs) (FI0 fs)) n.+1 (@I0_class_instance_0 n)
     (@succ0_class_instance_0 n) leq_instance_0).
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
     (@ssr_fun_of (FI fs)) n.+1
     (@ssr_I0 n) (@ssr_succ0 n) add1 mul1 div1
     feps feta)
  (@compute_c_aux _ _ _ (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_instance_0 (FI fs) (FI0 fs)) n.+1
     (@I0_class_instance_0 n) (@succ0_class_instance_0 n) add1 mul1 div1
     feps feta).
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
     (zero_infnan fs) (one_infnan fs) (@opp_infnan fs)
     (@ssr_fun_of (FI fs)) n.+1 (@ssr_I0 n) 
     (@ssr_succ0 n) (@leq_infnan fs) (@lt_infnan fs) add1 mul1 div1
     (@is_finite fs) feps feta)
  (@compute_c C _ _
     zero_instance_0 one_instance_0 opp_instance_0
     (@fun_of_instance_0 C zero_instance_0) n.+1 (@I0_class_instance_0 n)
     (@succ0_class_instance_0 n) leq_instance_0 lt_instance_0 add1 mul1 div1
     (@is_finite fs) feps feta).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /compute_c /zero_infnan /one_infnan /opp_infnan /lt_infnan.
rewrite /zero_instance_0 /one_instance_0 /opp_instance_0 /lt_instance_0 /C.
case (_ && _) => //.
set cc := compute_c_aux _ _ _ _ _ A _.
set cc' := compute_c_aux _ _ _ _ _ As _.
have Hcccc' : cc = cc'; [rewrite /cc /cc'|by rewrite Hcccc'].
apply paramP; apply (param_apply (R:=Logic.eq)).
{ eapply param_apply; [apply param_compute_c_aux|exact param_A]. }
eapply param_apply; [apply param_max_diag|exact param_A].
Qed.

Lemma param_map_diag :
  param (Logic.eq ==> Rseqmx ==> Rseqmx)
  (@map_diag _ _ _
     (@ssr_fun_of (FI fs)) (@ssr_store3 (FI fs)) n.+1
     (@ssr_I0 n) (@ssr_succ0 n))
  (@map_diag _ _ _
     (@fun_of_instance_0 C zero_instance_0) (@store_class_instance_1 C) n.+1
     (@I0_class_instance_0 n) (@succ0_class_instance_0 n)).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => A As param_A.
rewrite /map_diag.
eapply param_apply; [|exact param_A].
eapply param_apply.
{ rewrite -/iteri_ord4 -/iteri_ord5.
  by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_i]).
  eapply param_apply; [apply param_store3|exact param_s]. }
rewrite paramE in param_f; rewrite param_f paramE; apply f_equal, paramP.
do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_posdef_check :
  param (Rseqmx ==> Logic.eq)
  (gen_posdef_check (n':=n) eps_inv add1 mul1 div1 feps feta)
  (posdef_check4 (n:=n) eps_inv add1 mul1 div1 feps feta (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /gen_posdef_check /posdef_check4 /posdef_check.
apply f_equal2; [apply f_equal2; [apply f_equal|]|].
{ by apply param_eq; eapply param_apply; [apply param_is_sym|exact param_A]. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set c := compute_c _ _ _ _ _ _ A.
set c' := compute_c _ _ _ _ _ _ As.
have Hcc' : c = c'; [|rewrite -Hcc'; case c => // {c c' Hcc'} c].
{ rewrite /c /c'; apply paramP.
  eapply param_apply; [apply param_compute_c|exact param_A]. }
set R := cholesky3 _; set Rs := cholesky3 _; apply paramP.
suff param_R : param Rseqmx R Rs; [|rewrite /R /Rs].
{ rewrite paramE; apply f_equal2; apply paramP.
  { eapply param_apply; [|exact param_R].
    eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
  rewrite /pos_diag; eapply param_apply; [|exact param_R].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set At := map_diag _ A; set Ats := map_diag _ As.
suff: param Rseqmx At Ats; [|rewrite /At /Ats].
{ rewrite -/cholesky4 -/cholesky5; apply param_apply, param_cholesky. }
eapply param_apply; [|exact param_A].
eapply param_apply; [apply param_map_diag|apply param_eq_refl].
Qed.

End data_refinement'.

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

Instance eq'' : eq T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xeq => true
    | _ => false
  end.

Instance leq'' : leq T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xlt => true
    | Interval_xreal.Xeq => true
    | _ => false
  end.

Instance lt'' : lt T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xlt => true
    | _ => false
  end.

Definition eps_inv := 9007199254740992%bigZ.  (* 2^53 *)

Definition add1 := F.add rnd_UP 53%bigZ.
Definition mul1 := F.mul rnd_UP 53%bigZ.
Definition div1 := F.div rnd_UP 53%bigZ.

Definition feps : T := Float 2%bigZ (-53)%bigZ.
Definition feta : T := Float 2%bigZ (-1075)%bigZ.

Definition is_finite : T -> bool := F.real.

Definition posdef_check4_coqinterval (M : seq (seq T)) : bool :=
  @posdef_check4 T _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv add1 mul1 div1 feps feta is_finite M.

Goal True. idtac "test_posdef_check_CoqInterval". done. Qed.
Time Eval vm_compute in posdef_check4_coqinterval m12.

Goal True. idtac "test_CoqInterval". done. Qed.
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.
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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

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
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

End test_CoqInterval_none.
