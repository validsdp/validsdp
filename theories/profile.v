Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
From Bignums Require Import BigZ.
(* Print Module F. *)
Local Open Scope bigZ_scope.

Require Import mathcomp.algebra.matrix.
Require Import CoqEAL.refinements.seqmx.
Require Import CoqEAL.refinements.refinements.
Require Import CoqEAL.refinements.hrel.
Require Import CoqEAL.refinements.seqmx_complements.

Import Refinements.Op.

Require Import cholesky_prog iteri_ord posdef_check.

Require Import matrices.

(* Profile each floating-point arithmetic operation. *)

Lemma blackhole A (t : A) : unit.
exact tt.
Qed.
Notation "§" := (@blackhole _ _).

Fixpoint fib (n : nat) :=
  match n with
    O => 1%nat
  | S O => 1%nat
  | S ((S p) as q) => (fib p + fib q)%nat
  end.

Require Import Float.

Definition select_intvl (a b : F.type) := a.
Definition select_float (a b : float) := a.

Notation doubling1 f := (let r1 := (f) in
                        let r2 := (f) in
                        select_intvl r1 r2) (only parsing).
Notation doubling2 f := (let r1 := (f) in
                        let r2 := (f) in
                        select_float r1 r2) (only parsing).

Notation no_doubling1 f := (f) (only parsing).
Notation no_doubling2 f := (f) (only parsing).

Section test_CoqInterval.
Local Notation T := F.type (only parsing).

Definition two := Eval compute in
      let one := Float 1%bigZ 0%bigZ in
      F.add rnd_NE 53%bigZ one one.

Instance : add_of T := fun a b => no_doubling1 (F.add rnd_NE 53%bigZ a b).
Instance : mul_of T := fun a b => no_doubling1 (F.mul rnd_NE 53%bigZ a b).
Instance : sqrt_of T := fun a => no_doubling1 (F.sqrt rnd_NE 53%bigZ a).
Instance : div_of T := fun a b => no_doubling1 (F.div rnd_NE 53%bigZ a b).
Instance : opp_of T := fun a => no_doubling1 (F.neg a).
Instance : zero_of T := F.zero.
Instance : one_of T := Float 1%bigZ 0%bigZ.

Time Eval vm_compute in blackhole _ (cholesky_seqmx (n := seq.size matrix) matrix).

(* 9.397 = *)
(* 13.81 mul *)
(* 12.168 add *)
(* 9.711 opp *)
(* 9.589 div *)
(* 9.373 sqrt *)

(*old:*)
(* Finished transaction in 8.933 secs (8.92u,0.008s) (successful) with no doubling *)
(* Finished transaction in 15.454 secs (15.444u,0.008s) (successful) *)
(* Finished transaction in 18.175 secs (18.172u,0.004s) (successful) *)
End test_CoqInterval.

Section test_Prim.
Local Notation T := float (only parsing).

Instance : add_of T := fun a b => no_doubling2 (add a b).
Instance : mul_of T := fun a b => no_doubling2 (mul a b).
Instance : sqrt_of T := fun a => doubling2 (sqrt a).
Instance : div_of T := fun a b => no_doubling2 (div a b).
Instance : opp_of T := fun a => no_doubling2 (opp a).
Instance : zero_of T := zero.
Instance : one_of T := one.

Definition matrix_float := Eval compute in map (map BigZFloat2Prim) matrix.

Time Eval vm_compute in blackhole _ (cholesky_seqmx (n := seq.size matrix_float) matrix_float).

(* 0.523 = *)
(* 0.566 add *)
(* 0.533 mul *)

(*old:*)
(* Finished transaction in 0.524 secs (0.524u,0.s) (successful) *)
(* Finished transaction in 0.556 secs (0.555u,0.s) (successful) *)
End test_Prim.
