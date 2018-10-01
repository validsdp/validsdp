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

Section test_CoqInterval_add.
Local Notation T := F.type.

Definition two := Eval compute in
      let one := Float 1%bigZ 0%bigZ in
      F.add rnd_NE 53%bigZ one one.
Instance : add_of T := (* fun a b =>
  let r1 := F.add rnd_NE 53%bigZ a b in
  F.div rnd_NE 53%bigZ (F.add rnd_NE 53%bigZ r1 r1) two *)
F.add rnd_NE 53%bigZ.
(* Instance : add_of T :=F.add rnd_NE 53%bigZ. *)
Instance : mul_of T := F.mul rnd_NE 53%bigZ.
Fixpoint fib (n : nat) :=
  match n with
    O => 1%nat
  | S O => 1%nat
  | S ((S p) as q) => (fib p + fib q)%nat
  end.
Instance : sqrt_of T :=
  let a := F.sqrt rnd_NE 53%bigZ in
  a.
Instance : div_of T := F.div rnd_NE 53%bigZ.
Instance : opp_of T := F.neg.
Instance : zero_of T := F.zero.
Instance : one_of T := Float 1%bigZ 0%bigZ.

Time Eval vm_compute in blackhole _ (cholesky_seqmx (n := seq.size matrix) matrix).
(* Finished transaction in 8.933 secs (8.92u,0.008s) (successful) with no doubling *)
(* Finished transaction in 15.454 secs (15.444u,0.008s) (successful) *)
(* Finished transaction in 18.175 secs (18.172u,0.004s) (successful) *)
End test_CoqInterval_add.

Require Import Float.
Section test_prim_add.
Local Notation T := float (only parsing).
Instance : add_of T := fun a b => (* fun a b =>
                         let r1 := add a b in
                         let r2 := add b a in
                       ((r1 + r2) / two)%float *)
                         let r := add a b in r.
Instance : mul_of T := mul.
Instance : sqrt_of T := sqrt.
Instance : div_of T := div.
Instance : opp_of T := opp.
Instance : zero_of T := zero.
Instance : one_of T := one.
Definition matrix_float := Eval compute in map (map BigZFloat2Prim) matrix.
Time Eval vm_compute in blackhole _ (cholesky_seqmx (n := seq.size matrix_float) matrix_float).
(* Finished transaction in 0.524 secs (0.524u,0.s) (successful) *)
(* Finished transaction in 0.556 secs (0.555u,0.s) (successful) *)
End test_prim_add.

Set Printing All.
Print t.
About sqrt_of_instance_0.
Goal True. idtac "test_CoqInterval_add". done. Qed.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

Goal True. idtac "test_CoqInterval_none". done. Qed.
Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.

End test_CoqInterval_none.