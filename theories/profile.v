Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Require Import CBigZ.
(* Print Module F. *)
Local Open Scope bigZ_scope.

Require Import mathcomp.algebra.matrix.
Require Import CoqEAL_refinements.seqmatrix.
Require Import CoqEAL_refinements.refinements.

Require Import CoqEAL_theory.hrel.

Import Refinements.Op.

Require Import computation testsuite.

(* Profile each floating-point arithmetic operation. *)

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
Instance : Refinements.Op.one T := Float 1%bigZ 0%bigZ.

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