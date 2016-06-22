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
Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Require Import BigZ.
(* Print Module F. *)
Local Open Scope bigZ_scope.
Require Import mathcomp.algebra.matrix.
Require Import CoqEAL_refinements.seqmatrix.
Require Import CoqEAL_refinements.refinements.

Import Refinements.Op.

Require Import iteri_ord.
Require Import cholesky_prog.
Require Import BigQ.
Require Import Interval.Interval_xreal.

Require Import cholesky_prog.

Notation toR := (fun f => proj_val (F.toX f)).

Section test_CoqInterval.

Definition prec := 53%bigZ.

Local Notation T := (s_float BigZ.t_ BigZ.t_).

Instance add'' : add T := F.add rnd_NE prec.
Instance mul'' : mul T := F.mul rnd_NE prec.
Instance sqrt'' : sqrt T := F.sqrt rnd_NE prec.
Instance div'' : div T := F.div rnd_NE prec.
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

Instance add1 : addup_class T := F.add rnd_UP prec.
Instance mul1 : mulup_class T := F.mul rnd_UP prec.
Instance div1 : divup_class T := F.div rnd_UP prec.

Definition feps : T := Float 1%bigZ (-53)%bigZ.
Definition feta : T := Float 1%bigZ (-1075)%bigZ.

Definition is_finite : T -> bool := F.real.

Instance float_of_nat_up'' : nat2Fup_class T :=
  fun n => iter n (fun x => add1 x one'') zero''.

Definition test_n'' : nat -> bool :=
  fun n => lt'' (mul1 (mul1 (float_of_nat_up'' 4%N)
                            (float_of_nat_up'' n.+1)) feps) one''.

Instance sub1 : subdn_class T := fun x y => opp'' (add1 y (opp'' x)).

Definition posdef_check4_coqinterval (M : seq (seq T)) : bool :=
  posdef_check_seqmx (T := T) (n := (seq.size M).-1)
    feps feta is_finite M.

Definition posdef_check_itv4_coqinterval (M : seq (seq T)) (r : T) : bool :=
  posdef_check_itv_seqmx (T := T) (n := (seq.size M).-1)
    feps feta is_finite M r.

End test_CoqInterval.

Require Import testsuite.

Goal True. idtac "test_posdef_check_CoqInterval". done. Qed.
Time Eval vm_compute in posdef_check4_coqinterval m12.
(* 6.3 s on Erik's laptop *)

Time Eval vm_compute in posdef_check_F4_coqinterval' m12.
(* 7.1 s on Erik's laptop *)
