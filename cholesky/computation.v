(** * Bounds on the rounding error of dotproduct $c - \sum_{i=0}^k a_i b_i$#c - \sum_{i=0}^k a_i b_i#

    Notations are similar to the one in [fsum]. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg bigop.

Require Import binary64_infnan.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.
Require Import binary64_infnan.

Require Import ZArith.
Require Import Fcore Fappli_IEEE Fappli_IEEE_bits.

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

Require Import Fcalc_ops.

Definition half := b64_normalize (Float radix2 1 (-1)).
Definition one := b64_plus mode_NE half half.
Time Eval vm_compute in B2F one.

Time Eval vm_compute in B2F (fisqrt (Z2B 4)).

Time Eval vm_compute in is_finite _ _ (b64_normalize (Float radix2 1 4096)).

Time Eval vm_compute in is_nan _ _ (fisqrt (b64_normalize (Float radix2 (-1) 0))).

Definition F64 := binary64_infnan.

Require Import matrix seqmatrix refinements.

Section GenericFcmdotprod.

Local Open Scope ring_scope.

Import Refinements.Op.

Class hmulvB {I} B T := hmulvB_op : forall n : I, T -> B n -> B n -> T.
(* Local Notation "*v%HC" := hmulv_op.
Reserved Notation "A *v B" (at level 40, left associativity, format "A  *v  B").
Local Notation "x *v y" := (hmulv_op x y) : hetero_computable_scope. *)

Open Scope computable_scope.
Open Scope hetero_computable_scope.

Variable T : Type.
Variable mxA : nat -> nat -> Type.

Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hcast mxA}.
(* Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}. *)
Context `{!hmulvB (mxA 1) T, !scalar_mx_class T mxA}.

(* Check forall n c (a b : mxA n 1), hmulvB_op c a b = c - \sum_i (a i * b i). *)

(*
(** Sum [c + \sum a_i] computed in float from left to right. *)
Fixpoint fsum_l2r_rec n (c : F fs) : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (fplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i] computed in float from left to right. *)
Definition fsum_l2r n : F fs ^ n -> F fs :=
  match n with
    | 0%N => fun _ => F0 fs
    | n'.+1 =>
      fun a => fsum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.
*)

Definition gfcmdotprod_l2r n (c : T) (a b : mxA 1 n) : T :=
  hmulvB_op c a b.


End GenericFcmdotprod.

Section GenericHmulvb.

Import Refinements.Op.
Open Scope computable_scope.
Open Scope hetero_computable_scope.

Variable T : Type.
Variable mxA : nat -> nat -> Type.

Context `{!add T, !opp T, !mul T}.
(* Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hopp mxA}. *)

Compute hmulvB (mxA 1) T.
(*
Fixpoint hmulvB n c {struct n} :=
  match n return (mxA 1 n) -> (mxA 1 n) -> T with
    | 0%N => fun _ _ => c
    | n'.+1 => fun a b => hmulvB n' (c - (a ord0 * b ord0))%C (fun i => a (lift ord0 i)) (fun i => b (lift ord0 i))
  end.
*)

End GenericHmulvb.
