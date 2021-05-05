Require Import Reals.
From ValidSDP Require Import validsdp posdef_check.
Require matrices.
Local Open Scope R_scope.

Test Default Proof Mode.
Require Import Ltac2.Ltac2. (* TODO: this will later be unnecessary *)
Test Default Proof Mode.
(* Set Default Proof Mode "Ltac2". (implied) *)

(* To enable debug mode: *)
(* Ltac2 Set deb := fun str => Message.print str. *)

Lemma test_using_star (x : R) (H : - 10 <= x) (H0 : x <= 10) : True.
Proof.
intros.
validsdp_intro (1 + x ^ 2) using * as ?.
now split.
Qed.

Lemma test_wholeR_lower (x : R) : True.
Proof.
intros.
validsdp_intro (1 + x ^ 2) lower as H.
now split.
Qed.

Lemma test_double_ineq x : 10 <= x <= 12 -> True.
Proof.
intros hyp.
Fail validsdp_intro (11 - x) using * as H.
(* TODO Add support for "<= /\ <=" in "using *" *)
(* TODO Enhance exception support / Match_failure *)
validsdp_intro (11 - x) using hyp as H.
validsdp_intro (2 + x ^ 2) lower using hyp as HA.
now split.
Qed.
