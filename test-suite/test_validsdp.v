Require Import Reals.
From ValidSDP Require Import validsdp.
Local Open Scope R_scope.

Test Default Proof Mode.
Require Import Ltac2.Ltac2. (* TODO: this will later be unnecessary *)
Test Default Proof Mode.
(* Set Default Proof Mode "Ltac2". (implied) *)

(* To enable debug mode: *)
(* Ltac2 Set deb := fun str => Message.print str. *)

Section Tests.

Let test1 x y : 0 < x -> 1 <= y -> x + y >= 0.
Proof.
Time validsdp.
Qed.

Let test2 x y : 2 / 3 * x ^ 2 + y ^ 2 >= 0.
Proof.
Time validsdp.
Qed.

Let test3 x y : 2 / 3 * x ^ 2 + y ^ 2 + 1 > 0.
Proof.
Time validsdp.
Qed.

Let p x y := 2 / 3 * x ^ 2 + y ^ 2.

Let test4 x y : p x y + 1 > 0.
Proof.
Time validsdp.
Qed.

Let test6 x : x >= 10 -> x <= 12 -> 0 <= 2 + x ^ 2.
Proof.
validsdp.
Qed.

End Tests.
