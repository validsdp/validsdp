Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 : R) :=
  (x0 - x1)^2 + (x1 - 1)^2 + (x0 - (x2)^2)^2 + (x2 - 1)^2.

Let b1 (x0 x1 x2 : R) :=
  (x0 + 10) * (10 - x0).

Let b2 (x0 x1 x2 : R) :=
  (x1 + 10) * (10 - x1).

Let b3 (x0 x1 x2 : R) :=
  (x2 + 10) * (10 - x2).

Let lb := -1/10000.

Theorem p_ge_lb (x0 x1 x2 : R) :
  b1 x0 x1 x2 >= 0 ->
  b2 x0 x1 x2 >= 0 ->
  b3 x0 x1 x2 >= 0 ->
  lb <= p x0 x1 x2.
Proof.
unfold b1, b2, b3, p, lb.
validsdp.
Qed.
