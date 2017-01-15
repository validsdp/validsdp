Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 x3 : R) :=
  (0 - x0) * (x2)^3 + 4 * x1 * (x2)^2 * x3 + 4 * x0 * x2 * (x3)^2
  + 2 * x1 * (x3)^3 + 4 * x0 * x2 + 4 * (x2)^2 - 10 * x1 * x3 - 10 * (x3)^2
  + 2.

Let b1 (x0 x1 x2 x3 : R) :=
  (x0 + 1/2) * (1/2 - x0).

Let b2 (x0 x1 x2 x3 : R) :=
  (x1 + 1/2) * (1/2 - x1).

Let b3 (x0 x1 x2 x3 : R) :=
  (x2 + 1/2) * (1/2 - x2).

Let b4 (x0 x1 x2 x3 : R) :=
  (x3 + 1/2) * (1/2 - x3).

Let lb := -3181/1000.

Let ub := 4486/1000.

Theorem p_ge_lb (x0 x1 x2 x3 : R) :
  b1 x0 x1 x2 x3 >= 0 ->
  b2 x0 x1 x2 x3 >= 0 ->
  b3 x0 x1 x2 x3 >= 0 ->
  b4 x0 x1 x2 x3 >= 0 ->
  lb <= p x0 x1 x2 x3.
Proof.
unfold b1, b2, b3, b4, p, lb.
validsdp.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 : R) :
  b1 x0 x1 x2 x3 >= 0 ->
  b2 x0 x1 x2 x3 >= 0 ->
  b3 x0 x1 x2 x3 >= 0 ->
  b4 x0 x1 x2 x3 >= 0 ->
  p x0 x1 x2 x3 <= ub.
Proof.
unfold b1, b2, b3, b4, p, ub.
validsdp.
Qed.
