Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 : R) :=
  -x0 + 2/1 * x1 - x2 - 417817267/500000000 * x1 * (1 + x1).

Let b1 (x0 x1 x2 : R) :=
  (x0 + 5/1) * (5/1 - x0).

Let b2 (x0 x1 x2 : R) :=
  (x1 + 5/1) * (5/1 - x1).

Let b3 (x0 x1 x2 : R) :=
  (x2 + 5/1) * (5/1 - x2).

Let lb := -36713/1000.

Let ub := 10439/1000.

Theorem p_ge_lb (x0 x1 x2 : R) :
  b1 x0 x1 x2 >= 0 ->
  b2 x0 x1 x2 >= 0 ->
  b3 x0 x1 x2 >= 0 ->
  lb <= p x0 x1 x2.
Proof.
unfold b1, b2, b3, p, lb.
validsdp.
Qed.

Theorem p_le_ub (x0 x1 x2 : R) :
  b1 x0 x1 x2 >= 0 ->
  b2 x0 x1 x2 >= 0 ->
  b3 x0 x1 x2 >= 0 ->
  p x0 x1 x2 <= ub.
Proof.
unfold b1, b2, b3, p, ub.
validsdp.
Qed.
