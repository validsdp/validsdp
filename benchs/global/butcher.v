Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  x5 * (x1)^2 + x4 * (x2)^2 - x0 * (x3)^2 + (x3)^3 + (x3)^2 - 1/3 * x0
  + 4/3 * x3.

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 + 1/1) * (0/1 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 + 1/10) * (9/10 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 + 1/10) * (5/10 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 + 1/1) * (-1/10 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 + 1/10) * (-5/100 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 + 1/10) * (-3/100 - x5).

Let lb := -14394/10000.

Theorem p_ge_lb (x0 x1 x2 x3 x4 x5 : R) :
  b1 x0 x1 x2 x3 x4 x5 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 >= 0 ->
  lb <= p x0 x1 x2 x3 x4 x5.
Proof.
unfold b1, b2, b3, b4, b5, b6, p, lb.
validsdp.
Qed.
