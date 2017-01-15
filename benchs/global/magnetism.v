Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x0)^2 + 2 * (x1)^2 + 2 * (x2)^2 + 2 * (x3)^2 + 2 * (x4)^2 + 2 * (x5)^2
  + 2 * (x6)^2 - x0.

Let b1 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x0 + 1) * (1 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x1 + 1) * (1 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x2 + 1) * (1 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x3 + 1) * (1 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x4 + 1) * (1 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x5 + 1) * (1 - x5).

Let b7 (x0 x1 x2 x3 x4 x5 x6 : R) :=
  (x6 + 1) * (1 - x6).

Let lb := -2501/10000.

Let ub := 140001/10000.

Theorem p_ge_lb (x0 x1 x2 x3 x4 x5 x6 : R) :
  b1 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b7 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  lb <= p x0 x1 x2 x3 x4 x5 x6.
Proof.
unfold b1, b2, b3, b4, b5, b6, b7, p, lb.
validsdp.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 x4 x5 x6 : R) :
  b1 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  b7 x0 x1 x2 x3 x4 x5 x6 >= 0 ->
  p x0 x1 x2 x3 x4 x5 x6 <= ub.
Proof.
unfold b1, b2, b3, b4, b5, b6, b7, p, ub.
validsdp.
Qed.
