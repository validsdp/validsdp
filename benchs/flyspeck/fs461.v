Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  x0 * x3 * (0 - x0 + x1 + x2 - x3 + x4 + x5)
  + x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5)
  + x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) - x1 * x2 * x3 - x0 * x2 * x4
  - x0 * x1 * x5 - x3 * x4 * x5.

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 - 606887582536 / 100000000000) * (702674064 / 100000000 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 - 4/1) * (8/1 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 - 4/1) * (8/1 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 - 4/1) * (8/1 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 - 4/1) * (8/1 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 - 4/1) * (8/1 - x5).

Theorem p_nonneg (x0 x1 x2 x3 x4 x5 : R) :
  b1 x0 x1 x2 x3 x4 x5 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 >= 0 ->
  p x0 x1 x2 x3 x4 x5 >= 0.
Proof.
unfold b1, b2, b3, b4, b5, b6, p.
validsdp.
Qed.
