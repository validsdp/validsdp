Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

Let p (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (0 - x0) * (x5)^3 + 3 * x0 * x5 * (x6)^2 - x2 * (x6)^3
  + 3 * x2 * x6 * (x5)^2 - x1 * (x4)^3 + 3 * x1 * x4 * (x7)^2 - x3 * (x7)^3
  + 3 * x3 * x7 * (x4)^2 - 9563453/10000000.

Let b1 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x0 + 1/10) * (4/10 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x1 - 4/10) * (1/1 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x2 + 7/10) * (-4/10 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x3 + 7/10) * (4/10 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x4 - 1/10) * (2/10 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x5 + 1/10) * (2/10 - x5).

Let b7 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x6 + 3/10) * (11/10 - x6).

Let b8 (x0 x1 x2 x3 x4 x5 x6 x7 : R) :=
  (x7 + 11/10) * (-3/10 - x7).

Let lb := -1744/1000.

Let ub := 1369/1000.

Theorem p_ge_lb (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  b1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  lb <= p x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
unfold b1, b2, b3, b4, b5, b6, b7, b8, p, lb.
validsdp.
Qed.

Theorem p_le_ub (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
  b1 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b7 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  b8 x0 x1 x2 x3 x4 x5 x6 x7 >= 0 ->
  p x0 x1 x2 x3 x4 x5 x6 x7 <= ub.
Proof.
unfold b1, b2, b3, b4, b5, b6, b7, b8, p, ub.
validsdp.
Qed.
