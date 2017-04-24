Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.
Require Import Psatz.

Let p (x0 x1 x2 x3 x4 x5 : R) :=
  0
  - (x0 * x3 * (0 - x0 + x1 + x2 - x3 + x4 + x5)
     + x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5)
     + x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) - x1 * x2 * x3 - x0 * x2 * x4
     - x0 * x1 * x5 - x3 * x4 * x5).

Let p' (x0 x1 x2 x3 x4 x5 : R) :=
  -60
  + x0 * x3 * (0 - x0 + x1 + x2 - x3 + x4 + x5)
    + x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5)
    + x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) - x1 * x2 * x3 - x0 * x2 * x4
    - x0 * x1 * x5 - x3 * x4 * x5.

Let p'' (x0 x1 x2 x3 x4 x5 : R) :=
  (0 - x1) * x2 - x0 * x3 + x1 * x4 + x2 * x5 - x4 * x5
  + x0 * (0 - x0 + x1 + x2 - x3 + x4 + x5).

Let b1 (x0 x1 x2 x3 x4 x5 : R) :=
  (x0 - 606887582536/100000000000) * (702674064/100000000 - x0).

Let b2 (x0 x1 x2 x3 x4 x5 : R) :=
  (x1 - 4) * (8 - x1).

Let b3 (x0 x1 x2 x3 x4 x5 : R) :=
  (x2 - 4) * (8 - x2).

Let b4 (x0 x1 x2 x3 x4 x5 : R) :=
  (x3 - 4) * (702674064/100000000 - x3).

Let b5 (x0 x1 x2 x3 x4 x5 : R) :=
  (x4 - 4) * (8 - x4).

Let b6 (x0 x1 x2 x3 x4 x5 : R) :=
  (x5 - 4) * (8 - x5).

Theorem alternative (x0 x1 x2 x3 x4 x5 : R) :
  b1 x0 x1 x2 x3 x4 x5 >= 0 ->
  b2 x0 x1 x2 x3 x4 x5 >= 0 ->
  b3 x0 x1 x2 x3 x4 x5 >= 0 ->
  b4 x0 x1 x2 x3 x4 x5 >= 0 ->
  b5 x0 x1 x2 x3 x4 x5 >= 0 ->
  b6 x0 x1 x2 x3 x4 x5 >= 0 ->
  (p x0 x1 x2 x3 x4 x5 > 0
   \/ p' x0 x1 x2 x3 x4 x5 > 0
   \/ p'' x0 x1 x2 x3 x4 x5 > 0).
Proof.
intros H1 H2 H3 H4 H5 H6.
case (Rlt_or_le 0 (p x0 x1 x2 x3 x4 x5)) => Hp; [now left|right].
case (Rlt_or_le 0 (p' x0 x1 x2 x3 x4 x5)) => Hp'; [now left|right].
revert H1 H2 H3 H4 H5 H6 Hp Hp'.
unfold b1, b2, b3, b4, b5, b6, p, p', p''.
validsdp.
Qed.
