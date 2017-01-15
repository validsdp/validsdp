Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(0.9, 1.1);
x2 = rand(0, 0.2);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x1^2 + x2^2 <= 1) {
    x1 = pre_x1^2 + pre_x2^3;
    x2 = pre_x1^3 + pre_x2^2;
  } else {
    x1 = 0.5 * pre_x1^3 + 0.4 * pre_x2^2;
    x2 = -0.6 * pre_x1^2 + 0.3 * pre_x2^2;
  }
}
 *)

(* initial condition 0.9 <= x1 <= 1.1 encoded as (x1 - 0.9)*(1.1 - x1) (>= 0) *)
Let pI1 (x0 x1 : R) := (x0 - 9 / 10) * (11 / 10 - x0).
(* initial condition 0 <= x2 <= 0.2 *)
Let pI2 (x0 x1 : R) := x1 * (2 / 10 - x1).
(* guard x1^2 + x2^2 <= 1 (then branch) *)
Let g0 x0 x1 := 1 - (x0^2 + x1^2).
(* assignment in then branch *)
Let t0_x0 (x0 x1 : R) := x0^2 + x1^3.
Let t0_x1 (x0 x1 : R) := x0^3 + x1^2.
(* guard x1^2 + x2^2 >= 1 (else branch) *)
Let g1 x0 x1 := (x0^2 + x1^2) - 1.
(* assignment in else branch *)
Let t1_x0 (x0 x1 : R) := 5 / 10 * x0^3 + 4 / 10 * x1^2.
Let t1_x1 (x0 x1 : R) := (-6) / 10 * x0^2 + 3 / 10 * x1^2.

Let p x0 x1 :=
  45341764775/2199023255552 + 2543726999988995/576460752303423488 * x0
  + -1432997702740123/4611686018427387904 * x1
  + -6302578343467645/288230376151711744 * x0^2
  + 6245114857897609/1152921504606846976 * x0 * x1
  + -5391003868387453/576460752303423488 * x1^2
  + 6367724791712061/576460752303423488 * x0^3
  + -3595005646773247/288230376151711744 * x0^2 * x1
  + 3726914850232837/288230376151711744 * x0 * x1^2
  + 7525758218067537/288230376151711744 * x1^3
  + -5053053318909601/576460752303423488 * x0^4
  + -8679218943287311/9223372036854775808 * x0^3 * x1
  + 979459393320495/36028797018963968 * x0^2 * x1^2
  + 2667063388576173/1152921504606846976 * x0 * x1^3
  + -1416111155701539/36028797018963968 * x1^4.
  
Theorem init (x0 x1 : R) :
  pI1 x0 x1 >= 0 -> pI2 x0 x1 >= 0 ->
  p x0 x1 >= 0.
Proof.
unfold pI1, pI2, p.
validsdp.
Qed.

Theorem ind0 (x0 x1 : R) :
  p x0 x1 >= 0 -> g0 x0 x1 >= 0 -> 
  p (t0_x0 x0 x1) (t0_x1 x0 x1) >= 0.
Proof.
unfold p, g0, t0_x0, t0_x1.
validsdp.
Qed.

Theorem ind1 (x0 x1 : R) :
  p x0 x1 >= 0 -> g1 x0 x1 >= 0 ->
  p (t1_x0 x0 x1) (t1_x1 x0 x1) >= 0.
Proof.
unfold p, g1, t1_x0, t1_x1.
validsdp.
Qed.
