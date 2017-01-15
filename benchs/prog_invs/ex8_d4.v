Require Import Reals.
Local Open Scope R_scope.
From ValidSDP Require Import validsdp.

(* Attempt to prove that p >= 0 with p below is an
 * inductive invariant, for the program
 *
x1 = rand(-1.0, 1.0);
x2 = rand(-1.0, 1.0);
while (-1 <= 0) {
  pre_x1 = x1; pre_x2 = x2;
  if (x2 <= x1) {
    x1 = 0.687 * pre_x1 + 0.558 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
    x2 = -0.292 * pre_x1 + 0.773 * pre_x2;
  } else {
    x1 = 0.369 * pre_x1 + 0.532 * pre_x2 - 0.0001 * pre_x1^2;
    x2 = -1.27 * pre_x1 + 0.12 * pre_x2 - 0.0001 * pre_x1 * pre_x2;
  }
}
 *)

(* initial condition -1 <= x1 <= 1 encoded as (x1 - 1)*(1 - x1) (>= 0) *)
Let pI1 (x0 x1 : R) := (x0 - 1) * (1 - x0).
(* initial condition -1 <= x2 <= 1 *)
Let pI2 (x0 x1 : R) := (x1 - 1) * (1 - x1).
(* guard x2 <= x1 (then branch) *)
Let g0 x0 x1 := x0 - x1.
(* assignment in then branch *)
Let t0_x0 (x0 x1 : R) := 687 / 1000 * x0 + 558 / 1000 * x1 - 1 / 10000 * x0 * x1.
Let t0_x1 (x0 x1 : R) := (-292) / 1000 * x0 + 773 / 1000 * x1.
(* guard x2 >= x1 (else branch) *)
Let g1 x0 x1 := x1 - x0.
(* assignment in else branch *)
Let t1_x0 (x0 x1 : R) := 369 / 1000 * x0 + 532 / 1000 * x1 - 1 / 10000 * x0^2.
Let t1_x1 (x0 x1 : R) := (-127) / 100 * x0 + 12 / 100 * x1 - 1 / 10000 * x0 * x1.

Let p x0 x1 :=
  360137561854871/1125899906842624
  + -4648532753362095/1152921504606846976 * x0^2
  + -522343598561959/576460752303423488 * x0 * x1
  + -7354102629772791/2305843009213693952 * x1^2
  + 5916113786527169/576460752303423488 * x0^3
  + -574397345683745/36028797018963968 * x0^2 * x1
  + -1432498279428087/576460752303423488 * x0 * x1^2
  + 4968500152983215/288230376151711744 * x1^3
  + -8454232510940359/72057594037927936 * x0^4
  + 8778941830946171/288230376151711744 * x0^3 * x1
  + -3420954828653527/36028797018963968 * x0^2 * x1^2
  + -8812954633677685/144115188075855872 * x0 * x1^3
  + -4295668762430125/72057594037927936 * x1^4.
  
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
