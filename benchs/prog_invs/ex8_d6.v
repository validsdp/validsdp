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
  43123995072955912711/36893488147419103232
  + -6493559060491613/36893488147419103232 * x0^2
  + -884358362916423/18446744073709551616 * x0 * x1
  + -329763399056887/2305843009213693952 * x1^2
  + 149369550536191/36028797018963968 * x0^3
  + -4819241860629567/1152921504606846976 * x0^2 * x1
  + 3774600809056775/18446744073709551616 * x0 * x1^2
  + 3477006688641869/576460752303423488 * x1^3
  + -2244128971873147/9007199254740992 * x0^4
  + 4574509311614721/144115188075855872 * x0^3 * x1
  + -6453401090263411/36028797018963968 * x0^2 * x1^2
  + -2327838197255863/18014398509481984 * x0 * x1^3
  + -4964084993090941/36028797018963968 * x1^4
  + 5486717873434055/144115188075855872 * x0^5
  + -4029537496858215/36028797018963968 * x0^4 * x1
  + 3706449024899855/72057594037927936 * x0^3 * x1^2
  + 5038037496106181/288230376151711744 * x0^2 * x1^3
  + -5974525409517511/1152921504606846976 * x0 * x1^4
  + 5103977388721617/576460752303423488 * x1^5
  + -753920111973975/4503599627370496 * x0^6
  + 3618774720693301/18014398509481984 * x0^5 * x1
  + -920777858888785/4503599627370496 * x0^4 * x1^2
  + -796747567427347/4503599627370496 * x0^3 * x1^3
  + -1135212076048177/18014398509481984 * x0^2 * x1^4
  + -5945996449005367/144115188075855872 * x0 * x1^5
  + -858047383543717/18014398509481984 * x1^6.
  
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
