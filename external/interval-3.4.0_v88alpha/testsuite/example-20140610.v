Require Import Reals.
Require Import Interval_tactic.
Local Open Scope R_scope.

(*
Example taken from:
Marc Daumas and Guillaume Melquiond and César Muñoz,
Guaranteed Proofs Using Interval Arithmetic.
In IEEE ARITH 17, pages 188-195, 2005.
*)

Definition a := 6378137.
Definition f := 1000000000/298257223563.
Definition umf2 := (1 - f)².
Definition max := 715/512.
Definition rp phi := a / sqrt (1 + umf2 * (tan phi)²).
Definition arp phi :=
  let x := max² - phi² in
  4439091/4 + x * (9023647/4 + x * (
    13868737/64 + x * (13233647/2048 + x * (
      -1898597/16384 + x * (-6661427/131072))))).

Goal forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
unfold rp, arp, umf2, a, f, max.
intros phi Hphi.
(*
Time interval with (i_bisect_diff phi). (* 38 s *)
*)
Time interval with (i_bisect_taylor phi 5). (* 4.4 s *)
Qed.
