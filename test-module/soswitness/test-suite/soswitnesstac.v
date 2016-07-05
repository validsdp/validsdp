Require Import soswitness.soswitness Arith.PeanoNat.

Ltac prove_even :=
  match goal with
  | |- Nat.Even ?x =>
    let y := fresh "y" in
    soswitness of x in y;  (* puts x/2 in y *)
    let cs := eval cbv in y in clear y;
    exists cs; reflexivity
  end.

Goal Nat.Even 12.
Proof.
prove_even.
Qed.
