Require Import soswitness.soswitness.

Goal True.
Proof.
(*soswitness of ([::] : seq (seq nat * bigQ)) in y.*)  (* OSDP fails when we ask whether the 0 polynomial is SOS :( *)
soswitness of [:: ([:: 0; 0; 0; 0], 3%bigQ)] in y'.
soswitness of [:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)] in y''.
soswitness of [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)] in y'''.
Abort.

(*
Require Import Arith.PeanoNat.

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
 *)
