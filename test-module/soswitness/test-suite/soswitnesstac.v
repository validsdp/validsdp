Require Import soswitness.soswitness.

Open Scope N_scope.

Goal True.
Proof.
Fail soswitness of ([::] : seq (seq N * BigQ.t_)) in y.
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).
Fail soswitness of p in y'.
Fail soswitness of [:: ([:: 0; 0; 0; 0], 3%bigZ)] in y.
Fail soswitness of [:: ([:: 0; 0; 0; 0], 3%bigQ)] in y.
Fail soswitness of [:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)] in y'.
soswitness of [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)] in y.
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
