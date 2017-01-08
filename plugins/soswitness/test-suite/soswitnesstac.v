Require Import ValidSDP.soswitness.

Open Scope N_scope.

Goal True.
Proof.
Fail soswitness of ([::] : seq (seq N * BigQ.t_)) as y.
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).
Fail soswitness of p as y'.
Fail soswitness of [:: ([:: 0; 0; 0; 0], 3%bigZ)] as y.
Fail soswitness of [:: ([:: 0; 0; 0; 0], 3%bigQ)] as y.
(*Fail soswitness of [:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)] as y'.*)
soswitness of [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)] as y.
Abort.

(*
Require Import Arith.PeanoNat.

Ltac prove_even :=
  match goal with
  | |- Nat.Even ?x =>
    let y := fresh "y" in
    soswitness of x as y;  (* puts x/2 in y *)
    let cs := eval cbv in y in clear y;
    exists cs; reflexivity
  end.

Goal Nat.Even 12.
Proof.
prove_even.
Qed.
 *)
