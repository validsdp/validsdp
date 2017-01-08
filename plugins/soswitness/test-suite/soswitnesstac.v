Require Import ValidSDP.soswitness.

Open Scope N_scope.

Goal True.
Proof.
Fail soswitness of (([::], [::]) : seq (seq N * BigQ.t_) * seq (seq (seq N * BigQ.t_))) as y.
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).
Fail soswitness of (p, ([::] : seq (seq (seq N * BigQ.t_)))) as y'.
Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigZ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y.
Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y.
(*Fail soswitness of ([:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y'.*)
soswitness of ([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y.
Abort.
