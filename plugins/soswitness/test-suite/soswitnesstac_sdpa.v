Require Import ValidSDP.soswitness.

Open Scope N_scope.

Goal True.
Proof.
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).

Fail soswitness of (p, ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil).
Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigZ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil).
Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil).

soswitness of ([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as Y with (s_sdpa :: s_verbose 1 :: nil).
soswitness of ([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)], ([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]])) as Y' with (s_sdpa :: nil).
soswitness of ([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)], ([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]])) as Y'' with (s_sdpa :: nil).
Abort.
