Require Import ValidSDP.soswitness.

Open Scope N_scope.

Goal True.
Proof.
(* Fail soswitness of (([::], [::]) : seq (seq N * BigQ.t_) * seq (seq (seq N * BigQ.t_))) as y. (*?*) *)
(* set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]). *)

(* Fail soswitness of (p, ([::] : seq (seq (seq N * BigQ.t_)))) as y. *)
(* Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigZ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y. *)
(* Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y. *)

(* Fail soswitness of (p, ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil). *)
(* Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigZ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil). *)
(* Fail soswitness of ([:: ([:: 0; 0; 0; 0], 3%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y with (s_sdpa :: nil). *)

(*Fail soswitness of ([:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y'.*)

(* ltac2:(let r := soswitness2 constr:(([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_))))) [constr:(s_csdp); constr:(s_verbose 1)] in *)
ltac2:(let r := soswitness2 constr:(([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_))))) [] in
Message.print
  (Message.concat
     (Message.of_string "resultat: ")
     (Message.of_constr r))).

(* soswitness of ([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y. *)
(* soswitness of ([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)], ([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]])) as y'. *)
(* soswitness of ([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)], ([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]])) as y''. *)

(* soswitness of ([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as Y with (s_sdpa :: s_verbose 1 :: nil). *)
(* soswitness of ([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)], ([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]])) as Y' with (s_sdpa :: nil). *)
(* soswitness of ([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)], ([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]])) as Y'' with (s_sdpa :: nil). *)
(* soswitness_intro of ([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)], ([::] : seq (seq (seq N * BigQ.t_)))) as y'''. *)
(* soswitness_intro of ([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)], ([:: [:: ([:: 1], 1%bigQ); ([:: 0], (-2)%bigQ)]])) as y''''. *)
Abort.
