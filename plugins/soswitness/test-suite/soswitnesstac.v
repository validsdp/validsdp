From Stdlib Require Import NArith.
From ValidSDP Require Import soswitness.

Open Scope N_scope.

Goal True.
Proof.
Fail ltac2:(let _ := soswitness constr:([::] : seq (seq N * BigQ.t_)) constr:([::] * seq (seq (seq N * BigQ.t_))) [] in ()).
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).
Fail ltac2:(let _ := soswitness constr:(p) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in ()).
Fail ltac2:(let _ := soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigZ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in ()).
Fail ltac2:(let _ := soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in ()).
Fail ltac2:(let _ := soswitness constr:(p) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)] in ()).
Fail ltac2:(let _ := soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigZ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)] in ()).
Fail ltac2:(let _ := soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)] in ()).
Fail ltac2:(let _ := soswitness constr:([:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in ()).

ltac2:(let _ := Control.plus
         (fun () => soswitness constr:([:: ([:: 2; 0], O); ([:: 0; 2], O)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         (fun e => soswitness_print_exn e; ('tt, 'tt)) in ()).
ltac2:(let _ := Control.plus
         (fun () => soswitness constr:([:: ([:: 2; 0], (-3)%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         (fun e => soswitness_print_exn e; ('tt, 'tt)) in ()).
ltac2:(let _ := Control.plus
         (fun () => soswitness constr:([:: ([:: 0; 0], (-3)%bigQ); ([:: 0; 0], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         (fun e => soswitness_print_exn e; ('tt, 'tt)) in ()).

ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_csdp); constr:(s_verbose 1)] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)]) constr:([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
ltac2:(let (r, rl) := soswitness constr:([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)]) constr:([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
(* ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa); constr:(s_verbose 1)] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))). *)
(* ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)]) constr:([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]]) [constr:(s_sdpa)] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))). *)
(* ltac2:(let (r, rl) := soswitness constr:([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)]) constr:([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]]) [constr:(s_sdpa)] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))). *)
Fail ltac2:(let _ := soswitness constr:([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in ()).
ltac2:(let (r, rl) := soswitness constr:([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)]) constr:([:: [:: ([:: 1], 1%bigQ); ([:: 0], (-2)%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.concat
               (Message.of_string "result: ")
               (Message.of_constr r))
            (Message.concat
               (Message.of_string ", ")
               (Message.of_constr rl)))).
Abort.
