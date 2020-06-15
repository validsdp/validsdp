Require Import NArith ValidSDP.soswitness.

Open Scope N_scope.

Ltac2 print_exn e :=
  let m :=
      match e with
      | Parse_error_arg1 e =>
        Message.concat
          (Message.of_string "+++ Parse_error_arg1, expected *value* of type: ")
          (Message.of_constr e)
      | Parse_error_arg2 e =>
        Message.concat
          (Message.of_string "+++ Parse_error_arg2, expected *value* of type: ")
          (Message.of_constr e)
      | No_witness => Message.of_string "+++ No_witness"
      | Constant_input => Message.of_string "+++ Constant_input"
      | _ => Message.of_string "+++ unknown exception"
      end in
  let _ := Message.print m in
  constr:(tt).

Goal True.
Proof.
Fail ltac2:(soswitness constr:([::] : seq (seq N * BigQ.t_)) constr:([::] * seq (seq (seq N * BigQ.t_))) []).
set (p := [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]).
Fail ltac2:(soswitness constr:(p) constr:([::] : seq (seq (seq N * BigQ.t_))) []).
Fail ltac2:(soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigZ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) []).
Fail ltac2:(soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) []).
Fail ltac2:(soswitness constr:(p) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)]).
Fail ltac2:(soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigZ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)]).
Fail ltac2:(soswitness constr:([:: ([:: 0; 0; 0; 0], 3%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa)]).
Fail ltac2:(soswitness constr:([:: ([:: 0; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ); ([:: 2; 1], (-12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) []).

ltac2:(Control.plus
         (fun () => soswitness constr:([:: ([:: 2; 0], O); ([:: 0; 2], O)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         print_exn).
ltac2:(Control.plus
         (fun () => soswitness constr:([:: ([:: 2; 0], (-3)%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         print_exn).
ltac2:(Control.plus
         (fun () => soswitness constr:([:: ([:: 0; 0], (-3)%bigQ); ([:: 0; 0], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [])
         print_exn).

ltac2:(let r := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
ltac2:(let r := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_csdp); constr:(s_verbose 1)] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
ltac2:(let r := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
ltac2:(let r := soswitness constr:([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)]) constr:([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
ltac2:(let r := soswitness constr:([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)]) constr:([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
(* ltac2:(let r := soswitness constr:([:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) [constr:(s_sdpa); constr:(s_verbose 1)] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))). *)
(* ltac2:(let r := soswitness constr:([:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 4%bigQ)]) constr:([:: [:: ([:: 2; 0], (-1)%bigQ); ([:: 0; 2], (-1)%bigQ); ([:: 0; 0], 2%bigQ)]]) [constr:(s_sdpa)] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))). *)
(* ltac2:(let r := soswitness constr:([:: ([:: 1; 0], 1%bigQ); ([:: 0; 1], 1%bigQ); ([:: 0; 0], 1%bigQ)]) constr:([:: [:: ([:: 1; 0], 1%bigQ)]; [:: ([:: 0; 1], 1%bigQ)]]) [constr:(s_sdpa)] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))). *)
Fail ltac2:(soswitness constr:([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)]) constr:([::] : seq (seq (seq N * BigQ.t_))) []).
ltac2:(let r := soswitness constr:([:: ([:: 2], 1%bigQ); ([:: 1], (-1)%bigQ)]) constr:([:: [:: ([:: 1], 1%bigQ); ([:: 0], (-2)%bigQ)]]) [] in
       Message.print
         (Message.concat
            (Message.of_string "result: ")
            (Message.of_constr r))).
Abort.
