Require Export Bignums.BigQ.BigQ mathcomp.ssreflect.seq Interval.Float.Specific_ops.

Variant validsdp_tac_parameters :=
| s_sdpa
| s_csdp
| s_mosek
| s_verbose (verbosity: nat).

Register validsdp_tac_parameters as validsdp.soswitness.tac_parameters.type.
Register s_sdpa as validsdp.soswitness.tac_parameters.s_sdpa.
Register s_csdp as validsdp.soswitness.tac_parameters.s_csdp.
Register s_mosek as validsdp.soswitness.tac_parameters.s_mosek.
Register s_verbose as validsdp.soswitness.tac_parameters.s_verbose.

From Ltac2 Require Import Ltac2.

Ltac2 Type exn ::= [ Parse_error_arg1 (* expecting type *) (constr)
                   | Parse_error_arg2 (* expecting type *) (constr)
                   | No_witness | Constant_input].

Require Export soswitness_plugin.

(* [soswitness q [p1;...; pn] options] calls SDP solvers to retrieve
   witnesses for p1 >= 0 -> ... -> pn >= 0 -> q >= 0. It returns [(z, Q)]
   and [[(s1, (z1, Q1));...; (sn, (zn, Qn))]] where [z, Q] (z : vector
   of monomials, Q : float matrix) is a witness for q - \sum_i si pi
   >= 0 and each (zi, Qi) is a witness for si >= 0 (in the sense that
   zi^T Qi zi should be close from si and Qi should be positive
   semidefinite).

   [q] and the [pi] should be values of type seq (seq N * BigQ.t_),
   for instance [:: ([:: 2; 0], 3%bigQ); ([:: 0; 2], (10 # 12)%bigQ)]
   represents the polynomial (x, y) |-> 3 x^2 + 10/12 y^2
   [options] is a list of parameters of type validsdp_tac_parameters

   [z] is of type seq (seq N)
   [Q] is of type seq (seq (Specific_ops.s_float bigZ bigZ)) *)
Ltac2 @ external soswitness : constr -> constr -> constr list -> constr * constr := "soswitness" "soswitness".

(* Same as above but attempts to maximise lb such that p1 >= 0 ->
   ... -> pn >= 0 -> q >= lb. It returns a maximized [lb] and [(z, Q)]
   and [[(s1, (z1, Q1));...; (sn, (zn, Qn))]] as above.

   [lb] is of type BigQ.t *)
Ltac2 @ external soswitness_intro : constr -> constr -> constr list -> constr * constr * constr := "soswitness" "soswitness_intro".

Ltac2 soswitness_print_exn e :=
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
  Message.print m.
