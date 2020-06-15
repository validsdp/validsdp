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

Declare ML Module "soswitness".

Ltac2 @ external soswitness : constr -> constr -> constr list -> constr := "soswitness" "soswitness".

Ltac2 @ external soswitness_intro : constr -> constr -> constr list -> constr := "soswitness" "soswitness_intro".
