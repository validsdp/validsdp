Require Export Bignums.BigQ.BigQ mathcomp.ssreflect.seq Interval.Interval_specific_ops.

Inductive validsdp_tac_parameters :=
| s_sdpa
| s_csdp
| s_mosek
| s_verbose (verbosity: nat).
Register validsdp_tac_parameters as validsdp.soswitness.tac_parameters.type.
Register s_sdpa as validsdp.soswitness.tac_parameters.s_sdpa.
Register s_csdp as validsdp.soswitness.tac_parameters.s_csdp.
Register s_mosek as validsdp.soswitness.tac_parameters.s_mosek.
Register s_verbose as validsdp.soswitness.tac_parameters.s_verbose.

Declare ML Module "soswitness".
