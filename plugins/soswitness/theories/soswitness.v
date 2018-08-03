Require Export Bignums.BigQ.BigQ mathcomp.ssreflect.seq Interval.Interval_specific_ops.

Inductive validsdp_tac_parameters :=
| s_sdpa
| s_csdp
| s_mosek
| s_verbose (verbosity: nat).

Declare ML Module "soswitness".
