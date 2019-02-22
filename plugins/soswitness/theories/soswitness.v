Require Export Bignums.BigQ.BigQ mathcomp.ssreflect.seq Interval.Interval_specific_ops.

Inductive validsdp_tac_parameters :=
| s_sdpa
| s_csdp
| s_mosek
| s_verbose (verbosity: nat).

From Ltac2 Require Import Ltac2.

Declare ML Module "soswitness".

Ltac2 @ external soswitness2 : constr -> ident -> unit := "soswitness" "soswitness2".