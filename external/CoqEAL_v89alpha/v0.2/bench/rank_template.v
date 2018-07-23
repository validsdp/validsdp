(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import Int31 Int31Native Streams.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements seqmatrix rank ssrint31 random intmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope int31_scope.

Definition n := #MXSIZE%N.

Definition S1 := random_mx n n.
Definition M := S1.1.

Eval native_compute in ignore M.

Definition P := @elim_rank_seqmx n n M.
Time Eval native_compute in P.
