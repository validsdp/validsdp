Require Import Reals.
Require Import Interval.Interval_tactic.

(* Note: the error messages below were obtained with Coq 8.4pl6 *)

(** The tactic should always fail for syntax errors *)

Lemma fail_tuple_to_list : True.
Fail interval with (tt).
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Unknown tactic parameter tt (level 99). *)
Fail interval with (tt) || idtac.
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Unknown tactic parameter tt (level 98). *)
Abort.

Lemma fail_tuple_to_list_intro : True.
Fail interval_intro 0%R with (tt).
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Unknown tactic parameter tt (level 99). *)
Fail interval_intro 0%R with (tt) || idtac.
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Unknown tactic parameter tt (level 98). *)
Abort.

(** The tactic should fail gracefully for non-syntax errors *)

Lemma fail_get_bounds (x y : R) : (x <= y)%R -> (y - x >= 0)%R.
intros.
Fail interval with (i_prec 40).
(* Warning: Silently use the whole real line for the following terms: *)
(* y *)
(* x *)
(* You may need to unfold some of these terms, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
Fail interval.
(* Warning: Silently use the whole real line for the following terms: *)
(* y *)
(* x *)
(* You may need to unfold some of these terms, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
interval || idtac.
Abort.

Lemma fail_xalgorithm_pre : True.
Fail interval with (i_prec 40).
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Goal is not an inequality with constant bounds. *)
Fail interval.
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Goal is not an inequality with constant bounds. *)
interval || idtac.
Abort.

Lemma fail_do_interval : (PI > 314159265358979323846/100000000000000000000)%R.
Fail interval with (i_prec 40).
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
Fail interval.
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
interval || idtac.
Abort.

Lemma fail_do_interval : (PI > 314159265358979323846/100000000000000000000)%R.
Fail interval with (i_prec 40).
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
Fail interval.
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: *)
(*    Numerical evaluation failed to conclude. You may want to adjust some parameters. *)
interval || idtac.
Abort.

Lemma fail_do_interval_generalize_1 (x : R) : True.
Fail interval_intro (tan x) with (i_prec 40).
(* Warning: Silently use the whole real line for the following term: *)
(* x *)
(* You may need to unfold this term, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Nothing known about (tan x). *)
Fail interval_intro (tan x).
(* Warning: Silently use the whole real line for the following term: *)
(* x *)
(* You may need to unfold this term, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Nothing known about (tan x). *)
interval_intro (tan x) || idtac.
Abort.

Lemma fail_do_interval_generalize_2 (x : R) : True.
Fail interval_intro x with (i_prec 40).
(* Warning: Silently use the whole real line for the following term: *)
(* x *)
(* You may need to unfold this term, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Nothing known about x. *)
Fail interval_intro x.
(* Warning: Silently use the whole real line for the following term: *)
(* x *)
(* You may need to unfold this term, or provide a bound. *)
(* The command has indeed failed with message: *)
(* => Error: Tactic failure: Nothing known about x. *)
interval_intro x || idtac.
Abort.
