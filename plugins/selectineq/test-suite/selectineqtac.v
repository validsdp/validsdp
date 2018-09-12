Require Import ValidSDP.selectineq.

Require Import Reals.
Inductive type := Cstrict (ub : R) | Clarge (ub : R).

Ltac tac g k :=
  let aux c lb := k (c lb) in
  match g with
  | Rle ?x ?y => aux Clarge y
  | Rge ?x ?y => aux Clarge x
  | Rlt ?x ?y => aux Cstrict y
  | Rgt ?x ?y => aux Cstrict x
  end.

Ltac Running_Example expr (*point 1*) k :=
  let conc := constr:((R0 <= expr)%R) in
  tac (*point 3*) conc (*point 4*) ltac:(fun r => let v :=
    match r with
    | Clarge ?x => constr:((true, x))
    | Cstrict ?x => constr:((false, x))
    end in (*point 2*)
    k v).

Goal True.
Running_Example 12%R ltac:(fun res => idtac res).
(* Should display (true, 12%R) *)

running_example 12%R easy

(*
(* running_example0 12%R (ltac:(fun res => idtac res)). *)
running_example1 12%R ltac:(fun res => idtac res).
running_example2 12%R ltac:(fun res => idtac res).
running_example3 12%R ltac:(fun res => idtac res).
running_example4 12%R ltac:(fun res => idtac res).
running_example 12%R ltac:(fun res => idtac res).

(* Bug tactic=tactic5 ? *)
(* > running_example 12%R. *)
(* Error: Syntax error: [tactic:tactic] expected after [constr:constr] (in [tactic:simple_tactic]). *)

(* > running_example4 12%R. *)
(* Syntax error: [tactic:tactic_expr level 4] expected after [constr:constr] (in [tactic:simple_tactic]). *)
(* > running_example5 12%R. *)
(* Syntax error: [tactic:binder_tactic] expected after [constr:constr] (in [tactic:simple_tactic]). *)

Fail running_example0 12%R easy; fail.
Fail running_example1 12%R easy; fail.
Fail running_example2 12%R easy; fail.
Fail running_example3 12%R easy; fail.
running_example4 12%R easy; fail.
running_example 12%R easy; fail.
 *)
