(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Bool Reals List.
Require Import Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_xreal_derive.
Require Import Interval_definitions.
Require Import Interval_interval.
Require Import Interval_taylor_model.
Require Import coquelicot_compl.

Inductive unary_op : Set :=
  | Neg | Abs | Inv | Sqr | Sqrt
  | Cos | Sin | Tan | Atan | Exp | Ln
  | PowerInt (n : Z) | Nearbyint (m : rounding_mode).

Definition no_floor_op op :=
  match op with Nearbyint _ => false | _ => true end.

Inductive binary_op : Set :=
  | Add | Sub | Mul | Div.

Inductive term : Set :=
  | Forward : nat -> term
  | Unary : unary_op -> nat -> term
  | Binary : binary_op -> nat -> nat -> term.

Definition no_floor_term term :=
  match term with Unary op _ => no_floor_op op | _ => true end.

Definition no_floor_prog prog :=
  fold_left (fun r t => r && no_floor_term t) prog true.

Lemma no_floor_prog_cons t prog :
  no_floor_prog (t :: prog) = no_floor_term t && no_floor_prog prog.
Proof.
unfold no_floor_prog.
generalize true.
revert t; elim prog; simpl.
  now intros t b; case b; case no_floor_term.
intros a l IH t b.
now rewrite !IH; case no_floor_term; simpl; case no_floor_term; simpl.
Qed.

Lemma no_floor_prog_rcons t prog :
  no_floor_prog (prog ++ (t :: nil)) = no_floor_term t && no_floor_prog prog.
Proof.
unfold no_floor_prog.
generalize true.
revert t; elim prog; simpl.
  now intros t b; case b; case no_floor_term.
intros a l IH t b.
now rewrite !IH; case no_floor_term; simpl; case no_floor_term; simpl.
Qed.

Lemma no_floor_prog_rev prog :
  no_floor_prog (rev prog) = no_floor_prog prog.
Proof.
elim prog; simpl; try easy.
intros a l IH.
now rewrite no_floor_prog_rcons IH no_floor_prog_cons.
Qed.

Set Implicit Arguments.

Record operations (A : Type) : Type :=
  { constant : Z -> A
  ; unary : unary_op -> A -> A
  ; binary : binary_op -> A -> A -> A
  ; sign : A -> Xcomparison }.

Unset Implicit Arguments.

Definition eval_generic_body {A} def (ops : operations A) values op :=
  let nth n := nth n values def in
  match op with
  | Forward u => nth u
  | Unary o u => unary ops o (nth u)
  | Binary o u v => binary ops o (nth u) (nth v)
  end :: values.

Definition eval_generic {A} def (ops : operations A) :=
  fold_left (eval_generic_body def ops).

Lemma rev_formula :
  forall A formula terms def (ops : operations A),
  eval_generic def ops formula terms =
  fold_right (fun y x => eval_generic_body def ops x y) terms (rev formula).
Proof.
intros.
pattern formula at 1 ; rewrite <- rev_involutive.
unfold eval_generic, eval_generic_body.
rewrite <- fold_left_rev_right.
rewrite rev_involutive.
apply refl_equal.
Qed.

Theorem eval_inductive_prop :
  forall A B (P : A -> B -> Prop) defA defB (opsA : operations A) (opsB : operations B),
  P defA defB ->
 (forall o a b, P a b -> P (unary opsA o a) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (binary opsA o a1 a2) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (nth n inpA defA) (nth n inpB defB)) ->
  forall prog,
  forall n, P (nth n (eval_generic defA opsA prog inpA) defA) (nth n (eval_generic defB opsB prog inpB) defB).
Proof.
intros A B P defA defB opsA opsB Hdef Hun Hbin inpA inpB Hinp prog.
do 2 rewrite rev_formula.
induction (rev prog).
exact Hinp.
intros [|n].
2: apply IHl.
destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ] ; apply IHl.
Qed.

Theorem eval_inductive_no_floor_prop :
  forall A B (P : A -> B -> Prop) defA defB (opsA : operations A) (opsB : operations B),
  P defA defB ->
 (forall o a b, P a b -> no_floor_op o = true -> P (unary opsA o a) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (binary opsA o a1 a2) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (nth n inpA defA) (nth n inpB defB)) ->
  forall prog, no_floor_prog prog = true ->
  forall n, P (nth n (eval_generic defA opsA prog inpA) defA) (nth n (eval_generic defB opsB prog inpB) defB).
Proof.
intros A B P defA defB opsA opsB Hdef Hun Hbin inpA inpB Hinp prog.
rewrite -no_floor_prog_rev.
do 2 rewrite rev_formula.
induction (rev prog).
intros _.
exact Hinp.
rewrite no_floor_prog_cons.
intros H1.
assert (H2 : no_floor_term a = true).
  now revert H1; case no_floor_term.
assert (H3 : no_floor_prog l = true).
  now revert H1; case no_floor_term; try discriminate.
intros [|n].
2: now apply IHl.
now destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ]; try apply IHl.
Qed.

Definition ext_operations :=
  Build_operations (fun x => Xreal (IZR x))
   (fun o =>
    match o with
    | Neg => Xneg
    | Abs => Xabs
    | Inv => Xinv
    | Sqr => Xsqr
    | Sqrt => Xsqrt
    | Cos => Xcos
    | Sin => Xsin
    | Tan => Xtan
    | Atan => Xatan
    | Exp => Xexp
    | Ln => Xln
    | PowerInt n => fun x => Xpower_int x n
    | Nearbyint m => Xnearbyint m
    end)
   (fun o =>
    match o with
    | Add => Xadd
    | Sub => Xsub
    | Mul => Xmul
    | Div => Xdiv
    end)
   (fun x => Xcmp x (Xreal 0)).

Definition eval_ext :=
  eval_generic Xnan ext_operations.

Theorem eval_inductive_prop_fun :
  forall {T} A B P defA defB (opsA : operations A) (opsB : operations B),
 (forall a1 a2, (forall x, a1 x = a2 x) -> forall b, P a1 b -> P a2 b) ->
  P (fun _ : T => defA) defB ->
 (forall o a b, P a b -> P (fun x => unary opsA o (a x)) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (fun x => binary opsA o (a1 x) (a2 x)) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (fun x => nth n (inpA x) defA) (nth n inpB defB)) ->
  forall prog,
  forall n, P (fun x => nth n (eval_generic defA opsA prog (inpA x)) defA) (nth n (eval_generic defB opsB prog inpB) defB).
Proof.
intros T A B P defA defB opsA opsB HP Hdef Hun Hbin inpA inpB Hinp prog n.
apply HP with (fun x => nth n (fold_right (fun y x => eval_generic_body defA opsA x y) (inpA x) (rev prog)) defA).
intros x.
now rewrite rev_formula.
rewrite rev_formula.
generalize n. clear n.
induction (rev prog).
exact Hinp.
intros [|n].
2: apply IHl.
destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ] ; apply IHl.
Qed.

Theorem eval_inductive_prop_floor_fun :
  forall {T} A B P defA defB (opsA : operations A) (opsB : operations B),
 (forall a1 a2, (forall x, a1 x = a2 x) -> forall b, P a1 b -> P a2 b) ->
  P (fun _ : T => defA) defB ->
 (forall o a b, no_floor_op o = true -> P a b -> P (fun x => unary opsA o (a x)) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (fun x => binary opsA o (a1 x) (a2 x)) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (fun x => nth n (inpA x) defA) (nth n inpB defB)) ->
  forall prog, no_floor_prog prog = true ->
  forall n, P (fun x => nth n (eval_generic defA opsA prog (inpA x)) defA) (nth n (eval_generic defB opsB prog inpB) defB).
Proof.
intros T A B P defA defB opsA opsB HP Hdef Hun Hbin inpA inpB Hinp prog Hprog n.
apply HP with (fun x => nth n (fold_right (fun y x => eval_generic_body defA opsA x y) (inpA x) (rev prog)) defA).
intros x.
now rewrite rev_formula.
rewrite rev_formula.
generalize n. clear n.
revert Hprog; rewrite -no_floor_prog_rev.
induction (rev prog).
intros _.
exact Hinp.
rewrite no_floor_prog_cons.
intros H1.
assert (H2 : no_floor_term a = true).
  now revert H1; case no_floor_term.
assert (H3 : no_floor_prog l = true).
  now revert H1; case no_floor_term; try discriminate.
intros [|n].
2: now apply IHl.
now destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ] ; try apply IHl.
Qed.

Definition real_operations :=
  Build_operations IZR
   (fun o =>
    match o with
    | Neg => Ropp
    | Abs => Rabs
    | Inv => Rinv
    | Sqr => Rsqr
    | Sqrt => R_sqrt.sqrt
    | Cos => cos
    | Sin => sin
    | Tan => tan
    | Atan => atan
    | Exp => exp
    | Ln => ln
    | PowerInt n => fun x => powerRZ x n
    | Nearbyint m => Rnearbyint m
    end)
   (fun o =>
    match o with
    | Add => Rplus
    | Sub => Rminus
    | Mul => Rmult
    | Div => Rdiv
    end)
   (fun x => Xcmp (Xreal x) (Xreal 0)).

Definition eval_real :=
  eval_generic R0 real_operations.

Lemma rewrite_inv_diff :
  forall u u',
  Xmul u' (Xneg (Xsqr (Xinv u))) = Xneg (Xdiv u' (Xsqr u)).
Proof.
intros.
rewrite Xmul_Xneg_distr_r.
apply f_equal.
rewrite Xdiv_split.
apply f_equal.
assert (forall x, Xsqr x = Xmul x x) by now intros [|x].
rewrite 2!H.
apply sym_eq.
apply Xinv_Xmul_distr.
Qed.

Lemma rewrite_div_diff :
  forall u v u' v',
  Xdiv (Xsub u' (Xmul v' (Xdiv u v))) v = Xdiv (Xsub (Xmul u' v) (Xmul v' u)) (Xmul v v).
Proof.
intros.
repeat rewrite Xdiv_split.
rewrite Xinv_Xmul_distr.
repeat rewrite <- Xmul_assoc.
apply (f_equal (fun x => Xmul x (Xinv v))).
rewrite 2!Xsub_split.
rewrite Xadd_comm.
set (w := Xmul v' u).
rewrite Xmul_Xadd_distr_r.
rewrite Xmul_assoc Xmul_Xinv.
destruct (Xinv v) as [|z].
by rewrite /= 2!Xlift2_nan_r.
rewrite /= Xmul_1_r Xmul_Xneg_distr_l.
apply Xadd_comm.
Qed.

Lemma xreal_to_real :
  forall (P1 : ExtendedR -> Prop) (P2 : R -> Prop),
  (P1 Xnan -> forall r, P2 r) ->
  (forall r, P1 (Xreal r) -> P2 r) ->
  forall prog terms n,
  P1 (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  P2 (nth n (eval_real prog terms) 0%R).
Proof.
intros P1 P2 HP1 HP2 prog terms n.
unfold eval_ext, eval_real.
refine (_ (eval_inductive_prop _ _ (fun a b => match a with Xreal a => a = b | _ => True end)
  Xnan R0 ext_operations real_operations _ _ _ (map Xreal terms) terms _ prog n)).
case (nth n (eval_generic Xnan ext_operations prog (map Xreal terms)) Xnan).
intros _ H.
now apply HP1.
intros y H.
rewrite H.
apply HP2.
easy.
(* unary *)
destruct a as [|a].
now destruct o.
intros b H.
rewrite H.
destruct o ; try easy ; simpl ; unfold Xinv'.
now case (is_zero b).
unfold Xsqrt'.
now case (is_negative b).
unfold Xtan'.
now case (is_zero (cos b)).
unfold Xln'.
now case (is_positive b).
generalize (Xpower_int_correct n0 (Xreal b)).
simpl.
now case Xpower_int'.
(* binary *)
destruct a1 as [|a1].
now destruct o.
destruct a2 as [|a2].
now destruct o.
intros b1 b2 H1 H2.
rewrite H1 H2.
destruct o ; try easy ; simpl ; unfold Xdiv'.
now destruct (is_zero b2).
(* . *)
intros k.
destruct (le_or_lt (length (map Xreal terms)) k) as [H|H].
now rewrite nth_overflow.
rewrite (nth_indep _ _ (Xreal 0) H).
now rewrite map_nth.
Qed.

Lemma continuous_unary :
  forall unop a b x,
  no_floor_op unop = true ->
  (notXnan b -> b = Xreal (a x) /\ continuous a x) ->
  notXnan (unary ext_operations unop b) ->
  unary ext_operations unop b = Xreal (unary real_operations unop (a x)) /\
  continuous (fun x0 : R => unary real_operations unop (a x0)) x.
Proof.
move => unop a b x NF Hb HbnotXnan.
case Hbnan: b Hb => [|b1] // Hb.
rewrite Hbnan /= in HbnotXnan.
by case unop in HbnotXnan.
case: Hb => // Hb Hcontax.
move: HbnotXnan.
rewrite Hbnan Hb => {Hbnan Hb b1} HnotXnan.
split.
(case: unop NF HnotXnan; try discriminate) => //= [_|_|_|_|].
- rewrite /Xinv'.
  by case is_zero.
- rewrite /Xsqrt'.
  by case is_negative.
- rewrite /Xtan'.
  by case is_zero.
- rewrite /Xln'.
  by case is_positive.
- case => [||p] //.
  rewrite /Xpower_int'.
  by case is_zero.
(case: unop NF HnotXnan; try discriminate) => //=
    [_|_|_|_|_|_|_|_|_|_|_|].
- move => _. by apply: continuous_opp.
- move => _. by apply: continuous_Rabs_comp.
- move => HnotXnan.
  apply: continuous_Rinv_comp => // Ha.
  move: HnotXnan.
  by rewrite /Xinv' Ha is_zero_correct_zero.
- move => _. by apply: continuous_mult.
- move => HnotXnan.
  exact: continuous_sqrt_comp.
- move => _. by apply: continuous_cos_comp.
- move => _. by apply: continuous_sin_comp.
- move => HnotXnan.
  apply: continuous_comp => //.
  apply: continuous_tan => Ha.
    move: HnotXnan.
    by rewrite /Xtan' Ha is_zero_correct_zero.
- move => _. by apply: continuous_atan_comp.
- move => _. by apply: continuous_exp_comp.
- move => HnotXnan.
  apply: continuous_comp => //.
  apply: continuous_ln.
  rewrite /Xln' in HnotXnan.
  by case: is_positive_spec HnotXnan.
- move => n.
  rewrite /powerRZ.
  case: n => [|n|n] _ HnotXnan.
  + exact: continuous_const.
  + apply: (continuous_comp a (fun x => pow x _)) => //.
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
  + rewrite /Xpower_int' in HnotXnan.
    case: is_zero_spec HnotXnan => // Ha _.
    apply: continuous_comp.
    apply: (continuous_comp a (fun x => pow x _)) => //.
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
    apply: continuous_Rinv.
    exact: pow_nonzero.
Qed.

Module IntervalAlgos (I : IntervalOps).

Record check := {
  check_f : I.type -> bool;
  check_p : ExtendedR -> Prop;
  _ : forall y yi, contains (I.convert yi) y -> check_f yi = true -> check_p y
}.

Definition subset_check : I.type -> check.
Proof.
intros output.
apply (Build_check (fun i => I.subset i output) (contains (I.convert output))).
abstract (
  intros y yi Hy Hb ;
  assert (H := I.subset_correct yi output Hb) ;
  now apply subset_contains with (1 := H)).
Defined.

Definition positive_check : check.
Proof.
apply (Build_check
  (fun i => match I.sign_strict i with Xgt => true | _ => false end)
  (fun y => match y with Xreal r => (0 < r)%R | _ => False end)).
abstract (
  intros y yi Hy Hb ;
  generalize (I.sign_strict_correct yi) ;
  destruct (I.sign_strict yi) ; try easy ;
  intros H ;
  destruct (H y Hy) as (H1,H2) ;
  now rewrite H1).
Defined.

Definition nonzero_check : check.
Proof.
apply (Build_check
  (fun i => match I.sign_strict i with Xgt => true | Xlt => true | _ => false end)
  (fun y => match y with Xreal r => r <> R0 | _ => False end)).
abstract (
  intros y yi Hy Hb ;
  generalize (I.sign_strict_correct yi) ;
  destruct (I.sign_strict yi) ; try easy ;
  intros H ;
  destruct (H y Hy) as [H1 H2] ;
  rewrite H1 ;
  [ apply Rlt_not_eq | apply Rgt_not_eq ] ;
  assumption).
Defined.

Definition bisect_1d_step l u (check : I.type -> bool) cont :=
  if check (I.bnd l u) then true
  else
    let m := I.midpoint (I.bnd l u) in
    match cont l m with
    | true => cont m u
    | false => false
    end.

Fixpoint bisect_1d l u check steps { struct steps } :=
  match steps with
  | O => false
  | S n =>
    bisect_1d_step l u check
      (fun l u => bisect_1d l u check n)
  end.

Theorem bisect_1d_correct :
  forall steps inpl inpu f P,
  (forall y yi, contains (I.convert yi) y -> f yi = true -> P y) ->
  bisect_1d inpl inpu f steps = true ->
  forall x,
  contains (I.convert (I.bnd inpl inpu)) x -> P x.
Proof.
intros steps inpl inpu f P Hf.
revert inpl inpu.
induction steps.
intros inpl inpu Hb.
discriminate Hb.
intros inpl inpu.
simpl.
unfold bisect_1d_step.
case_eq (f (I.bnd inpl inpu)).
intros Hb _ x Hx.
now apply Hf with (2 := Hb).
intros _.
set (inpm := I.midpoint (I.bnd inpl inpu)).
case_eq (bisect_1d inpl inpm f steps) ; try easy.
intros Hl Hr x Hx.
apply (bisect P (I.convert_bound inpl) (I.convert_bound inpm) (I.convert_bound inpu)).
unfold domain.
rewrite <- I.bnd_correct.
apply IHsteps with (1 := Hl).
unfold domain.
rewrite <- I.bnd_correct.
apply IHsteps with (1 := Hr).
now rewrite <- I.bnd_correct.
Qed.

Definition lookup_1d_step fi l u output cont :=
  if I.subset (fi (I.bnd l u)) output then output
  else
    let m := I.midpoint (I.bnd l u) in
    let output := cont l m output in
    if I.lower_bounded output || I.upper_bounded output then cont m u output
    else output.

Fixpoint lookup_1d_main fi l u output steps { struct steps } :=
  match steps with
  | O => I.join (fi (I.bnd l u)) output
  | S n =>
    lookup_1d_step fi l u output
      (fun l u output => lookup_1d_main fi l u output n)
  end.

Definition lookup_1d fi l u extend steps :=
  let m := iter_nat (fun u => I.midpoint (I.bnd l u)) steps u in
  let output := extend (fi (I.bnd l m)) in
  match steps with
  | O => I.whole
  | S steps =>
    if I.lower_bounded output || I.upper_bounded output then
      lookup_1d_main fi l u output steps
    else output
  end.

Inductive bound_proof :=
  | Bproof : forall x xi, contains (I.convert xi) (Xreal x) -> bound_proof.

Definition real_from_bp v := match v with Bproof x _ _ => x end.
Definition xreal_from_bp v := match v with Bproof x _ _ => Xreal x end.
Definition interval_from_bp v := match v with Bproof _ xi _ => xi end.

Lemma iterated_bnd_nth :
  forall bounds n,
  contains (I.convert (nth n (map interval_from_bp bounds) I.nai))
    (nth n (map xreal_from_bp bounds) Xnan).
Proof.
intros bounds n.
destruct (le_or_lt (length bounds) n) as [H|H].
rewrite -> 2!nth_overflow by now rewrite map_length.
now rewrite I.nai_correct.
rewrite -> (nth_indep _ Xnan (Xreal 0)) by now rewrite map_length.
assert (H0: contains (I.convert I.nai) (Xreal 0)) by now rewrite I.nai_correct.
pose (b := Bproof R0 I.nai H0).
change (Xreal 0) with (xreal_from_bp b).
change I.nai with (interval_from_bp b).
rewrite 2!map_nth.
now case (nth n bounds b).
Qed.

Lemma continuous_eval_ext :
  forall prog bounds x m,
  no_floor_prog prog = true ->
  notXnan (nth m (eval_ext prog (Xreal x :: map xreal_from_bp bounds)) Xnan) ->
  continuous (fun x => nth m (eval_real prog (x :: map real_from_bp bounds)) R0) x.
Proof.
intros prog bounds x.
rewrite /eval_ext /eval_real.
intros m Hf H.
eapply proj2.
revert Hf m H.
apply: (eval_inductive_prop_floor_fun _ _ (fun (f : R -> R) v => notXnan v -> v = Xreal (f x) /\ continuous f x)) => //.
intros f1 f2 Heq b H Hb.
case: (H Hb) => {H} H H'.
split.
by rewrite -Heq.
now eapply continuous_ext.
move => unop a b Hb HnotXnan.
exact: continuous_unary.
(* case of binary operator *)
case => a1 a2 b1 b2 Ha1 Ha2 HnotXnan /=.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_plus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_minus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_mult.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => HnotXnan [] // Heq1 Hconta1 [] // Heq2 Hconta2.
  split => // .
  + move: HnotXnan.
    rewrite /= /Xdiv'.
    case: (is_zero b2) => // .
    by inversion Heq1; inversion Heq2.
  + apply: continuous_mult => // .
    apply: continuous_Rinv_comp => // Habs .
    by move: Heq2 HnotXnan => ->; rewrite /= /Xdiv' Habs is_zero_correct_zero.
intros [|n].
simpl.
intros _.
apply (conj eq_refl).
apply continuous_id.
simpl.
destruct (le_or_lt (length bounds) n).
rewrite nth_overflow => //.
by rewrite map_length.
rewrite (nth_indep _ _ (Xreal 0)).
replace (map xreal_from_bp bounds) with (map Xreal (map real_from_bp bounds)).
rewrite map_nth.
intros _.
apply (conj eq_refl).
apply continuous_const.
rewrite map_map.
apply map_ext.
now intros [].
by rewrite map_length.
Qed.

Module BndValuator.

Definition operations prec :=
  Build_operations I.fromZ
   (fun o =>
    match o with
    | Neg => I.neg
    | Abs => I.abs
    | Inv => I.inv prec
    | Sqr => I.sqr prec
    | Sqrt => I.sqrt prec
    | Cos => I.cos prec
    | Sin => I.sin prec
    | Tan => I.tan prec
    | Atan => I.atan prec
    | Exp => I.exp prec
    | Ln => I.ln prec
    | PowerInt n => fun x => I.power_int prec x n
    | Nearbyint m => I.nearbyint m
    end)
   (fun o =>
    match o with
    | Add => I.add prec
    | Sub => I.sub prec
    | Mul => I.mul prec
    | Div => I.div prec
    end)
    I.sign_strict.

Definition eval prec :=
  eval_generic I.nai (operations prec).

Lemma eval_correct_aux :
  forall prec prog terms bounds,
 (forall n, contains (I.convert (nth n bounds I.nai)) (nth n terms Xnan)) ->
  forall n,
  contains (I.convert (nth n (eval prec prog bounds) I.nai))
   (nth n (eval_ext prog terms) Xnan).
Proof.
intros prec prog terms bounds Hinp.
unfold eval, eval_ext.
apply (eval_inductive_prop _ _ (fun a b => contains (I.convert a) b)).
(* . *)
rewrite I.nai_correct.
exact I.
(* unary *)
destruct o ; simpl ;
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct
  | apply I.exp_correct
  | apply I.ln_correct
  | apply I.power_int_correct
  | apply I.nearbyint_correct ].
(* binary *)
destruct o ; simpl ;
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ].
(* . *)
exact Hinp.
Qed.

Theorem eval_correct :
  forall prec prog bounds n,
  contains
    (I.convert (nth n (eval prec prog (map interval_from_bp bounds)) I.nai))
    (nth n (eval_ext prog (map xreal_from_bp bounds)) Xnan).
Proof.
intros prec prog bounds.
apply eval_correct_aux.
apply iterated_bnd_nth.
Qed.

Theorem eval_correct_ext :
  forall prec prog bounds n,
  I.extension
    (fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) Xnan)
    (fun b => nth n (eval prec prog (b :: map interval_from_bp bounds)) I.nai).
Proof.
intros prec prog bounds n xi x Hx.
generalize n. clear n.
apply eval_correct_aux.
intros [|n].
exact Hx.
apply iterated_bnd_nth.
Qed.

Lemma continuous_eval :
  forall prec prog bounds m i x,
  no_floor_prog prog = true ->
  contains (I.convert i) (Xreal x) ->
  I.convert (nth m (eval prec prog (i :: map interval_from_bp bounds)) I.nai) <> Inan ->
  continuous (fun x => nth m (eval_real prog (x :: map real_from_bp bounds)) R0) x.
Proof.
move => prec prog bounds m i x Hf Hcontains HnotInan.
apply: continuous_eval_ext => //.
generalize (eval_correct_ext prec prog bounds m i (Xreal x) Hcontains).
revert HnotInan.
case I.convert => //.
by case: (nth _ _ _).
Qed.

Lemma ex_RInt_eval :
  forall prec prog bounds m a b i,
  no_floor_prog prog = true ->
  (forall x, Rmin a b <= x <= Rmax a b -> contains (I.convert i) (Xreal x)) ->
  I.convert (nth m (eval prec prog (i :: map interval_from_bp bounds)) I.nai) <> Inan ->
  ex_RInt (fun x => nth m (eval_real prog (x :: map real_from_bp bounds)) R0) a b.
Proof.
move => prec prog bounds m a b i Hf Hcontains HnotInan.
apply: ex_RInt_continuous.
intros z Hz.
apply: continuous_eval HnotInan => //.
exact: Hcontains.
Qed.

End BndValuator.

Module DiffValuator.

Definition diff_operations A (ops : @operations A) :=
  Build_operations
   (fun x => (constant ops x, constant ops 0))
   (fun o x =>
    match x with
    | (v, d) =>
      match o with
      | Neg => let f := unary ops Neg in (f v, f d)
      | Abs => let w := unary ops Abs v in (w,
        match sign ops v with Xlt => unary ops Neg d | Xgt => d | _ => unary ops Inv (constant ops 0) end)
      | Inv => let w := unary ops Inv v in (w,
        binary ops Mul d (unary ops Neg (unary ops Sqr w)))
      | Sqr => let w := binary ops Mul d v in (unary ops Sqr v, binary ops Add w w)
      | Sqrt => let w := unary ops Sqrt v in (w,
        binary ops Div d (binary ops Add w w))
      | Cos => (unary ops Cos v,
        binary ops Mul d (unary ops Neg (unary ops Sin v)))
      | Sin => (unary ops Sin v,
        binary ops Mul d (unary ops Cos v))
      | Tan => let w := unary ops Tan v in (w,
        binary ops Mul d (binary ops Add (constant ops 1) (unary ops Sqr w)))
      | Atan => (unary ops Atan v,
        binary ops Div d (binary ops Add (constant ops 1) (unary ops Sqr v)))
      | Exp => let w := unary ops Exp v in (w,
        binary ops Mul d w)
      | Ln => (unary ops Ln v,
        match sign ops v with Xgt => binary ops Div d v | _ => unary ops Inv (constant ops 0) end)
      | PowerInt n =>
        (unary ops o v, binary ops Mul d (binary ops Mul (constant ops n) (unary ops (PowerInt (n-1)) v)))
      | Nearbyint m => let w := unary ops (Nearbyint m) v in (w, unary ops Inv (constant ops 0))
      end
    end)
   (fun o x y =>
    match x, y with
    | (vx, dx), (vy, dy) =>
      match o with
      | Add => let f := binary ops Add in (f vx vy, f dx dy)
      | Sub => let f := binary ops Sub in (f vx vy, f dx dy)
      | Mul => let f := binary ops Mul in (f vx vy,
        binary ops Add (f dx vy) (f dy vx))
      | Div => let f := binary ops Div in
        let w := f vx vy in
        (w, f (binary ops Sub dx (binary ops Mul dy w)) vy)
      end
    end)
   (fun x => match x with (vx, _) => sign ops vx end).

Lemma unary_diff_correct :
  forall o f d x,
  Xderive_pt f x d ->
  let v := unary (diff_operations _ ext_operations) o (f x, d) in
  unary ext_operations o (f x) = fst v /\
  Xderive_pt (fun x0 => unary ext_operations o (f x0)) x (snd v).
Proof.
intros o f d x Hd.
destruct o ; simpl ; repeat split.
now apply Xderive_pt_neg.
rewrite /Xinv' is_zero_correct_zero.
now apply Xderive_pt_abs.
rewrite rewrite_inv_diff.
now apply Xderive_pt_inv.
eapply Xderive_pt_eq_fun.
2: now apply Xderive_pt_mul.
intros y.
simpl.
now case f.
now apply Xderive_pt_sqrt.
now apply Xderive_pt_cos.
now apply Xderive_pt_sin.
now apply Xderive_pt_tan.
now apply Xderive_pt_atan.
now apply Xderive_pt_exp.
rewrite /Xinv' is_zero_correct_zero.
now apply Xderive_pt_ln.
now apply Xderive_pt_power_int.
rewrite /Xinv' is_zero_correct_zero.
now destruct x.
Qed.

Lemma binary_diff_correct :
  forall o f1 f2 d1 d2 x,
  Xderive_pt f1 x d1 ->
  Xderive_pt f2 x d2 ->
  let v := binary (diff_operations _ ext_operations) o (f1 x, d1) (f2 x, d2) in
  binary ext_operations o (f1 x) (f2 x) = fst v /\
  Xderive_pt (fun x0 => binary ext_operations o (f1 x0) (f2 x0)) x (snd v).
Proof.
intros o f1 f2 d1 d2 x Hd1 Hd2.
destruct o ; simpl ; repeat split.
now apply Xderive_pt_add.
now apply Xderive_pt_sub.
now apply Xderive_pt_mul.
rewrite rewrite_div_diff.
now apply Xderive_pt_div.
Qed.

Lemma eval_diff_correct :
  forall prog terms n x,
  let v := nth n (eval_generic (Xnan, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xnan, Xnan) in
  nth n (eval_ext prog (x :: map Xreal terms)) Xnan = fst v /\
  Xderive_pt (fun x => nth n (eval_ext prog (x :: map Xreal terms)) Xnan) x (snd v).
Proof.
intros prog terms n x.
(*set (inpA x := x :: map Xreal terms).
set (inpB := (x, Xmask (Xreal 1) x) :: map (fun v : R => (Xreal v, Xmask (Xreal 0) x)) terms).*)
refine (eval_inductive_prop_fun _ _ (fun a b => a x = fst b /\ Xderive_pt a x (snd b)) _ _ _ _ _ _ _ _ _ _ _ _ _).
(* extensionality *)
intros a1 a2 Heq (bl, br).
simpl.
intros (Hl, Hr).
split.
now rewrite <- Heq.
apply Xderive_pt_eq_fun with (2 := Hr).
intros.
now apply sym_eq.
(* default *)
destruct x ; repeat split.
(* unary *)
intros o a (bl, br) (Hl, Hr).
simpl in Hl.
rewrite <- Hl.
now apply unary_diff_correct.
(* binary *)
intros o a1 a2 (bl1, br1) (bl2, br2) (Hl1, Hr1) (Hl2, Hr2).
simpl in Hl1, Hl2.
rewrite <- Hl1, <- Hl2.
now apply binary_diff_correct.
(* inputs *)
clear n.
intros [|n].
simpl.
repeat split.
apply Xderive_pt_identity.
simpl.
split.
rewrite <- (map_nth (@fst ExtendedR ExtendedR)).
rewrite map_map.
apply (f_equal (fun v => nth n v _)).
now apply map_ext.
rewrite <- map_nth.
rewrite map_map.
simpl.
destruct (le_or_lt (length terms) n) as [H|H].
rewrite -> 2!nth_overflow by now rewrite map_length.
now case x.
rewrite -> (nth_indep (map (fun _ => Xmask (Xreal 0) x) terms) _ (Xmask (Xreal 0) x))
  by now rewrite map_length.
change (Xmask (Xreal 0) x) with ((fun _ => Xmask (Xreal 0) x) R0) at 2.
rewrite map_nth.
rewrite -> (nth_indep _ _ (Xreal 0)) by now rewrite map_length.
rewrite map_nth.
apply Xderive_pt_constant.
Qed.

Lemma unary_diff_bnd_correct :
  forall prec o f f',
  let u x := unary (diff_operations _ ext_operations) o (f x, f' x) in
  forall yi yi' xi,
 (forall x, contains xi x -> contains (I.convert yi) (f x)) ->
 (forall x, contains xi x -> contains (I.convert yi') (f' x)) ->
  let v := unary (diff_operations _ (BndValuator.operations prec)) o (yi, yi') in
 (forall x, contains xi x -> contains (I.convert (snd v)) (snd (u x))).
Proof.
intros prec o f f' u yi yi' xi Hf Hf' v x Hx.
destruct o ; simpl ;
  repeat first
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct
  | apply I.exp_correct
  | apply I.ln_correct
  | apply I.power_int_correct
  | apply I.add_correct
  | apply I.mul_correct
  | apply I.div_correct
  | apply I.fromZ_correct
  | refine (I.add_correct _ _ _ (Xreal 1%R) _ _ _)
  | refine (I.mul_correct _ _ _ (Xreal (IZR _)) _ _ _) ] ;
  try now first [ apply Hf | apply Hf' ].
(* abs *)
generalize (I.inv_correct prec (I.fromZ 0) (Xreal 0) (I.fromZ_correct _)).
rewrite /= /Xinv' is_zero_correct_zero.
specialize (Hf _ Hx).
generalize (I.sign_strict_correct yi).
case I.sign_strict ; case (I.convert (I.inv prec (I.fromZ 0))) ; try easy.
intros H _.
specialize (H _ Hf).
rewrite (proj1 H).
simpl.
rewrite Rcompare_Lt.
apply I.neg_correct.
now apply Hf'.
apply H.
intros H _.
specialize (H _ Hf).
rewrite (proj1 H).
simpl.
rewrite Rcompare_Gt.
now apply Hf'.
apply H.
(* ln *)
generalize (I.inv_correct prec (I.fromZ 0) (Xreal 0) (I.fromZ_correct _)).
rewrite /= /Xinv' is_zero_correct_zero.
specialize (Hf _ Hx).
generalize (I.sign_strict_correct yi).
case I.sign_strict ; case (I.convert (I.inv prec (I.fromZ 0))) ; try easy.
intros H _.
specialize (H _ Hf).
rewrite {1}(proj1 H).
simpl.
rewrite Rcompare_Gt.
apply I.div_correct.
now apply Hf'.
exact Hf.
apply H.
(* nearbyint *)
apply (I.inv_correct _ _ (Xreal 0)).
apply I.fromZ_correct.
Qed.

Lemma binary_diff_bnd_correct :
  forall prec o f1 f2 f1' f2',
  let u x := binary (diff_operations _ ext_operations) o (f1 x, f1' x) (f2 x, f2' x) in
  forall yi1 yi2 yi1' yi2' xi,
 (forall x, contains xi x -> contains (I.convert yi1) (f1 x)) ->
 (forall x, contains xi x -> contains (I.convert yi2) (f2 x)) ->
 (forall x, contains xi x -> contains (I.convert yi1') (f1' x)) ->
 (forall x, contains xi x -> contains (I.convert yi2') (f2' x)) ->
  let v := binary (diff_operations _ (BndValuator.operations prec)) o (yi1, yi1') (yi2, yi2') in
 (forall x, contains xi x -> contains (I.convert (snd v)) (snd (u x))).
Proof.
intros prec o f1 f2 f1' f2' u yi1 yi2 yi1' yi2' xi Hf1 Hf2 Hf1' Hf2' v x Hx.
destruct o ; simpl ;
  repeat first
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ] ;
  now first [ apply Hf1 | apply Hf2 | apply Hf1' | apply Hf2' ].
Qed.

Lemma eval_diff_bnd_correct :
  forall prec prog bounds n,
  let ff' x := nth n (eval_generic (Xnan, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) (map real_from_bp bounds))) (Xnan, Xnan) in
  let ffi' xi := nth n (eval_generic (I.nai, I.nai) (diff_operations _ (BndValuator.operations prec)) prog
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) (map interval_from_bp bounds))) (I.nai, I.nai) in
  forall xi,
  nth n (BndValuator.eval prec prog (xi :: map interval_from_bp bounds)) I.nai = fst (ffi' xi) /\
 (forall x, contains (I.convert xi) x -> contains (I.convert (snd (ffi' xi))) (snd (ff' x))).
Proof.
intros prec prog bounds n ff' ffi' xi.
split.
(* . *)
unfold ffi', BndValuator.eval.
apply (eval_inductive_prop _ (I.type * I.type) (fun a b => a = fst b)).
apply refl_equal.
intros o a (bl, br) H.
rewrite H.
now destruct o.
intros o a1 a2 (bl1, br1) (bl2, br2) H1 H2.
rewrite H1 H2.
now destruct o.
clear.
intros [|n].
apply refl_equal.
simpl.
rewrite <- (map_nth (@fst I.type I.type)).
rewrite map_map.
simpl.
apply sym_eq.
exact (map_nth _ _ _ _).
(* . *)
refine (let toto := _ in fun x Hx => proj2 (toto x Hx : contains (I.convert (fst (ffi' xi))) (fst (ff' x)) /\ _)).
apply (eval_inductive_prop_fun (ExtendedR * _) (I.type * _) (fun a b =>
  forall x, contains (I.convert xi) x ->
  contains (I.convert (fst b)) (fst (a x)) /\
  contains (I.convert (snd b)) (snd (a x)))).
intros f1 f2 Heq (yi, yi') H x Hx.
rewrite <- Heq.
now apply H.
intros _ _.
simpl.
rewrite I.nai_correct.
now split.
intros o f (yi, yi') H x Hx.
rewrite (surjective_pairing (f x)).
split.
assert (Hf := proj1 (H x Hx)).
destruct o ; simpl ;
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct
  | apply I.exp_correct
  | apply I.ln_correct
  | apply I.power_int_correct
  | apply I.nearbyint_correct ] ;
  exact Hf.
apply (unary_diff_bnd_correct prec o (fun x => fst (f x)) (fun x => snd (f x))) with (3 := Hx).
exact (fun x Hx => proj1 (H x Hx)).
exact (fun x Hx => proj2 (H x Hx)).
intros o f1 f2 (yi1, yi1') (yi2, yi2') H1 H2 x Hx.
rewrite (surjective_pairing (f1 x)).
rewrite (surjective_pairing (f2 x)).
split.
assert (Hf1 := proj1 (H1 x Hx)).
assert (Hf2 := proj1 (H2 x Hx)).
destruct o ; simpl ;
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ] ;
  first [ exact Hf1 | exact Hf2 ].
apply (binary_diff_bnd_correct prec o (fun x => fst (f1 x)) (fun x => fst (f2 x)) (fun x => snd (f1 x)) (fun x => snd (f2 x))) with (5 := Hx).
exact (fun x Hx => proj1 (H1 x Hx)).
exact (fun x Hx => proj1 (H2 x Hx)).
exact (fun x Hx => proj2 (H1 x Hx)).
exact (fun x Hx => proj2 (H2 x Hx)).
clear.
intros [|n] x Hx ; simpl.
split.
exact Hx.
apply I.mask_correct.
apply I.fromZ_correct.
exact Hx.
split.
rewrite <- (map_nth (@fst I.type I.type)).
rewrite <- (map_nth (@fst ExtendedR ExtendedR)).
do 4 rewrite map_map.
simpl.
replace (map (fun x => interval_from_bp x) bounds) with (map interval_from_bp bounds).
replace (map (fun x => Xreal (real_from_bp x)) bounds) with (map xreal_from_bp bounds).
apply iterated_bnd_nth.
apply map_ext.
now destruct a.
apply map_ext.
now destruct a.
rewrite <- (map_nth (@snd I.type I.type)).
rewrite <- (map_nth (@snd ExtendedR ExtendedR)).
do 4 rewrite map_map.
simpl.
assert (H1 := map_length (fun _ => I.mask (I.fromZ 0) xi) bounds).
assert (H2 := map_length (fun _ => Xmask (Xreal 0) x) bounds).
destruct (le_or_lt (length bounds) n).
generalize H. intro H0.
rewrite <- H1 in H.
rewrite <- H2 in H0.
rewrite -> nth_overflow with (1 := H).
rewrite -> nth_overflow with (1 := H0).
now rewrite I.nai_correct.
replace (nth n (map (fun _ => I.mask (I.fromZ 0) xi) bounds) I.nai) with (I.mask (I.fromZ 0) xi).
replace (nth n (map (fun _ => Xmask (Xreal 0) x) bounds) Xnan) with (Xmask (Xreal 0) x).
apply I.mask_correct.
apply I.fromZ_correct.
exact Hx.
rewrite <- H2 in H.
rewrite (nth_indep _ Xnan (Xmask (Xreal 0) x) H).
apply sym_eq.
refine (map_nth _ bounds (Bproof 0 I.nai _) _).
now rewrite I.nai_correct.
rewrite <- H1 in H.
rewrite (nth_indep _ I.nai (I.mask (I.fromZ 0) xi) H).
apply sym_eq.
refine (map_nth _ bounds (Bproof 0 I.nai _) _).
now rewrite I.nai_correct.
Qed.

Definition diff_refining_points prec xi di yi yi' ym yl yu :=
  match I.sign_large yi' with
  | Xund =>
    if I.bounded yi' then
      I.meet yi (I.add prec ym (I.mul prec di yi'))
    else yi
  | Xeq => ym
  | Xlt =>
    I.meet
     (if I.lower_bounded xi then I.lower_extent yl
      else I.whole)
     (if I.upper_bounded xi then I.upper_extent yu
      else I.whole)
  | Xgt =>
    I.meet
     (if I.lower_bounded xi then I.upper_extent yl
      else I.whole)
     (if I.upper_bounded xi then I.lower_extent yu
      else I.whole)
  end.

Definition diff_refining prec xi yi yi' fi :=
  match I.sign_large yi' with
  | Xund =>
    if I.bounded yi' then
      let m := I.midpoint xi in
      let mi := I.bnd m m in
      I.meet yi
       (I.add prec (fi mi) (I.mul prec (I.sub prec xi mi) yi'))
    else yi
  | Xeq =>
    let m := I.midpoint xi in fi (I.bnd m m)
  | Xlt =>
    I.meet
     (if I.lower_bounded xi then
        let l := I.lower xi in
        I.lower_extent (fi (I.bnd l l))
      else I.whole)
     (if I.upper_bounded xi then
        let u := I.upper xi in
        I.upper_extent (fi (I.bnd u u))
      else I.whole)
  | Xgt =>
    I.meet
     (if I.lower_bounded xi then
        let l := I.lower xi in
        I.upper_extent (fi (I.bnd l l))
      else I.whole)
     (if I.upper_bounded xi then
      let u := I.upper xi in
        I.lower_extent (fi (I.bnd u u))
      else I.whole)
  end.

Lemma diff_refining_aux_0 :
  forall f f' xi yi',
  Xderive f f' ->
  I.sign_large yi' <> Xund ->
 (forall x, contains xi x -> contains (I.convert yi') (f' x)) ->
  forall x, contains xi x ->
  x = Xreal (proj_val x) /\
  forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)).
Proof.
intros f f' xi yi' Hd Hs Hy' x Hx.
case_eq (f' x).
(* assuming f'(x) is NaN ... *)
intros Hnf'.
generalize (Hy' _ Hx).
rewrite Hnf'.
intros Hny'.
apply False_ind.
generalize (I.sign_large_correct yi').
destruct (I.sign_large yi') ; intros H.
generalize (H _ Hny').
discriminate.
destruct (H _ Hny') as (H0, _).
discriminate H0.
destruct (H _ Hny') as (H0, _).
discriminate H0.
now elim Hs.
(* ... leads to a contradiction, so f'(x) is real ... *)
intros ry' Hrf'.
generalize (Hd x).
destruct x as [|x].
rewrite Hrf'.
now intro H.
(* ... so x is real too *)
rewrite Hrf'.
unfold Xderive_pt.
case_eq (f (Xreal x)).
now intros _ H.
intros ry Hrf _.
repeat split.
unfold proj_fun, proj_val.
now rewrite Hrf.
unfold proj_fun, proj_val.
now rewrite Hrf'.
Qed.

Lemma diff_refining_aux_1 :
  forall prec f f' xi yi' m mi ymi,
  Xderive f f' ->
  contains (I.convert mi) (Xreal m) ->
  contains (I.convert xi) (Xreal m) ->
  contains (I.convert ymi) (f (Xreal m)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) ->
  forall x, contains (I.convert xi) x ->
  contains (I.convert (I.add prec ymi (I.mul prec (I.sub prec xi mi) yi'))) (f x).
Proof.
intros prec f f' xi yi' m mi ymi Hd Hxm Hm Hym Hy' x Hx.
case_eq (I.convert yi').
(* - yi' is NaI *)
intro Hyn'.
rewrite I.add_propagate_r.
easy.
now apply I.mul_propagate_r.
(* - yi' is real ... *)
intros yl' yu' Hyi'.
destruct x as [|x].
case_eq (I.convert xi).
intros Hxi.
generalize (Hy' _ Hx).
rewrite Hyi'.
generalize (Hd Xnan).
unfold Xderive_pt.
case (f' Xnan).
intros _ H.
elim H.
intros _ H _.
elim H.
intros xl xu Hxi.
rewrite Hxi in Hx.
elim Hx.
(* ... so x is real ... *)
set (Pxi := fun x => contains (I.convert xi) (Xreal x)).
assert (H': forall c, Pxi c -> f' (Xreal c) <> Xnan).
intros c Hc H.
generalize (Hy' (Xreal c) Hc).
rewrite H Hyi'.
intro H0.
elim H0.
(* ... and we can apply the MVT *)
destruct (Xderive_MVT _ _ Hd Pxi (contains_connected _) H' _ Hm _ Hx) as (c, (Hc1, Hc2)).
rewrite Hc2.
apply I.add_correct.
exact Hym.
rewrite Xmul_comm.
apply I.mul_correct.
now apply I.sub_correct.
apply Hy'.
exact Hc1.
Qed.

Lemma diff_refining_aux_2 :
  forall f f' xi m ymi,
  Xderive f f' ->
  contains xi (Xreal m) ->
  contains ymi (f (Xreal m)) ->
 (forall x, contains xi x -> contains (Ibnd (Xreal 0) (Xreal 0)) (f' x)) ->
  forall x, contains xi x ->
  contains ymi (f x).
Proof.
intros f f' xi m ymi Hd Hm Hym Hy'.
(* the derivative is zero ... *)
destruct xi as [|xl xu].
apply False_ind.
generalize (Hy' Xnan I) (Hd Xnan).
now case (f' (Xnan)).
intros [|x] Hx.
elim Hx.
(* ... so x is real ... *)
set (Pxi := fun x => contains (Ibnd xl xu) (Xreal x)).
assert (H': forall c, Pxi c -> f' (Xreal c) <> Xnan).
intros c Hc H.
generalize (Hy' (Xreal c) Hc).
now rewrite H.
(* ... and we can apply the MVT *)
destruct (Xderive_MVT _ _ Hd Pxi (contains_connected _) H' _ Hm _ Hx) as (c, (Hc1, Hc2)).
rewrite Hc2.
replace (f' (Xreal c)) with (Xreal 0).
simpl.
rewrite Rmult_0_l.
rewrite Xadd_0_r.
exact Hym.
generalize (Hy' (Xreal c) Hc1).
destruct (f' (Xreal c)) as [|y].
intro H.
elim H.
intros (H3,H4).
apply f_equal.
now apply Rle_antisym.
Qed.

Theorem diff_refining_points_correct :
  forall prec f f' xi yi yi' ym yl yu,
  Xderive f f' ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi) (f x)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) ->
  contains (I.convert ym) (f (I.convert_bound (I.midpoint xi))) ->
 (if I.lower_bounded xi then
    contains (I.convert yl) (f (I.convert_bound (I.lower xi)))
  else True) ->
 (if I.upper_bounded xi then
    contains (I.convert yu) (f (I.convert_bound (I.upper xi)))
  else True) ->
  let m := I.midpoint xi in
  forall x, contains (I.convert xi) x ->
  contains (I.convert (diff_refining_points prec xi (I.sub prec xi (I.bnd m m)) yi yi' ym yl yu)) (f x).
Proof.
intros prec f f' xi yi yi' ym yl yu Hd Hyi Hyi' Hym Hyl Hyu m x Hx.
unfold m. clear m.
unfold diff_refining_points.
generalize (I.sign_large_correct yi').
case_eq (I.sign_large yi') ; intros Hs1 Hs2.
(* - sign is Xeq *)
destruct (I.midpoint_correct xi (ex_intro _ _ Hx)) as (H1, H2).
eapply diff_refining_aux_2 with (1 := Hd) (5 := Hx).
instantiate (1 := proj_val (I.convert_bound (I.midpoint xi))).
now rewrite <- H1.
now rewrite <- H1.
intros.
rewrite (Hs2 (f' x0)).
split ; apply Rle_refl.
now apply Hyi'.
(* - sign is Xlt *)
assert (I.sign_large yi' <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (proj_fun v f' (proj_val x) <= 0)%R).
intros a Ha v.
destruct (Hs2 _ (Hyi' _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
rewrite H in Hyl.
clear Hym Hyu H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
now rewrite <- (proj1 (Hs2 _ Hl 0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2 Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite -> Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
rewrite H in Hyu.
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
now rewrite <- (proj1 (Hs2 _ Hu 0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2 Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite -> Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xgt *)
assert (I.sign_large yi' <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (0 <= proj_fun v f' (proj_val x))%R).
intros a Ha v.
destruct (Hs2 _ (Hyi' _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
rewrite H in Hyl.
clear H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
now rewrite <- (proj1 (Hs2 _ Hl 0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun 0 f) (proj_fun 0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2 Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite -> Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
rewrite H in Hyu.
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
now rewrite <- (proj1 (Hs2 _ Hu 0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun 0 f) (proj_fun 0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2 Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite -> Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xund *)
clear Hs1 Hs2.
case_eq (I.bounded yi') ; intro Hb.
apply I.meet_correct.
now apply Hyi.
destruct (I.midpoint_correct xi (ex_intro _ _ Hx)) as (Hm1, Hm2).
eapply diff_refining_aux_1 with (1 := Hd).
rewrite I.bnd_correct.
rewrite Hm1.
split ; apply Rle_refl.
now rewrite <- Hm1.
now rewrite <- Hm1.
exact Hyi'.
exact Hx.
now apply Hyi.
Qed.

Lemma convert_bnd :
  forall l u v, contains (Ibnd l u) (I.convert_bound v) ->
  contains (I.convert (I.bnd v v)) (I.convert_bound v).
Proof.
intros l u v H.
rewrite I.bnd_correct.
destruct (I.convert_bound v).
elim H.
split ; apply Rle_refl.
Qed.

Theorem diff_refining_correct :
  forall prec f f' fi fi',
  I.extension f fi ->
  I.extension f' fi' ->
  Xderive f f' ->
  I.extension f (fun b => diff_refining prec b (fi b) (fi' b) fi).
Proof.
intros prec f f' fi fi' Hf Hf' Hd xi x Hx.
unfold diff_refining.
case_eq (I.convert xi) ; intros.
(* - xi is Inan *)
assert (contains (I.convert (fi' xi)) Xnan).
replace Xnan with (f' Xnan).
apply Hf'.
now rewrite H.
generalize (Hd Xnan).
now case (f' Xnan) ; intros.
generalize (I.sign_large_correct (fi' xi)).
case (I.sign_large (fi' xi)) ; intro.
now assert (H2 := H1 _ H0).
now assert (H2 := proj1 (H1 _ H0)).
now assert (H2 := proj1 (H1 _ H0)).
clear H1.
generalize (I.bounded_correct (fi' xi)).
case (I.bounded (fi' xi)).
intro H1.
generalize (I.lower_bounded_correct _ (proj1 (H1 (refl_equal _)))).
clear H1. intros (_, H1).
unfold I.bounded_prop in H1.
now destruct (I.convert (fi' xi)).
intros _.
now apply Hf.
(* - xi is Ibnd *)
apply diff_refining_points_correct with (1 := Hd) (7 := Hx).
apply Hf.
apply Hf'.
apply Hf.
apply (convert_bnd l u).
rewrite <- H.
exact (proj2 (I.midpoint_correct _ (ex_intro _ _ Hx))).
(*   lower bound *)
generalize (I.lower_bounded_correct xi).
case (I.lower_bounded xi).
refine (fun H0 => _ (H0 (refl_equal true))).
clear H0.
intros (H0, H1).
apply Hf.
apply (convert_bnd l l).
rewrite -> H1, H0 in H.
rewrite H0.
inversion H.
split ; apply Rle_refl.
now intros _.
(*   upper bound *)
generalize (I.upper_bounded_correct xi).
case (I.upper_bounded xi).
refine (fun H0 => _ (H0 (refl_equal true))).
clear H0.
intros (H0, H1).
apply Hf.
apply (convert_bnd u u).
rewrite -> H1, H0 in H.
rewrite H0.
inversion H.
split ; apply Rle_refl.
now intros _.
Qed.

Definition eval prec formula bounds n xi :=
  match nth n (eval_generic (I.nai, I.nai) (diff_operations _ (BndValuator.operations prec)) formula
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) bounds)) (I.nai, I.nai) with
  | (yi, yi') =>
    diff_refining prec xi yi yi'
      (fun b => nth n (BndValuator.eval prec formula (b :: bounds)) I.nai)
  end.

Theorem eval_correct_ext :
  forall prec prog bounds n,
  I.extension
    (fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) Xnan)
    (fun b => eval prec prog (map interval_from_bp bounds) n b).
Proof.
intros prec prog bounds n xi x Hx.
unfold eval.
pose (f := fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) Xnan).
fold (f x).
pose (ff' := fun x => nth n (eval_generic (Xnan, Xnan) (diff_operations _ ext_operations) prog
     ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) (map real_from_bp bounds))) (Xnan, Xnan)).
set (fi := fun xi => nth n (BndValuator.eval prec prog (xi :: map interval_from_bp bounds)) I.nai).
pose (ffi' := fun xi => nth n (eval_generic (I.nai, I.nai) (diff_operations _ (BndValuator.operations prec)) prog
     ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) (map interval_from_bp bounds))) (I.nai, I.nai)).
fold (ffi' xi).
rewrite (surjective_pairing (ffi' xi)).
refine (_ (eval_diff_bnd_correct prec prog bounds n)).
intros H.
replace (fst (ffi' xi)) with (fi xi).
pose (fi' := fun xi => snd (ffi' xi)).
fold (fi' xi).
pose (f' x := snd (ff' x)).
refine (diff_refining_correct prec f f' _ _ _ _ _ xi x Hx) ;
  clear Hx xi x.
(* . *)
apply BndValuator.eval_correct_ext.
intros xi x Hx.
exact (proj2 (H xi) x Hx).
intros x.
generalize (proj2 (eval_diff_correct prog (map real_from_bp bounds) n x)).
fold (ff' x).
replace (map Xreal (map real_from_bp bounds)) with (map xreal_from_bp bounds).
fold f.
exact (fun p => p).
rewrite map_map.
apply map_ext.
now destruct a.
exact (proj1 (H xi)).
Qed.

End DiffValuator.

Module TaylorValuator.

Module TM := TM I.

Definition operations prec deg xi :=
  Build_operations
   (fun _ => TM.dummy) (* fromZ *)
   (fun o =>
    match o with
    | Neg => TM.opp (prec, deg) xi
    | Abs => TM.abs (prec, deg) xi
    | Inv => TM.inv (prec, deg) xi
    | Sqr => TM.sqr (prec, deg) xi
    | Sqrt => TM.sqrt (prec, deg) xi
    | Cos => TM.cos (prec, deg) xi
    | Sin => TM.sin (prec, deg) xi
    | Tan => TM.tan (prec, deg) xi
    | Atan => TM.atan (prec, deg) xi
    | Exp => TM.exp (prec, deg) xi
    | Ln => TM.ln (prec, deg) xi
    | PowerInt n => TM.power_int n (prec, deg) xi
    | Nearbyint m => TM.nearbyint m (prec, deg) xi
 (* | _ => fun _ => TM.dummy *)
    end)
   (fun o =>
    match o with
    | Add => TM.add (prec, deg) xi
    | Sub => TM.sub (prec, deg) xi
    | Mul => TM.mul (prec, deg) xi
    | Div => TM.div (prec, deg) xi
    end)
   (fun _ => Xund) (* sign_strict *).

Definition eval prec deg xi :=
  eval_generic TM.dummy (operations prec deg xi).

Theorem eval_correct_aux :
  forall prec deg prog bounds n xi,
  TM.approximates xi
    (nth n (eval prec deg xi prog (TM.var :: map (fun b => TM.const (interval_from_bp b)) bounds)) TM.dummy)
    (fun x => nth n (eval_ext prog (Xreal x :: map xreal_from_bp bounds)) Xnan).
Proof.
intros prec deg prog bounds n xi.
unfold eval, eval_ext.
rewrite rev_formula.
apply (@TM.approximates_ext (fun t => nth n (fold_right
  (fun y l => eval_generic_body Xnan ext_operations l y)
  (Xreal t :: map xreal_from_bp bounds)
  (rev prog)) Xnan)).
intros t.
apply (f_equal (fun v => nth n v _)).
apply sym_eq, rev_formula.
revert n.
induction (rev prog) as [|t l].
- intros [|n].
  + now apply TM.var_correct.
  + simpl.
    destruct (le_or_lt (length bounds) n) as [H|H].
    rewrite -> nth_overflow by now rewrite map_length.
    apply (@TM.approximates_ext (fun _ => Xnan)).
    intros t.
    apply sym_eq, nth_overflow.
    now rewrite map_length.
    now apply TM.dummy_correct.
    assert (H0: contains (I.convert I.nai) (Xreal 0)) by now rewrite I.nai_correct.
    pose (b := Bproof R0 I.nai H0).
    rewrite (nth_indep _ TM.dummy (TM.const (interval_from_bp b))).
    2: now rewrite map_length.
    rewrite (map_nth (fun v => TM.const (interval_from_bp v))).
    apply (@TM.approximates_ext (fun t => xreal_from_bp (nth n bounds b))).
    intros t.
    rewrite (nth_indep _ _ (xreal_from_bp b)).
    apply sym_eq, (map_nth xreal_from_bp).
    now rewrite map_length.
    destruct (nth n bounds b) as [t ti Ht].
    simpl.
    now apply TM.const_correct with (1 := Ht).
- intros [|n].
  2: apply IHl.
  simpl.
  destruct t as [|uo n1|bo n1 n2].
  + apply IHl.
  + generalize (IHl n1).
    destruct uo.
    apply TM.opp_correct.
    apply TM.abs_correct.
    apply TM.inv_correct.
    apply TM.sqr_correct.
    apply TM.sqrt_correct.
    apply TM.cos_correct.
    apply TM.sin_correct.
    apply TM.tan_correct.
    apply TM.atan_correct.
    apply TM.exp_correct.
    apply TM.ln_correct.
    apply TM.power_int_correct.
    apply TM.nearbyint_correct.
  + generalize (IHl n1) (IHl n2).
    destruct bo.
    apply TM.add_correct.
    apply TM.sub_correct.
    apply TM.mul_correct.
    apply TM.div_correct.
Qed.

Theorem eval_correct_ext :
  forall prec deg prog bounds n yi,
  I.extension
    (Xbind (fun x => nth n (eval_ext prog (Xreal x :: map xreal_from_bp bounds)) Xnan))
    (fun b => TM.eval (prec,deg) (nth n (eval prec deg yi prog (TM.var :: map (fun b => TM.const (interval_from_bp b)) bounds)) TM.dummy) yi b).
Proof.
intros prec deg prog bounds n yi xi x Hx.
pose (f x := nth n (eval_ext prog (Xreal x :: map xreal_from_bp bounds)) Xnan).
pose (ft := nth n (eval prec deg yi prog (TM.var :: map (fun b => TM.const (interval_from_bp b)) bounds)) TM.dummy).
apply (@TM.eval_correct (prec,deg) yi ft f) with (2 := Hx).
now apply eval_correct_aux.
Qed.

End TaylorValuator.

End IntervalAlgos.
