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

Require Import Reals List ZArith Psatz.
Require Import Coquelicot.Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
Require Import Interval_integral.
Require Import Interval_bisect.
Require Import coquelicot_compl.
Require Import bertrand.
Require Import various_integrals.

Module IntervalTactic (F : FloatOps with Definition even_radix := true).

Inductive interval_tac_parameters :=
  | i_prec : nat -> interval_tac_parameters
  | i_bisect : R -> interval_tac_parameters
  | i_bisect_diff : R -> interval_tac_parameters
  | i_bisect_taylor : R -> nat -> interval_tac_parameters
  | i_depth : nat -> interval_tac_parameters
  | i_integral_depth : nat -> interval_tac_parameters
  | i_integral_prec : nat -> interval_tac_parameters
  | i_integral_width : Z -> interval_tac_parameters
  | i_integral_deg : nat -> interval_tac_parameters
  | i_native_compute : interval_tac_parameters
  | i_delay : interval_tac_parameters.

Module Private.

Module I := FloatIntervalFull F.
Module Fext := FloatExt F.
Module A := IntervalAlgos I.
Module Int := IntegralTactic F I.
Module Int' := IntegralTaylor I.
Module Bertrand := BertrandInterval F I.
Module ExpNIntegral := ExpNInterval F I.

Ltac get_float t :=
  let get_float_rational s n d :=
    let rec aux t :=
      match t with
      | xO xH => xH
      | xO ?v =>
        let w := aux v in
        constr:(Pos.succ w)
      end in
    let e := aux d in
    eval vm_compute in (F.fromF (@Interval_definitions.Float F.radix s n (Zneg e))) in
  let get_float_bpow s n d :=
    eval vm_compute in (F.fromF (@Interval_definitions.Float F.radix s n d)) in
  let get_float_integer s t :=
    let rec aux m e :=
      match m with
      | xO ?v =>
        let u := constr:(Z.succ e) in
        aux v u
      | _ => constr:((m, e))
      end in
    let v := aux t Z0 in
    match v with
    | (?m, ?e) => eval vm_compute in (F.fromF (@Interval_definitions.Float F.radix s m e))
    end in
  match t with
  | 0%R => F.zero
  | (IZR (Zneg ?n) * / IZR (Zpos ?d))%R => get_float_rational true n d
  | (IZR (Zpos ?n) * / IZR (Zpos ?d))%R => get_float_rational false n d
  | (IZR (Zneg ?n) / IZR (Zpos ?d))%R => get_float_rational true n d
  | (IZR (Zpos ?n) / IZR (Zpos ?d))%R => get_float_rational false n d
  | (IZR (Zneg ?n) * bpow radix2 ?d)%R => get_float_bpow true n d
  | (IZR (Zpos ?n) * bpow radix2 ?d)%R => get_float_bpow false n d
  | IZR (Zneg ?n) => get_float_integer true n
  | IZR (Zpos ?n) => get_float_integer false n
  | _ => false
  end.

Lemma Rabs_contains :
  forall f v,
  contains (I.convert (I.bnd (F.neg f) f)) (Xreal v) ->
  match F.toF f with
  | Interval_definitions.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => True
  end.
Proof.
intros f v (H1,H2).
generalize (F.real_correct f).
case_eq (F.toF f) ; try easy.
intros [|] m e Hf _.
exact I.
rewrite F.neg_correct in H1.
rewrite <- F.toF_correct in H1, H2.
rewrite Hf in H1, H2.
simpl in H1, H2.
now apply Rabs_def1_le.
Qed.

Lemma Rabs_contains_rev :
  forall f v,
  match F.toF f with
  | Interval_definitions.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => False
  end ->
  contains (I.convert (I.bnd (F.neg f) f)) (Xreal v).
Proof.
intros f v.
generalize (F.real_correct f).
case_eq (F.toF f) ; try easy.
intros [|] m e Hf _ H.
easy.
destruct (Rabs_def2_le _ _ H) as (H1,H2).
split.
rewrite F.neg_correct.
now rewrite <- F.toF_correct, Hf.
rewrite <- F.toF_correct.
now rewrite Hf.
Qed.

Lemma contains_eval :
  forall prec prog bounds n,
  contains (I.convert (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai)) (Xreal (nth n (eval_real prog (map A.real_from_bp bounds)) 0)).
Proof.
intros prec prog bounds n.
set (xi := nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
unfold xi.
replace (map Xreal (map A.real_from_bp bounds)) with (map A.xreal_from_bp bounds).
apply A.BndValuator.eval_correct.
clear.
induction bounds.
easy.
simpl.
rewrite IHbounds.
now case a.
Qed.

Lemma contains_eval_arg :
  forall prec prog bounds n xi x,
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (nth n (A.BndValuator.eval prec prog (xi :: map A.interval_from_bp bounds)) I.nai)) (Xreal (nth n (eval_real prog (x :: map A.real_from_bp bounds)) 0)).
Proof.
intros prec prog bounds n xi x Hx.
apply (contains_eval prec prog (A.Bproof x xi Hx :: bounds)).
Qed.

Lemma contains_bound_lr :
  forall x prec proga boundsa na progb boundsb nb,
  Rle (nth na (eval_real proga (map A.real_from_bp boundsa)) 0) x /\
  Rle x (nth nb (eval_real progb (map A.real_from_bp boundsb)) 0) ->
  contains (I.convert (I.meet (I.upper_extent (nth na (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai)) (I.lower_extent (nth nb (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai)))) (Xreal x).
Proof.
intros x prec proga boundsa na progb boundsb nb [Hx1 Hx2].
apply I.meet_correct.
apply I.upper_extent_correct with (2 := Hx1).
apply contains_eval.
apply I.lower_extent_correct with (2 := Hx2).
apply contains_eval.
Qed.

Lemma contains_bound_lr' :
  forall x prec proga boundsa na progb boundsb nb,
  let ia := nth na (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let ib := nth nb (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai in
  I.upper_bounded ia = true ->
  I.lower_bounded ib = true ->
  contains (I.convert (I.bnd (I.upper ia) (I.lower ib))) (Xreal x) ->
  Rle (nth na (eval_real proga (map A.real_from_bp boundsa)) 0) x /\
  Rle x (nth nb (eval_real progb (map A.real_from_bp boundsb)) 0).
Proof.
intros x prec proga boundsa na progb boundsb nb.
generalize (contains_eval prec proga boundsa na) (contains_eval prec progb boundsb nb).
case (nth nb (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai).
easy.
case (nth na (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai).
easy.
intros la ua lb ub [_ Hua] [Hlb _] ia ib.
generalize (I.upper_bounded_correct ia) (I.lower_bounded_correct ib).
unfold ia, ib.
simpl.
case F.real.
2: easy.
case F.real.
2: easy.
intros Ha Hb _ _.
specialize (Ha eq_refl).
specialize (Hb eq_refl).
revert Hua.
destruct Ha as [-> _].
revert Hlb.
destruct Hb as [-> _].
intros H1b H1a [H2 H3].
split.
now apply Rle_trans with (1 := H1a).
now apply Rle_trans with (2 := H1b).
Qed.

Lemma contains_bound_l :
  forall x prec prog bounds n,
  Rle (nth n (eval_real prog (map A.real_from_bp bounds)) 0) x ->
  contains (I.convert (I.upper_extent (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai))) (Xreal x).
Proof.
intros x prec prog bounds n Hx.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
simpl.
intros l _ [Hl _].
split.
destruct (F.toX l) as [|lr].
exact I.
now apply Rle_trans with (2 := Hx).
now rewrite F.nan_correct.
Qed.

Lemma contains_bound_l' :
  forall x prec prog bounds n,
  let i := nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai in
  I.upper_bounded i = true ->
  contains (I.convert (I.bnd (I.upper i) F.nan)) (Xreal x) ->
  Rle (nth n (eval_real prog (map A.real_from_bp bounds)) 0) x.
Proof.
intros x prec prog bounds n.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
intros l u [_ Hu].
generalize (I.upper_bounded_correct (Interval_interval_float.Ibnd l u)).
simpl.
case F.real.
2: easy.
intros H _.
specialize (H eq_refl).
revert Hu.
destruct H as [-> _].
intros H1 [H2 H3].
now apply Rle_trans with (1 := H1).
Qed.

Lemma contains_bound_r :
  forall x prec prog bounds n,
  Rle x (nth n (eval_real prog (map A.real_from_bp bounds)) 0) ->
  contains (I.convert (I.lower_extent (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai))) (Xreal x).
Proof.
intros x prec prog bounds n Hx.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
simpl.
intros _ u [_ Hu].
split.
now rewrite F.nan_correct.
destruct (F.toX u) as [|ur].
exact I.
now apply Rle_trans with (1 := Hx).
Qed.

Lemma contains_bound_r' :
  forall x prec prog bounds n,
  let i := nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai in
  I.lower_bounded i = true ->
  contains (I.convert (I.bnd F.nan (I.lower i))) (Xreal x) ->
  Rle x (nth n (eval_real prog (map A.real_from_bp bounds)) 0).
Proof.
intros x prec prog bounds n.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
intros l u [Hl _].
generalize (I.lower_bounded_correct (Interval_interval_float.Ibnd l u)).
simpl.
case F.real.
2: easy.
intros H _.
specialize (H eq_refl).
revert Hl.
destruct H as [-> _].
intros H1 [H2 H3].
now apply Rle_trans with (2 := H1).
Qed.

Lemma contains_bound_ar :
  forall x prec prog bounds n,
  Rle (Rabs x) (nth n (eval_real prog (map A.real_from_bp bounds)) 0) ->
  let xi := I.lower_extent (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai) in
  contains (I.convert (I.meet (I.neg xi) xi)) (Xreal x).
Proof.
intros x prec prog bounds n Hx.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
simpl.
intros _ u [_ Hu].
rewrite 4!F.real_correct.
rewrite 2!F.neg_correct.
rewrite F.nan_correct.
simpl.
case_eq (F.toX u).
intros _.
simpl.
now rewrite F.nan_correct.
simpl.
intros ur Hur.
rewrite F.neg_correct.
rewrite Hur in Hu.
rewrite Hur.
simpl.
apply Rabs_def2_le.
now apply Rle_trans with (1 := Hx).
Qed.

Lemma contains_bound_ar' :
  forall x prec prog bounds n,
  let i := nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai in
  I.lower_bounded i = true ->
  contains (I.convert (let l := I.lower i in I.bnd (F.neg l) l)) (Xreal x) ->
  Rle (Rabs x) (nth n (eval_real prog (map A.real_from_bp bounds)) 0).
Proof.
intros x prec prog bounds n.
generalize (contains_eval prec prog bounds n).
case (nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
easy.
intros l u [Hl _].
generalize (I.lower_bounded_correct (Interval_interval_float.Ibnd l u)).
simpl.
case F.real.
2: easy.
intros H _.
specialize (H eq_refl).
revert Hl.
destruct H as [Hl _].
rewrite F.neg_correct.
rewrite Hl.
intros H1 [H2 H3].
apply Rle_trans with (2 := H1).
apply Rabs_le.
now split.
Qed.

Section IntegralProg.

Variable prec : F.precision.
Variables prog proga progb : list term.
Variables bounds boundsa boundsb : list A.bound_proof.

Let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0.
Let iF := (fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai).

Variable estimator : I.type -> I.type -> I.type.

Definition correct_estimator :=
  forall ia ib, Int.integralEstimatorCorrect f (estimator ia ib) ia ib.

Let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0.
Let b := nth 0 (eval_real progb (map A.real_from_bp boundsb)) 0.
Let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai.
Let ib := nth 0 (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai.

Lemma integral_epsilon_correct :
  forall (depth : nat) epsilon,
  let i := Int.integral_interval prec estimator depth ia ib epsilon in
  correct_estimator ->
  (I.convert i <> Inan -> ex_RInt f a b) /\
  contains (I.convert i) (Xreal (RInt f a b)).
Proof.
move => depth epsilon i base_case.
case H: (I.convert i).
  by split.
rewrite -H.
case: (Int.integral_interval_correct prec f estimator depth ia ib epsilon base_case a b).
- exact: contains_eval.
- exact: contains_eval.
- by rewrite H.
intros I [If Cf].
split.
move => _.
by exists I.
by rewrite (is_RInt_unique _ _ _ _ If).
Qed.

End IntegralProg.

Section InfiniteIntegralProg.

(* g x = f x * x^alpha * (ln x)^beta *)

Variable prec : F.precision.
Variables prog_f prog_g proga progb : list term.
Variables bounds_f bounds_g boundsa boundsb : list A.bound_proof.

Let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0.
Let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0.

Let iF := (fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai).
Let iG := (fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai).

Variable estimator : I.type -> I.type -> I.type.

Let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0.
Let b := nth 0 (eval_real progb (map A.real_from_bp boundsb)) 0.
Let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai.
Let ib := nth 0 (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai.


Variable estimator_infty : I.type -> I.type.

Definition correct_estimator_infty :=
  forall ia, Int.integralEstimatorCorrect_infty g (estimator_infty ia) ia.

Lemma integral_epsilon_infty_correct :
  forall (depth : nat) epsilon,
  let i := Int.integral_interval_infty prec estimator estimator_infty depth ia epsilon in
  (correct_estimator prog_g bounds_g estimator) ->
  correct_estimator_infty ->
  (I.convert i <> Inan -> exists I, is_RInt_gen g (at_point a) (Rbar_locally p_infty) I /\
  contains (I.convert i) (Xreal I)).
Proof.
move => depth epsilon i Hc Hc_infty.
case H: (I.convert i) => [| l u]// _ .
rewrite -H.
apply: (Int.integral_interval_infty_correct prec g estimator estimator_infty depth ia epsilon Hc Hc_infty).
- exact: contains_eval.
- by rewrite H.
Qed.

Lemma integral_epsilon_infty_correct_RInt_gen :
  forall (depth : nat) epsilon,
  let i := Int.integral_interval_infty prec estimator estimator_infty depth ia epsilon in
  (correct_estimator prog_g bounds_g estimator) ->
  correct_estimator_infty ->
  (I.convert i <> Inan -> ex_RInt_gen g (at_point a) (Rbar_locally p_infty) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty)))).
Proof.
move => depth epsilon i Hc Hc_infty HnotInan.
case: (integral_epsilon_infty_correct depth epsilon Hc Hc_infty HnotInan) => I [H1 H2].
split.
  by exists I.
suff -> : RInt_gen g (at_point a) (Rbar_locally p_infty) = I; first by [].
by apply is_RInt_gen_unique. (* apply: does not work *)
Qed.

End InfiniteIntegralProg.

Section SingIntegralProg.

Variable prec : F.precision.
Variables prog_f prog_g proga progb : list term.
Variables bounds_f bounds_g boundsa boundsb : list A.bound_proof.

Let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0.
Let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0.

Let iF := (fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai).
Let iG := (fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai).

Variable estimator : I.type -> I.type -> I.type.

Let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0.
Let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai.

Variable estimator_sing : I.type -> I.type.

Definition correct_estimator_sing sing :=
  forall ia, Int.integralEstimatorCorrect_atsing g (estimator_sing ia) ia sing.

Lemma integral_epsilon_sing_correct :
  forall (depth : nat) epsilon sing (iSing : I.type),
  let i := Int.integral_interval_sing prec estimator estimator_sing depth ia iSing epsilon in
  (correct_estimator prog_g bounds_g estimator) ->
  correct_estimator_sing sing ->
  (I.convert i <> Inan -> exists I, is_RInt_gen g (at_right sing) (at_point a) I /\
  contains (I.convert i) (Xreal I)).
Proof.
move => depth epsilon sing iSing i Hc Hc_sing.
case H: (I.convert i) => [| l u]// _ .
rewrite -H.
apply: (Int.integral_interval_sing_correct prec g estimator estimator_sing depth ia epsilon sing iSing (* Hc Hc_sing *)).
- exact: Hc_sing.
- exact: Hc.
- apply: contains_eval.
- by rewrite H.
Qed.

Lemma integral_epsilon_sing_correct_RInt_gen :
  forall (depth : nat) epsilon sing iSing,
  let i := Int.integral_interval_sing prec estimator estimator_sing depth ia iSing epsilon in
  (correct_estimator prog_g bounds_g estimator) ->
  correct_estimator_sing sing ->
  (I.convert i <> Inan -> ex_RInt_gen g (at_right sing) (at_point a) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_right sing) (at_point a)))).
Proof.
move => depth epsilon sing iSing i Hc Hc_sing HnotInan.
case: (integral_epsilon_sing_correct depth epsilon sing iSing Hc Hc_sing HnotInan) => I [H1 H2].
split.
  by exists I.
suff -> : RInt_gen g (at_right sing) (at_point a) = I; first by [].
by apply is_RInt_gen_unique. (* apply: does not work *)
Qed.

End SingIntegralProg.

(* To reorganize *)
Section Helper.

Lemma integralEstimatorCorrect_infty_ext f1 f2 (Heq : forall x, f1 x = f2 x) (estimator1 : I.type) ia1 :
  Int.integralEstimatorCorrect_infty f1 estimator1 ia1 ->
  Int.integralEstimatorCorrect_infty f2 estimator1 ia1.
Proof.
rewrite /Int.integralEstimatorCorrect_infty => Hf1.
move => a1 Hia1 HnotInan.
have := (Hf1 a1 Hia1 HnotInan).
case => I [HI Hcont].
exists I.
split => // .
  apply: (is_RInt_gen_ext f1 f2) => // .
  exact: filter_forall => bnd x _.
Qed.

Lemma integralEstimatorCorrect_atsing_ext f1 f2 (Heq : forall x, f1 x = f2 x) (estimator1 : I.type) ia1 sing :
  Int.integralEstimatorCorrect_atsing f1 estimator1 ia1 sing ->
  Int.integralEstimatorCorrect_atsing f2 estimator1 ia1 sing.
Proof.
rewrite /Int.integralEstimatorCorrect_atsing => Hf1.
move => a1 Hia1 HnotInan.
have := (Hf1 a1 Hia1 HnotInan).
case => I [HI Hcont].
exists I.
split => // .
  apply: (is_RInt_gen_ext f1 f2) => // .
  exact: filter_forall => bnd x _.
Qed.

End Helper.

Section Correction_lemmas_integral_for_tactic.

(* this lemma has been isolated and generalized so that it could be
reused in the case of integralEstimatorCorrect_infty *)
Lemma taylor_correct_estimator_general :
  forall prec deg prog bounds (* ia ib a b *),
    (* contains (I.convert ia) (Xreal a) -> *)
    (* contains (I.convert ib) (Xreal b) -> *)
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let iF'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds)
) A.TaylorValuator.TM.dummy in
  let iF' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iF'' xi) in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iF (iF' xi) xi fa fb in
correct_estimator prog bounds estimator.
Proof.
move => prec deg prog bounds (* ia ib a b Hconta Hcontb *) Hf f iF'' iF' iF estimator.
revert Hf; clear -f; move=> Hf.
move => ia ib a b Hconta Hcontb Hint.
have Hfint: ex_RInt f a b.
  apply: (A.BndValuator.ex_RInt_eval prec _ _ _ _ _ (I.join ia ib)).
  + by [].
  + move => x.
    apply: contains_connected.
    rewrite /Rmin; case: (Rle_dec a b) => _.
    * by apply : (I.join_correct ia ib (Xreal a)); left.
    * by apply : (I.join_correct ia ib (Xreal b)); right.
    rewrite /Rmax /=; case: (Rle_dec a b) => _.
    * by apply : (I.join_correct ia ib (Xreal b)); right.
    * by apply : (I.join_correct ia ib (Xreal a)); left.
  + move: Hint.
    rewrite /estimator /Int'.taylor_integral_naive_intersection.
    case E: I.mul => [//|l u] _.
    rewrite -/(iF (I.join ia ib)).
    move /(I.mul_propagate_r prec (I.sub prec ib ia)).
    by rewrite E.
exists (RInt f a b).
split.
  exact: RInt_correct.
apply: (Int'.taylor_integral_naive_intersection_correct prec f) => // .
  move => x xi Hxi.
  by apply (contains_eval_arg prec prog bounds 0).
rewrite /f.
set iab := I.join ia ib.
have: (Int'.TM.TMI.i_validTM (Int'.iX0 iab) (Int'.iX iab) (iF' iab)
    (fun x => nth 0 (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)) Xnan)).
  have H := (@A.TaylorValuator.TM.get_tm_correct _ _ _ (fun x => nth 0 (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)) Xnan) _).
  apply H.
  apply: A.TaylorValuator.eval_correct_aux.
    by exists a; apply: I.join_correct; left.
rewrite /Int'.TM.TMI.i_validTM.
case: (I.convert (taylor_model_int_sharp.error (iF' iab))).
  by case.
move => l u [H1 H0 H2 H3 H4].
split => //.
move => x0 Hx0.
case: (H4 x0 Hx0) => {H4} [Q H4 H4'].
exists Q => //.
move => x Hx.
move: (H1 x Hx) (H4' x Hx) => {H1 H4'}.
set bx := A.Bproof x iab Hx.
rewrite -[_::map _ _]/(map _ (bx::_)).
rewrite -[_::map _ _]/(map A.real_from_bp (bx::_)).
case E: (nth 0 _ Xnan) => H.
  by move: (H eq_refl).
rewrite -[Xreal (_ - _)]/(Xsub (Xreal _) (Xreal _)).
rewrite -E.
rewrite (_ : map A.xreal_from_bp (bx :: bounds) = (map Xreal (map A.real_from_bp (bx :: bounds)))).
exact: (xreal_to_real (fun x => contains _ (Xsub x (Xreal _))) (fun x => contains _ (Xreal (x - _)))).
rewrite map_map.
apply map_ext.
by case.
  by apply: I.join_correct; left.
  by apply: I.join_correct; right.
Qed.


Lemma taylor_integral_naive_intersection_epsilon_correct :
  forall prec deg depth proga boundsa progb boundsb prog bounds epsilon,
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let iF'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds)
) A.TaylorValuator.TM.dummy in
  let iF' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iF'' xi) in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let b := nth 0 (eval_real progb (map A.real_from_bp boundsb)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let ib := nth 0 (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iF (iF' xi) xi fa fb in
  let i := Int.integral_interval prec estimator depth ia ib epsilon in
  (I.convert i <> Inan -> ex_RInt f a b) /\
  contains (I.convert i) (Xreal (RInt f a b)).
Proof.
move => prec deg depth proga boundsa progb boundsb prog bounds epsilon Hf f iF'' iF' iF a b ia ib estimator i.
apply: integral_epsilon_correct.
exact: (taylor_correct_estimator_general).
Qed.


Section Correction_lemmas_integral_infinity.

Import Bertrand.

Lemma remainder_correct_bertrand :
  forall prec prog bounds ia alpha beta,
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
    if Fext.le (F.fromZ 1) (I.lower ia) then
      if (I.bounded (fi (I.upper_extent ia))) then
        I.mul prec (fi (I.upper_extent ia))
              (Bertrand.f_int_fast prec ia alpha beta)
      else I.nai
      else I.nai in
  (alpha < -1)%Z ->
  Int.integralEstimatorCorrect_infty (fun x => f x * (powerRZ x alpha * (pow (ln x) beta))) (estimator ia) ia.
Proof.
intros prec prog bounds ia alpha beta Hf f fi estimator Halpha (* Hbnded *) a Ha.
unfold estimator.
case Ha1': Fext.le ; last by rewrite I.nai_correct.
have {Ha1'} Ha1: 1 <= a.
  apply Fext.le_correct in Ha1'.
  revert Ha1'.
  rewrite F.fromZ_correct.
  rewrite I.lower_correct.
  destruct (I.convert ia) as [|la ua].
  easy.
  destruct la as [|la].
  easy.
  intros H.
  exact: Rle_trans H (proj1 Ha).
case Hbnded : (I.bounded _) => // .
intros HnotInan.
apply: Int.integral_interval_mul_infty.
- exact: Ha.
- intros x Hx.
  apply contains_eval_arg.
  exact: I.upper_extent_correct Ha Hx.
- exact: Hbnded.
- intros x Hx.
  apply: (A.BndValuator.continuous_eval prec _ _ 0 (I.upper_extent ia)) => //.
  exact: I.upper_extent_correct Ha Hx.
  intros H.
  apply Int.bounded_ex in Hbnded.
  destruct Hbnded as [l [u H']].
  now rewrite H' in H.
- move => x Hx.
  apply: continuous_mult.
  apply: ex_derive_continuous.
  apply: ex_derive_powerRZ; right; lra.
  apply: ex_derive_continuous.
  apply: ex_derive_pow.
  eexists; apply: coquelicot_compl.is_derive_ln; lra.
- intros x Hax.
  apply Rmult_le_pos_pos.
  apply powerRZ_le.
  apply: Rlt_le_trans Hax.
  exact: Rlt_le_trans Rlt_0_1 Ha1.
  apply pow_le.
  rewrite <- ln_1.
  apply ln_le.
  exact Rlt_0_1.
  exact: Rle_trans Ha1 Hax.
- apply: f_lim_correct Halpha.
  exact: Rlt_le_trans Rlt_0_1 Ha1.
- apply (f_int_fast_correct prec a ia Ha alpha beta).
  exact: Rlt_le_trans Rlt_0_1 Ha1.
  exact: Zlt_not_eq.
Qed.

(* we need two functions: f, and g(x) := f(x) * x^alpha * ln(x)^beta *)
Lemma remainder_correct_bertrand_tactic :
  forall prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon alpha beta,
  no_floor_prog prog_f = true ->
  no_floor_prog prog_g = true ->
  let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0 in
  let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0 in
  let iG'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog_g (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds_g)
) A.TaylorValuator.TM.dummy in
  let iG' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iG'' xi) in
  let iG := fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let estimator_infty := fun ia =>
    if Fext.le (F.fromZ 1) (I.lower ia) then
      if (I.bounded (iF (I.upper_extent ia))) then
        I.mul prec (iF (I.upper_extent ia))
              (Bertrand.f_int_fast prec ia alpha beta)
      else I.nai
    else I.nai in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iG (iG' xi) xi fa fb in
  let i := if (alpha <? -1)%Z then
             Int.integral_interval_infty prec estimator estimator_infty depth ia epsilon else I.nai in
  (forall x,  g x = f x * (powerRZ x alpha * ln x ^ beta)) ->
  (I.convert i <> Inan ->
  (ex_RInt_gen g (at_point a) (Rbar_locally p_infty))) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
Proof.
move => prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon alpha beta Hf Hg f g iG'' iG' iG iF a ia estimator_infty estimator.
case Halphab : (alpha <? -1)%Z; last by rewrite /=; split.
have {Halphab} Halpha: (alpha < -1)%Z by rewrite -Z.ltb_lt.
move => i Hfg.
suff: I.convert i <> Inan -> (ex_RInt_gen g (at_point a) (Rbar_locally p_infty)) /\
  contains (I.convert i)
    (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
  move => H.
  case Hi: (I.convert i) => [|l u]; first by split.
  rewrite -Hi; split => [HnotInan|]; first by apply H.
  apply H; by rewrite Hi.
apply: integral_epsilon_infty_correct_RInt_gen => // .
  - apply: taylor_correct_estimator_general.
  - by [].
  - rewrite /correct_estimator_infty.
    move => ia0.
suff:  Int.integralEstimatorCorrect_infty
             (fun x : R => f x * (powerRZ x alpha * ln x ^ beta))
             (estimator_infty ia0) ia0.
      apply: integralEstimatorCorrect_infty_ext.
      by move => x; rewrite -Hfg.
    by apply remainder_correct_bertrand.
Qed.

(* Not sure if useful, definitely overkill for exp(-x) but maybe this can gain us a lot of time for future 'kernels'? *)
Lemma remainder_correct_generic_fun_at_infty (kernel : R -> R) (kernelInt : R -> R) iKernelInt
      (pre_cond : (R -> R) -> R -> Prop)
      (dom_constant_sign : R -> Prop)
      (test : (I.type -> I.type) -> I.type -> bool)
      (Hcont : forall a x f, pre_cond f a -> a <= x -> continuous kernel x)
      (Hint : forall a f, (pre_cond f a) -> is_RInt_gen kernel (at_point a) (Rbar_locally p_infty) (kernelInt a))
      (Hint_iExt : forall a ia, contains (I.convert ia) (Xreal a) -> contains (I.convert (iKernelInt ia)) (Xreal (kernelInt a)))
      (Hpcimpcs : forall a f x, pre_cond f a -> a <= x -> dom_constant_sign x)
      (* ultimately we want constant_sign here *)
      (Hpos : forall x, dom_constant_sign x -> 0 <= kernel x)
      (H_test : forall f fi ia a,
                  (forall x ix, contains (I.convert ix) (Xreal x) -> contains (I.convert (fi ix)) (Xreal (f x)))  ->
                  contains (I.convert ia) (Xreal a) ->
                  test fi ia ->
                  pre_cond f a)
:
  forall prec prog bounds ia,
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
      if test fi ia then
      if (I.bounded (fi (I.upper_extent ia))) then
        I.mul prec (fi (I.upper_extent ia)) (iKernelInt ia)
      else I.nai
      else I.nai in
  Int.integralEstimatorCorrect_infty (fun x => f x * kernel x) (estimator ia) ia.
Proof.
intros prec prog bounds ia Hf f fi estimator (* Hbnded *) a Ha.
unfold estimator.
case Htest: test; last by rewrite I.nai_correct.
have Hprec_cond : pre_cond f a.
  apply: H_test Ha Htest => x ix Hix.
  exact: contains_eval_arg Hix.
case Hbnded : (I.bounded _) => // .
intros HnotInan.
apply: Int.integral_interval_mul_infty.
- exact: Ha.
- intros x Hx.
  apply contains_eval_arg.
  exact: I.upper_extent_correct Ha Hx.
- exact: Hbnded.
- intros x Hx.
  apply: (A.BndValuator.continuous_eval prec _ _ 0 (I.upper_extent ia)) => //.
  exact: I.upper_extent_correct Ha Hx.
  intros H.
  apply Int.bounded_ex in Hbnded.
  destruct Hbnded as [l [u H']].
  now rewrite H' in H.
- move => x Hx.
  by apply: Hcont; first apply Hprec_cond.
- intros x Hax.
  by apply: Hpos; apply: Hpcimpcs; first apply: Hprec_cond.
- apply: Hint; exact: Hprec_cond.
- exact: Hint_iExt => // .
Qed.

Lemma remainder_correct_exp_at_infty :
  forall prec prog bounds ia lam iLam,
  no_floor_prog prog = true ->
  let test _ _ := true in
  let iKernelInt ia iLam := ExpNIntegral.ExpN prec ia iLam in
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
      if test fi ia then
      if (I.bounded (fi (I.upper_extent ia))) then
        I.mul prec (fi (I.upper_extent ia)) (iKernelInt ia iLam)
      else I.nai
      else I.nai in
  lam > 0 ->
  contains (I.convert iLam) (Xreal lam) ->
  Int.integralEstimatorCorrect_infty (fun x => f x * expn lam x) (estimator ia) ia.
Proof.
move => prec prog bounds ia lam iLam Hf test iKernelInt f fi estimator Hlam Hcontains.
apply (remainder_correct_generic_fun_at_infty (fun x => expn lam x)
                (fun a => exp (-(lam * a)) / lam) _ (fun _ _ => 0 < lam) (fun x => True)).
- by move => a x _ _ Hax; apply: continuous_expn.
- move => a _ Hlam'; exact: is_RInt_gen_exp_infty.
- move => a ia0 H; apply: ExpNIntegral.ExpN_correct => //; lra.
- by [].
- move => x; move: (exp_pos (-(lam * x))) ;rewrite /expn; lra.
- by [].
- by [].
Qed.

Lemma remainder_correct_expn_tactic prec deg depth proga boundsa
prog_f prog_g prog_lam bounds_lam bounds_f bounds_g epsilon:
  no_floor_prog prog_f = true ->
  no_floor_prog prog_g = true ->
  let lam := nth 0 (eval_real prog_lam (map A.real_from_bp bounds_lam)) 0 in
  let iLam := nth 0 (A.BndValuator.eval prec prog_lam (map A.interval_from_bp bounds_lam)) I.nai in
  let test _ _ := true in
  let iKernelInt ia iLam := ExpNIntegral.ExpN prec ia iLam in
  let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0 in
  let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0 in
  let iG'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog_g (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds_g)
) A.TaylorValuator.TM.dummy in
  let iG' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iG'' xi) in
  let iG := fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let estimator_infty := fun ia =>
      if test iF ia then
      if (I.bounded (iF (I.upper_extent ia))) then
        I.mul prec (iF (I.upper_extent ia)) (iKernelInt ia iLam)
      else I.nai
      else I.nai in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iG (iG' xi) xi fa fb in
  let i :=
      if Fext.lt (F.fromZ 0) (I.lower iLam) then
      Int.integral_interval_infty prec estimator estimator_infty depth ia epsilon else I.nai in
  (forall x,  g x = f x * (exp (-(lam * x)))) ->
  (I.convert i <> Inan ->
  (ex_RInt_gen g (at_point a) (Rbar_locally p_infty))) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
Proof.
move => Hf Hg lam iLam test iKernelInt f g iG'' iG' iG iF a ia estimator_infty estimator.
move => i Hfg.
suff: I.convert i <> Inan -> (ex_RInt_gen g (at_point a) (Rbar_locally p_infty)) /\
  contains (I.convert i)
    (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
  move => H.
  case Hi: (I.convert i) => [|l u]; first by split.
  rewrite -Hi; split => [HnotInan|]; first by apply H.
  apply H; by rewrite Hi.
case Hlam : (Fext.lt (F.fromZ 0) (I.lower iLam)); last first.
  by rewrite /i Hlam I.nai_correct.
have Hcontains : contains (I.convert iLam) (Xreal lam).
  exact: contains_eval.
have lt0lam : 0 < lam.
  move: Hcontains.
  apply Fext.lt_correct in Hlam; rewrite F.fromZ_correct in Hlam.
  rewrite I.lower_correct in Hlam; move: Hlam.
  case HiLam: (I.convert iLam) => [|laml lamu] //= .
  by case: laml HiLam => [|laml] // HiLam; lra.
rewrite /i. case: ifP => // H.
apply: integral_epsilon_infty_correct_RInt_gen => // .
  - apply: taylor_correct_estimator_general.
  - by [].
  - rewrite /correct_estimator_infty.
    move => ia0.
    suff:  Int.integralEstimatorCorrect_infty
             (fun x : R => f x * (expn lam x))
             (estimator_infty ia0) ia0.
      apply: integralEstimatorCorrect_infty_ext.
      by move => x; rewrite -Hfg.
    rewrite /Int.integralEstimatorCorrect_infty.
    by apply: remainder_correct_exp_at_infty.
Qed.


Lemma remainder_correct_bertrand_log_neg_at_infty prec prog bounds ia beta:
  no_floor_prog prog = true ->
  let test iF ia := Fext.lt (F.fromZ 1) (I.lower ia) && I.lower_bounded ia in
  let iKernelInt ia := I.neg (Bertrand.f_neg_int prec ia beta) in
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
      if test fi ia then
      if (I.bounded (fi (I.upper_extent ia))) then
        I.mul prec (fi (I.upper_extent ia)) (iKernelInt ia)
      else I.nai
      else I.nai in
  (2 <= beta)%nat ->
  Int.integralEstimatorCorrect_infty (fun x => f x * / (x * (ln x)^(S beta))) (estimator ia) ia.
Proof.
move => Hf test iKernelInt f fi estimator Hbeta.
apply (remainder_correct_generic_fun_at_infty (fun x => / (x * (ln x)^(S beta))) (fun a => - f_neg a beta) _ (fun _ x => 1 < x ) (fun x => 1 < x)).
- by move => a x Hx H1a Hax; apply: f_neg_continuous; try lra.
- move => a _ Ha; apply: f_neg_correct_RInt_gen_a_infty => // .
- (* ugly *)by rewrite SSR_leq.
- move => a ia0 H; rewrite /iKernelInt; apply: J.neg_correct.
  by apply: f_neg_int_correct => // .
- move => a _ x Ha Hx; lra.
- move => x Hx. apply: Rlt_le; apply: Rinv_0_lt_compat; apply: Rmult_lt_0_compat.
    by lra.
    suff Hln :0 < (ln x); first by apply: pow_lt.
    move: (ln_increasing 1 x); rewrite ln_1; lra.
- move => g ig ib b Hgext Hcontains.
  rewrite /test; case/andP.
  move/Fext.lt_correct; rewrite F.fromZ_correct.
  case: ib Hcontains => // l u /= ;case: (F.toX l) => // lr [] Hlrb _ lt1lr.
  by move => _; lra.
- by [].
Qed.


Lemma remainder_correct_log_neg_infty_tactic prec deg depth proga
boundsa prog_f prog_g bounds_f bounds_g epsilon beta:
  no_floor_prog prog_f = true ->
  no_floor_prog prog_g = true ->
  let test iF ia := Fext.lt (F.fromZ 1) (I.lower ia) && I.lower_bounded ia in
  let iKernelInt ia := I.neg (Bertrand.f_neg_int prec ia beta) in
  let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0 in
  let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0 in
  let iG'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog_g (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds_g)
) A.TaylorValuator.TM.dummy in
  let iG' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iG'' xi) in
  let iG := fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in

  let estimator_infty := fun ia =>
      if test iF ia then
      if (I.bounded (iF (I.upper_extent ia))) then
        I.mul prec (iF (I.upper_extent ia)) (iKernelInt ia)
      else I.nai
      else I.nai in

  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iG (iG' xi) xi fa fb in
  let i := if (Z.of_nat beta >? 1)%Z then Int.integral_interval_infty prec estimator estimator_infty depth ia epsilon else I.nai in
  (forall x,  g x = f x * / (x * (ln x)^(S beta))) ->
  (I.convert i <> Inan ->
  (ex_RInt_gen g (at_point a) (Rbar_locally p_infty))) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
Proof.
move => Hf Hg test iKernelInt f g iG'' iG' iG iF a ia estimator_infty estimator.
(* case Halphab : (alpha <? -1)%Z; last by rewrite /=; split. *)
case Hbeta : (Z.of_nat beta >? 1)%Z; last first.
  by move => H _; rewrite /=; split.
move => i Hfg.
suff: I.convert i <> Inan -> (ex_RInt_gen g (at_point a) (Rbar_locally p_infty)) /\
  contains (I.convert i)
    (Xreal (RInt_gen g (at_point a) (Rbar_locally p_infty))).
  move => H.
  case Hi: (I.convert i) => [|l u]; first by split.
  rewrite -Hi; split => [HnotInan|]; first by apply H.
  apply H; by rewrite Hi.
apply: integral_epsilon_infty_correct_RInt_gen => // .
  - apply: taylor_correct_estimator_general.
  - by [].
  - rewrite /correct_estimator_infty.
    move => ia0.
    suff:  Int.integralEstimatorCorrect_infty
             (fun x : R => f x * / (x * (ln x)^(S beta)))
             (estimator_infty ia0) ia0.
      apply: integralEstimatorCorrect_infty_ext.
      by move => x; rewrite -Hfg.
    apply: remainder_correct_bertrand_log_neg_at_infty.
  - by [].
  - rewrite /is_true in Hbeta.
    move: (proj1 (Z.gtb_lt _ _ ) Hbeta).
    by have -> : 1%Z = Z.of_nat 1 by []; rewrite -Nat2Z.inj_lt; lia.
Qed.

End Correction_lemmas_integral_infinity.

Section Correction_lemmas_integral_sing.

Lemma remainder_correct_sing :
  forall prec prog bounds ia alpha beta,
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
  if Fext.lt (F.fromZ 0) (I.lower ia) then
    if Fext.le (I.upper ia) (F.fromZ 1) then
      if (I.bounded (fi (I.join (I.fromZ 0) ia))) then
        I.mul prec (fi (I.join (I.fromZ 0) ia))
              (Bertrand.f0eps_int prec ia alpha beta)
      else I.nai
      else I.nai
      else I.nai in
  (alpha > -1)%Z ->
  Int.integralEstimatorCorrect_atsing (fun x => f x * (powerRZ x alpha * (pow (ln x) beta))) (estimator ia) ia 0.
Proof.
move => prec prog bounds ia alpha beta Hf f fi estimator Halpha.
move => epsilon Hia HnotInan.
rewrite /estimator.
case Hlt : Fext.lt; last first.
  by move: HnotInan; rewrite /estimator Hlt I.nai_correct.
case Hle : Fext.le; last first.
  by move: HnotInan; rewrite /estimator Hlt Hle I.nai_correct.
case Hbnded : I.bounded; last first.
  by move: HnotInan; rewrite /estimator Hlt Hle Hbnded I.nai_correct.
have Hepspos : 0 < epsilon.
    apply Fext.lt_correct in Hlt. move: Hlt.
    rewrite F.fromZ_correct.
    rewrite I.lower_correct.
    case Hia_ : (I.convert ia) => [|l_ia u_ia] //= .
    case: l_ia Hia_ => // r Hia_.
    by move: Hia; rewrite Hia_ /contains => [] []; lra.

  have lex1 x : 0 < x <= epsilon -> x <= 1.
  apply Fext.le_correct in Hle. move: Hle.
  rewrite F.fromZ_correct.
  rewrite I.upper_correct.
  case Hia_ : (I.convert ia) => [|l_ia u_ia] //= .
  case: u_ia Hia_ => // r Hia_.
  by move: Hia; rewrite Hia_ /contains => [] []; lra.

apply: (Int.integral_interval_mul_sing prec 0 epsilon (I.join (I.fromZ 0) ia) f) => // .
- by apply:I.join_correct; right; exact: Hia.
- move => x Hx.
  apply: contains_eval_arg.
  apply: (contains_connected _ 0 epsilon) => // .
  apply: I.join_correct; left; apply: I.fromZ_correct.
  apply: I.join_correct; right; exact: Hia.
- move => x Hx.
  apply: (A.BndValuator.continuous_eval prec _ _ _ (I.join (I.fromZ 0) ia)) => //.
  apply: (contains_connected _ 0 epsilon) => // .
  apply: I.join_correct; left; apply: I.fromZ_correct.
  apply: I.join_correct; right; exact: Hia.
  rewrite /estimator in HnotInan.
  rewrite  Hlt Hle Hbnded /fi in HnotInan.
  case Habs : I.convert => // .
    move: HnotInan; rewrite (I.mul_propagate_l prec) //.
- move => x Hx.
  apply: continuous_mult.
  apply: ex_derive_continuous.
  apply: ex_derive_powerRZ; right; lra.
  apply: ex_derive_continuous.
  apply: ex_derive_pow.
  by eexists; apply: coquelicot_compl.is_derive_ln; lra.
  case HEvenOdd: (Z.even (Z.of_nat beta)); [left| right] => x Hx.
  + apply: Rmult_le_pos_pos.
    apply: powerRZ_le; lra.
    apply: A.TaylorValuator.TM.TMI.ZEven_pow_le.
    by rewrite -Z.even_spec.
  + apply: Rmult_le_pos_neg.
    apply: powerRZ_le; lra.
    apply: Int'.TM.TMI.ZOdd_pow_le.
    by rewrite -Z.odd_spec Zodd_even_bool HEvenOdd.
  rewrite - ln_1; apply: ln_le.
  lra.
  exact: lex1.
  + apply: f0eps_lim_correct Hepspos.
    apply (IZR_lt (-1)); lia.
  apply: Bertrand.f0eps_correct => // .
    by lia.
Qed.

Lemma remainder_correct_sing_tactic :
  forall prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon alpha beta,
  no_floor_prog prog_f = true ->
  no_floor_prog prog_g = true ->
  let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0 in
  let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0 in
  let iG'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog_g (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds_g)
) A.TaylorValuator.TM.dummy in
  let iG' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iG'' xi) in
  let iG := fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let estimator_sing :=
fun ia =>
  if Fext.lt (F.fromZ 0) (I.lower ia) then
    if Fext.le (I.upper ia) (F.fromZ 1) then
      if (I.bounded (iF (I.join (I.fromZ 0) ia))) then
        I.mul prec (iF (I.join (I.fromZ 0) ia))
              (Bertrand.f0eps_int prec ia alpha beta)
      else I.nai
      else I.nai
      else I.nai in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iG (iG' xi) xi fa fb in
  let i := if (alpha >? -1)%Z then
             Int.integral_interval_sing prec estimator estimator_sing depth ia (I.fromZ 0) epsilon else I.nai in
  (forall x,  g x = f x * (powerRZ x alpha * ln x ^ beta)) ->
  (I.convert i <> Inan ->
  (ex_RInt_gen g (at_right 0) (at_point a))) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_right 0) (at_point a))).
Proof.
move => prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon alpha beta Hf Hg f g iG'' iG' iG iF a ia estimator_sing estimator.
case Halphab : (alpha >? -1)%Z; last by rewrite /=; split.
have {Halphab} Halpha: (alpha > -1)%Z by rewrite Zgt_is_gt_bool.
move => i Hfg.
suff: I.convert i <> Inan -> (ex_RInt_gen g (at_right 0) (at_point a)) /\
  contains (I.convert i)
    (Xreal (RInt_gen g (at_right 0) (at_point a))).
  move => H.
  case Hi: (I.convert i) => [|l u]; first by split.
  rewrite -Hi; split => [HnotInan|]; first by apply H.
  apply H; by rewrite Hi.
apply: integral_epsilon_sing_correct_RInt_gen => // .
  - apply: taylor_correct_estimator_general.
  - by [].
  - rewrite /correct_estimator_sing.
    move => ia0.
    suff:  Int.integralEstimatorCorrect_atsing
             (fun x : R => f x * (powerRZ x alpha * ln x ^ beta))
             (estimator_sing ia0) ia0 0.
      apply: integralEstimatorCorrect_atsing_ext.
      by move => x; rewrite -Hfg.
    exact: remainder_correct_sing.
Qed.

Lemma constant_sign_weaken (dsmall dbig : R -> Prop) f:
  (forall x, dsmall x -> dbig x) ->
  Int.constant_sign dbig f ->
  Int.constant_sign dsmall f.
Proof.
move => Hinc [Hpos|Hneg]; [left|right] => x Hsmall.
  by apply: Hpos; apply: Hinc.
by apply: Hneg; apply: Hinc.
Qed.

Lemma remainder_correct_generic_fun_at_right_singularity (kernel : R -> R) (kernelInt : R -> R) iKernelInt sing iSing
      (Hsing : contains (I.convert iSing) (Xreal sing))
      (pre_cond : (R -> R) -> R -> Prop)
      (Hpc_sing_a : forall f a, pre_cond f a -> sing < a)
      (dom_constant_sign : R -> Prop)
      (test : (I.type -> I.type) -> I.type -> bool)
      (Hcont : forall a x f, pre_cond f a -> sing < x <= a -> continuous kernel x)
      (Hint : forall a f, (pre_cond f a) -> is_RInt_gen kernel (at_right sing) (at_point a) (kernelInt a))
      (Hint_iExt : forall a ia, contains (I.convert ia) (Xreal a) -> contains (I.convert (iKernelInt ia)) (Xreal (kernelInt a)))
      (Hpcimpcs : forall a f x, pre_cond f a -> (sing < x <= a) -> dom_constant_sign x)
      (* ultimately we want constant_sign here *)
      (Hconstant_sign : Int.constant_sign dom_constant_sign kernel)
      (H_test : forall f fi ia a,
                  (forall x ix, contains (I.convert ix) (Xreal x) -> contains (I.convert (fi ix)) (Xreal (f x)))  ->
                  contains (I.convert ia) (Xreal a) ->
                  test fi ia ->
                  pre_cond f a) :
  forall prec prog bounds ia,
  no_floor_prog prog = true ->
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) 0 in
  let fi := fun xi => nth 0 (A.BndValuator.eval prec prog (xi::map A.interval_from_bp bounds)) I.nai in
  let estimator := fun ia =>
      if test fi ia then
      if (I.bounded (fi (I.join iSing ia))) then
        I.mul prec (fi (I.join iSing ia)) (iKernelInt ia)
      else I.nai
      else I.nai in
  Int.integralEstimatorCorrect_atsing (fun x => f x * kernel x) (estimator ia) ia sing.
Proof.
intros prec prog bounds ia Hf f fi estimator (* Hbnded *) a Ha.
unfold estimator.
case Htest: test; last by rewrite I.nai_correct.
have Hprec_cond : pre_cond f a.
  apply: H_test Ha Htest => x ix Hix.
  exact: contains_eval_arg Hix.
case Hbnded : (I.bounded _) => // .
intros HnotInan.
have HxSingIa x : sing <= x <= a ->  contains (I.convert (I.join iSing ia)) (Xreal x).
  apply: (contains_connected _ sing a) => // .
    by apply: I.join_correct; left.
  by apply: I.join_correct; right.
apply: Int.integral_interval_mul_sing => // .
- apply: Hpc_sing_a; exact: Hprec_cond.
- exact: Ha.
- intros x Hx.
  apply contains_eval_arg.
  exact: HxSingIa.
- intros x Hx.
  apply: (A.BndValuator.continuous_eval prec _ _ 0 (I.join iSing ia)) => //.
  exact: HxSingIa.
  intros H.
  apply Int.bounded_ex in Hbnded.
  destruct Hbnded as [l [u H']].
  now rewrite H' in H.
- move => x Hx.
  by apply: Hcont; first apply Hprec_cond.
  apply: (constant_sign_weaken _ dom_constant_sign) => // x Hx.
  by apply: Hpcimpcs => // ; first apply: Hprec_cond.
- apply: Hint; exact: Hprec_cond.
- exact: Hint_iExt => // .
Qed.

Lemma constant_sign_mult dom f g :
  Int.constant_sign dom f ->
  Int.constant_sign dom g ->
  Int.constant_sign dom (fun x => f x * g x).
Proof.
move => [Hf|Hf] [Hg|Hg]; [left| right| right | left] => x Hx;
have Hfx := (Hf x Hx);
have Hgx := (Hg x Hx).
- by apply: Rmult_le_pos_pos.
- by apply: Rmult_le_pos_neg.
- by apply: Rmult_le_neg_pos.
- by apply: Rmult_le_neg_neg.
Qed.

Lemma constant_sign_inv (dom : R -> Prop) f :
  (forall x, dom x -> f x <> 0) ->
  Int.constant_sign dom f ->
  Int.constant_sign dom (fun x => Rinv (f x)).
Proof.
move => Hfn0 [Hf|Hf];[left|right] => x Hx; have Hfx := (Hf x Hx); have Hfn0x := (Hfn0 x Hx).
- apply: Rlt_le; apply: Rinv_0_lt_compat; lra.
- apply: Rlt_le;apply: Rinv_lt_0_compat; lra.
Qed.

Lemma constant_sign_pow (dom : R -> Prop) f (beta : nat) :
  Int.constant_sign dom f ->
  Int.constant_sign dom (fun x => pow (f x) beta).
Proof.
move => [Hf|Hf].
  by left => x Hx; apply: pow_le; exact: Hf.
rewrite -(ssrnat.odd_double_half beta).
case: (ssrnat.odd beta) => /= .
- right => x Hx; apply: Rmult_le_neg_pos.
    exact: Hf.
  by rewrite -ssrnat.mul2n pow_Rsqr; apply: pow_le; apply: Rle_0_sqr.
- rewrite ssrnat.add0n; left => x Hx.
  by rewrite -ssrnat.mul2n pow_Rsqr; apply: pow_le; apply: Rle_0_sqr.
Qed.

Lemma remainder_correct_bertrandEq_0_tactic :
  forall prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon beta,
  no_floor_prog prog_f = true ->
  no_floor_prog prog_g = true ->
  let test iF ia := Fext.lt (F.fromZ 0) (I.lower ia) && Fext.lt (I.upper ia) (F.fromZ 1) in
  let iKernelInt ia := (Bertrand.f_neg_int prec ia (S beta)) in

  let f := fun x => nth 0 (eval_real prog_f (x::map A.real_from_bp bounds_f)) 0 in
  let g := fun x => nth 0 (eval_real prog_g (x::map A.real_from_bp bounds_g)) 0 in
  let iG'' := fun xi =>
    nth 0 (A.TaylorValuator.eval prec deg xi prog_g (A.TaylorValuator.TM.var ::
      map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds_g)
) A.TaylorValuator.TM.dummy in
  let iG' := fun xi => A.TaylorValuator.TM.get_tm (prec, deg) xi (iG'' xi) in
  let iG := fun xi => nth 0 (A.BndValuator.eval prec prog_g (xi::map A.interval_from_bp bounds_g)) I.nai in
  let iF := fun xi => nth 0 (A.BndValuator.eval prec prog_f (xi::map A.interval_from_bp bounds_f)) I.nai in
  let a := nth 0 (eval_real proga (map A.real_from_bp boundsa)) 0 in
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let estimator_sing :=
fun ia =>
  if test iF ia then
    if (I.bounded (iF (I.join (I.fromZ 0) ia))) then
      I.mul prec (iF (I.join (I.fromZ 0) ia)) (iKernelInt ia)
    else I.nai
  else I.nai
  in
  let estimator := fun fa fb =>
    let xi := I.join fa fb in
    Int'.taylor_integral_naive_intersection prec iG (iG' xi) xi fa fb in
  let i := Int.integral_interval_sing prec estimator estimator_sing depth ia (I.fromZ 0) epsilon in
  (forall x,  g x = f x * / (x * pow (ln x) (S (S beta)))) ->
  (I.convert i <> Inan ->
  (ex_RInt_gen g (at_right 0) (at_point a))) /\
  contains (I.convert i) (Xreal (RInt_gen g (at_right 0) (at_point a))).
Proof.
move => prec deg depth proga boundsa prog_f prog_g bounds_f bounds_g epsilon beta Hf Hg test iKernelInt f g iG'' iG' iG iF a ia estimator_sing estimator.
move => i Hfg.
suff: I.convert i <> Inan -> (ex_RInt_gen g (at_right 0) (at_point a)) /\
  contains (I.convert i)
    (Xreal (RInt_gen g (at_right 0) (at_point a))).
  move => H.
  case Hi: (I.convert i) => [|l u]; first by split.
  rewrite -Hi; split => [HnotInan|]; first by apply H.
  apply H; by rewrite Hi.
apply: integral_epsilon_sing_correct_RInt_gen => // .
  - apply: taylor_correct_estimator_general.
  - by [].
  - rewrite /correct_estimator_sing.
    move => ia0.
    suff:  Int.integralEstimatorCorrect_atsing
             (fun x : R => f x * / (x  * ln x ^ (S (S beta))))
             (estimator_sing ia0) ia0 0.
      apply: integralEstimatorCorrect_atsing_ext.
      by move => x; rewrite -Hfg.
    apply: (remainder_correct_generic_fun_at_right_singularity _ _ _ _ _ _ (fun f a => 0 < a < 1) _ (fun x => 0 < x < 1)).
    + apply: I.fromZ_correct.
    + by move => _ a0 [] // .
    + by move => a0 x f0 Hpre_cond Ha0x; apply: f_neg_continuous; lra.
    + by move => a0 _ Ha0; apply: f_neg_correct_RInt_gen_0_a => // .
    + by move => a0 ia1 H1; rewrite /iKernelInt; exact: Bertrand.f_neg_int_correct.
    + move => a0 _ x Ha0 Hx; lra.
    + apply: constant_sign_inv.
        move => x Hx; apply: Rmult_integral_contrapositive; split; first by lra.
        by apply: pow_nonzero; move: (ln_increasing x 1); rewrite ln_1; lra.
      apply: constant_sign_mult.
        by left => x Hx; lra.
      apply: constant_sign_pow; right => x Hx.
      by move: (ln_increasing x 1); rewrite ln_1; lra.
    + move => h ih ib b Hextih Hcontib /andP [Htest1 Htest2].
        apply Fext.lt_correct in Htest1.
        apply Fext.lt_correct in Htest2.
        move: Htest1 Htest2.
        rewrite !F.fromZ_correct I.lower_correct I.upper_correct.
        move: Hcontib.
        case Hib : (I.convert ib) => [|lb ub] //= ; case: lb Hib => [|lb] // Hib.
        case: ub Hib => [|ub] // Hib; lra.
    + by [].
Qed.

End Correction_lemmas_integral_sing.

End Correction_lemmas_integral_for_tactic.

Lemma xreal_to_contains :
  forall prog terms n xi,
  A.check_p (A.subset_check xi) (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  contains (I.convert xi) (Xreal (nth n (eval_real prog terms) 0)).
Proof.
intros prog terms n xi.
simpl A.check_p.
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
Qed.

Lemma xreal_to_positive :
  forall prog terms n,
  A.check_p A.positive_check (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  0 < nth n (eval_real prog terms) 0.
Proof.
intros prog terms n.
simpl A.check_p.
now apply (xreal_to_real (fun x => match x with Xnan => False | Xreal r => (0 < r)%R end) (fun x => (0 < x)%R)).
Qed.

Lemma xreal_to_nonzero :
  forall prog terms n,
  A.check_p A.nonzero_check (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  nth n (eval_real prog terms) 0 <> 0.
Proof.
intros prog terms n.
simpl A.check_p.
now apply (xreal_to_real (fun x => match x with Xnan => False | Xreal r => r <> 0 end) (fun x => x <> 0)).
Qed.

Inductive expr :=
  | Econst : nat -> expr
  | Eunary : unary_op -> expr -> expr
  | Ebinary : binary_op -> expr -> expr -> expr.

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | nil        => constr:((n, cons a l))
    | cons a _   => constr:((n, l))
    | cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, cons x l))
      end
    end in
  aux a l O.

Ltac reify t l :=
  let rec aux t l :=
    match get_float t with
    | false =>
      let aux_u o a :=
        match aux a l with
        | (?u, ?l) => constr:((Eunary o u, l))
        end in
      let aux_b o a b :=
        match aux b l with
        | (?v, ?l) =>
          match aux a l with
          | (?u, ?l) => constr:((Ebinary o u v, l))
          end
        end in
      match t with
      | Ropp ?a => aux_u Neg a
      | Rabs ?a => aux_u Abs a
      | Rinv ?a => aux_u Inv a
      | Rsqr ?a => aux_u Sqr a
      | Rmult ?a ?a => aux_u Sqr a
      | sqrt ?a => aux_u Sqrt a
      | cos ?a => aux_u Cos a
      | sin ?a => aux_u Sin a
      | tan ?a => aux_u Tan a
      | atan ?a => aux_u Atan a
      | exp ?a => aux_u Exp a
      | ln ?a => aux_u Ln a
      | powerRZ ?a ?b => aux_u (PowerInt b) a
      | pow ?a ?b => aux_u (PowerInt (Z_of_nat b)) a
      | Rplus ?a ?b => aux_b Add a b
      | Rminus ?a ?b => aux_b Sub a b
      | Rplus ?a (Ropp ?b) => aux_b Sub a b
      | Rmult ?a ?b => aux_b Mul a b
      | Rdiv ?a ?b => aux_b Div a b
      | Rmult ?a (Rinv ?b) => aux_b Div a b
      | Rnearbyint ?a ?b => aux_u (Nearbyint a) b
      | IZR (Ztrunc ?a) => aux_u (Nearbyint rnd_ZR) a
      | IZR (Zfloor ?a) => aux_u (Nearbyint rnd_DN) a
      | IZR (Zceil ?a) => aux_u (Nearbyint rnd_UP) a
      | IZR (Round_NE.ZnearestE ?a) => aux_u (Nearbyint rnd_NE) a
      | _ =>
        match list_add t l with
        | (?n, ?l) => constr:((Econst n, l))
        end
      end
    | ?f =>
      let u := constr:(I.T.toR f) in
      match list_add u l with
      | (?n, ?l) => constr:((Econst n, l))
      end
    end in
  aux t l.

Ltac list_find1 a l :=
  let rec aux l n :=
    match l with
    | nil       => false
    | cons a _  => n
    | cons _ ?l => aux l (S n)
    end in
  aux l O.

Ltac get_non_constants t :=
  let rec aux t l :=
    match t with
    | Econst _ => l
    | _ =>
      match list_find1 t l with
      | false =>
        let m :=
          match t with
          | Eunary _ ?a => aux a l
          | Ebinary _ ?a ?b => aux a ltac:(aux b l)
          end in
        constr:(cons t m)
      | _ => l
      end
    end in
  aux t (@nil expr).

Ltac list_find2 a l :=
  let rec aux l n :=
    match l with
    | nil       => false
    | cons a _  => n
    | cons _ ?l => aux l (S n)
    end in
  match a with
  | Econst ?n => eval compute in (n + length l)%nat
  | _ => aux l O
  end.

Ltac generate_machine l :=
  let rec aux l q :=
    match l with
    | nil => q
    | cons ?t ?l =>
      let m :=
        match t with
        | Eunary ?o ?a =>
          let u := list_find2 a l in
          constr:(Unary o u)
        | Ebinary ?o ?a ?b =>
          let u := list_find2 a l in
          let v := list_find2 b l in
          constr:(Binary o u v)
        end in
      aux l (cons m q)
    end in
  aux l (@nil term).

Ltac extract_algorithm t l :=
  match reify t l with
  | (Econst ?n, ?lc) =>
    constr:((cons (Forward n) nil, lc))
  | (?t, ?lc) =>
    let lnc := get_non_constants t in
    let lm := generate_machine lnc in
    constr:((lm, lc))
  end.

Ltac xalgorithm_post lx :=
  match goal with
  | |- contains (I.convert ?xi) (Xreal ?y) =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_contains formula b O xi _)
    end
  | |- (0 < ?y)%R =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_positive formula b O _)
    end
  | |- (?y <> 0)%R =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_nonzero formula b O _)
    end
  end.

Ltac list_warn l :=
  let rec aux l :=
    match l with
    | nil => idtac
    | cons ?a ?l => idtac a ; aux l
    end in
  aux l.

Ltac list_warn_rev l :=
  let rec aux l :=
    match l with
    | nil => idtac
    | cons ?a ?l => aux l ; idtac a
    end in
  aux l.

Ltac warn_whole l :=
  match l with
  | nil => idtac
  | cons _ nil =>
    idtac "Warning: Silently use the whole real line for the following term:" ;
    list_warn_rev l ; idtac "You may need to unfold this term, or provide a bound."
  | cons _ _ =>
    idtac "Warning: Silently use the whole real line for the following terms:" ;
    list_warn_rev l ; idtac "You may need to unfold some of these terms, or provide a bound."
  end.

Ltac get_trivial_bounds l prec :=
  let rec aux l prec :=
    match l with
    | nil => constr:(@nil A.bound_proof)
    | cons ?x ?l =>
      let i :=
      match x with
      | PI => constr:(A.Bproof x (I.pi prec) (I.pi_correct prec))
      | I.T.toR ?v =>
        constr:(let f := v in let rf := I.T.toR f in A.Bproof x (I.bnd f f) (conj (Rle_refl rf) (Rle_refl rf)))
      end in
      match aux l prec with
      | ?m => constr:(cons i m)
      end
    end in
  aux l prec.

Ltac get_bounds_aux x prec :=
  match goal with
  | H: Rle ?a x /\ Rle x ?b |- _ =>
    let v := get_float a in
    let w := get_float b in
    constr:(A.Bproof x (I.bnd v w) H)
  | H: Rle ?a x /\ Rle x ?b |- _ =>
    let va := extract_algorithm a (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
      | (?pb, ?lb) =>
        let lcb := get_trivial_bounds lb prec in
        constr:(let proga := pa in let boundsa := lca in let progb := pb in let boundsb := lcb in
          A.Bproof x _ (contains_bound_lr x prec proga boundsa 0 progb boundsb 0 H))
      end
    end
  | H: Rle ?a x |- _ =>
    let v := get_float a in
    constr:(A.Bproof x (I.bnd v F.nan) (conj H I))
  | H: Rle ?a x |- _ =>
    let v := extract_algorithm a (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in A.Bproof x _ (contains_bound_l x prec prog bounds 0 H))
    end
  | H: Rle x ?b |- _ =>
    let v := get_float b in
    constr:(A.Bproof x (I.bnd F.nan v) (conj I H))
  | H: Rle x ?b |- _ =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in A.Bproof x _ (contains_bound_r x prec prog bounds 0 H))
    end
  | H: Rle (Rabs x) ?b |- _ =>
    let v := get_float b in
    constr:(A.Bproof x (I.bnd (F.neg v) v) (Rabs_contains_rev v x H))
  | H: Rle (Rabs x) ?b |- _ =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in A.Bproof x _ (contains_bound_ar x prec prog bounds 0 H))
    end
  end.

Definition reify_var : R.
Proof.
exact R0.
Qed.

Ltac get_RInt_gen_bounds prec rint_depth rint_prec rint_deg x :=
  match x with
(* improper Bertrand integral at infinity *)
  | RInt_gen (fun x => (@?f x) * ((powerRZ x ?alpha) * (pow (ln x) ?beta))) (at_point ?a) (Rbar_locally p_infty) =>
    let g := eval cbv beta in ((fun (y : R) => (f y) * (powerRZ y alpha * pow (ln y) beta)) reify_var) in
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let vg := extract_algorithm g (cons reify_var nil) in
    let va := extract_algorithm a (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
        match vf with
        | (?pf, _ :: ?lf) =>
          let lcf := get_trivial_bounds lf prec in
          match vg with
            | (?pg, _ :: ?lg) =>
              let lcg := get_trivial_bounds lg prec in
              let c := constr:(proj2 (remainder_correct_bertrand_tactic prec rint_deg rint_depth pa lca pf pg lcf lcg rint_prec alpha beta
                                         (refl_equal true) (refl_equal true) (fun z => @eq_refl _ (nth 0 (eval_real pg (z::lg)) 0)))) in
              (* work-around for a bug in the pretyper *)
              match type of c with
                | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
              end
          end
        end
    end

(* improper Bertrand integral, alpha = 1 and beta > 1 at infinity *)
  | RInt_gen (fun x => (@?f x) * / (x * (pow (ln x) (S ?beta)))) (at_point ?a) (Rbar_locally p_infty) =>
    let g := eval cbv beta in ((fun (y : R) => (f y) * / (y * pow (ln y) (S beta))) reify_var) in
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let vg := extract_algorithm g (cons reify_var nil) in
    let va := extract_algorithm a (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
        match vf with
        | (?pf, _ :: ?lf) =>
          let lcf := get_trivial_bounds lf prec in
          match vg with
            | (?pg, _ :: ?lg) =>
              let lcg := get_trivial_bounds lg prec in
              let c := constr:(proj2 (remainder_correct_log_neg_infty_tactic prec rint_deg rint_depth pa lca pf pg lcf lcg rint_prec beta
                                        (refl_equal true) (refl_equal true) (fun z => @eq_refl _ (nth 0 (eval_real pg (z::lg)) 0)))) in
              (* work-around for a bug in the pretyper *)
              match type of c with
                | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
              end
          end
        end
    end

(* improper integral f(x) * exp (- (\lambda * x)) at infinity *)
  | RInt_gen (fun x => (@?f x) * (exp (Ropp (Rmult ?lam x)))) (at_point ?a) (Rbar_locally p_infty) =>
    let g := eval cbv beta in ((fun (y : R) => (f y) * (exp (Ropp (Rmult lam y)))) reify_var) in
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let vg := extract_algorithm g (cons reify_var nil) in
    let va := extract_algorithm a (@nil R) in
    let vlam := extract_algorithm lam (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
        match vf with
        | (?pf, _ :: ?lf) =>
          let lcf := get_trivial_bounds lf prec in
          match vg with
            | (?pg, _ :: ?lg) =>
              let lcg := get_trivial_bounds lg prec in
              match vlam with
                | (?plam,?llam) =>
                  let lclam := get_trivial_bounds llam prec in
                  let c := constr:(proj2 (remainder_correct_expn_tactic prec rint_deg rint_depth pa lca pf pg plam lclam lcf lcg rint_prec
                                             (refl_equal true) (refl_equal true) (fun z => @eq_refl _ (nth 0 (eval_real pg (z::lg)) 0)))) in
                  (* work-around for a bug in the pretyper *)
                  match type of c with
                    | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
                  end
              end
          end
        end
    end

(* improper integral at sing 0 *)
  | RInt_gen (fun x => (@?f x) * ((powerRZ x ?alpha) * (pow (ln x) ?beta))) (at_right 0) (at_point ?b) =>
    let g := eval cbv beta in ((fun (y : R) => (f y) * (powerRZ y alpha * pow (ln y) beta)) reify_var) in
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let vg := extract_algorithm g (cons reify_var nil) in
    (* for now, hardcoding 0 as the sing *)
    let va := extract_algorithm 0 (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
        | (?pb, ?lb) =>
          let lcb := get_trivial_bounds lb prec in
          match vf with
            | (?pf, _ :: ?lf) =>
              let lcf := get_trivial_bounds lf prec in
              match vg with
                | (?pg, _ :: ?lg) =>
                  let lcg := get_trivial_bounds lg prec in
                  let c := constr:(proj2 (remainder_correct_sing_tactic prec rint_deg rint_depth pb lcb pf pg lcf lcg rint_prec alpha beta
                                             (refl_equal true) (refl_equal true) (fun z => @eq_refl _ (nth 0 (eval_real pg (z::lg)) 0)))) in
                  (* work-around for a bug in the pretyper *)
                  match type of c with
                    | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
                  end
              end
          end
      end
    end

(* Bertrand equality case at singularity 0 *)
  | RInt_gen (fun x => (@?f x) * / (x * (pow (ln x) (S (S ?beta))))) (at_right 0) (at_point ?b) =>
    let g := eval cbv beta in ((fun (y : R) => (f y) * / (y * pow (ln y) (S (S beta)))) reify_var) in
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let vg := extract_algorithm g (cons reify_var nil) in
    let va := extract_algorithm 0 (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
        | (?pb, ?lb) =>
          let lcb := get_trivial_bounds lb prec in
          match vf with
            | (?pf, _ :: ?lf) =>
              let lcf := get_trivial_bounds lf prec in
              match vg with
                | (?pg, _ :: ?lg) =>
                  let lcg := get_trivial_bounds lg prec in
                  let c := constr:(proj2 (remainder_correct_bertrandEq_0_tactic prec rint_deg rint_depth pb lcb pf pg lcf lcg rint_prec beta
                                             (refl_equal true) (refl_equal true) (fun z => @eq_refl _ (nth 0 (eval_real pg (z::lg)) 0)))) in
                  (* work-around for a bug in the pretyper *)
                  match type of c with
                    | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
                  end
              end
          end
      end
    end
  end.

Ltac get_RInt_bounds prec rint_depth rint_prec rint_deg x :=
  match x with
  | RInt ?f ?a ?b =>
    let f := eval cbv beta in (f reify_var) in
    let vf := extract_algorithm f (cons reify_var nil) in
    let va := extract_algorithm a (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
      | (?pb, ?lb) =>
        let lcb := get_trivial_bounds lb prec in
        match vf with
        | (?pf, _ :: ?lf) =>
          let lcf := get_trivial_bounds lf prec in
          let c := constr:(proj2 (taylor_integral_naive_intersection_epsilon_correct prec rint_deg rint_depth pa lca pb lcb pf lcf rint_prec
                                    (refl_equal true))) in
          (* work-around for a bug in the pretyper *)
          match type of c with
          | contains (I.convert ?i) _ => constr:((A.Bproof x i c, @None R))
          end
        end
      end
    end
  end.

Ltac get_bounds l prec rint_depth rint_prec rint_deg :=
  let rec aux l prec lw :=
    match l with
    | nil => constr:((@nil A.bound_proof, @nil R))
    | cons ?x ?l =>
      let i :=
      match x with
      | PI => constr:((A.Bproof x (I.pi prec) (I.pi_correct prec), @None R))
      | I.T.toR ?v =>
        constr:((let f := v in A.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)), @None R))
      | _ => get_RInt_bounds prec rint_depth rint_prec rint_deg x
      | _ => get_RInt_gen_bounds prec rint_depth rint_prec rint_deg x
      | _ =>
        match goal with
        | _ =>
          let v := get_bounds_aux x prec in
          constr:((v, @None R))
        | _ =>
          constr:((A.Bproof x (I.bnd F.nan F.nan) (conj I I), @Some R x))
        end
      end in
      match aux l prec lw with
      | (?m, ?lw) =>
        match i with
        | (?i, @None R) => constr:((cons i m, lw))
        | (?i, @Some R ?aw) => constr:((cons i m, cons aw lw))
        end
      end
    end in
  aux l prec (@nil R).

Ltac xalgorithm_pre prec :=
  match goal with
  | |- Rge _ _ =>
    apply Rle_ge ;
    xalgorithm_pre prec
  | |- Rgt _ _ =>
    unfold Rgt ;
    xalgorithm_pre prec
  | |- Rle ?a ?x /\ Rle ?x ?b =>
    let v := get_float a in
    let w := get_float b in
    change (contains (I.convert (I.bnd v w)) (Xreal x))
  | |- Rle ?a ?x /\ Rle ?x ?b =>
    let va := extract_algorithm a (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
      | (?pb, ?lb) =>
        let lcb := get_trivial_bounds lb prec in
        refine (let proga := pa in let boundsa := lca in let progb := pb in let boundsb := lcb in contains_bound_lr' x prec proga boundsa 0 progb boundsb 0 _ _ _) ;
        [ vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl true) | idtac ]
      end
    end
  | |- Rle (Rabs ?a) ?b =>
    let v := get_float b in
    refine (Rabs_contains v a _)
  | |- Rle (Rabs ?a) ?b =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      refine (let prog := p in let bounds := lc in contains_bound_ar' a prec prog bounds 0 _ _) ;
      [ vm_cast_no_check (eq_refl true) | idtac ]
    end
  | |- Rle ?a ?b =>
    let v := get_float b in
    refine (proj2 (_ : contains (I.convert (I.bnd F.nan v)) (Xreal a)))
  | |- Rle ?a ?b =>
    let v := get_float a in
    refine (proj1 (_ : contains (I.convert (I.bnd v F.nan)) (Xreal b)))
  | |- Rle ?a ?b =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      refine (let prog := p in let bounds := lc in contains_bound_r' a prec prog bounds 0 _ _) ;
      [ vm_cast_no_check (eq_refl true) | idtac ]
    end
  | |- Rle ?a ?b =>
    let v := extract_algorithm a (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      refine (let prog := p in let bounds := lc in contains_bound_l' b prec prog bounds 0 _ _) ;
      [ vm_cast_no_check (eq_refl true) | idtac ]
    end
  | |- Rle ?a ?b =>
    apply Rminus_le ;
    refine (proj2 (_ : contains (I.convert (I.bnd F.nan F.zero)) (Xreal (a - b))))
  | |- Rlt 0 ?b =>
    idtac
  | |- Rlt ?a ?b =>
    apply Rminus_gt ;
    unfold Rgt
  | |- (?a <> 0)%R =>
    idtac
  | |- (?a <> ?b)%R =>
    apply Rminus_not_eq
  | _ => fail 5 "Goal is not an inequality with constant bounds"
  end.

Ltac xalgorithm lx prec :=
  match goal with
  | |- A.check_p ?check (nth ?n (eval_ext ?formula (map Xreal ?constants)) Xnan) => idtac
  | |- contains (I.convert ?xi) (Xreal ?y) => xalgorithm_post lx
  | _ => xalgorithm_pre prec ; xalgorithm_post lx
  end.

Lemma interval_helper_evaluate :
  forall bounds check formula prec n,
  A.check_f check (nth n (A.BndValuator.eval prec formula (map A.interval_from_bp bounds)) I.nai) = true ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros bound (check_f, check_p, check_th). simpl.
intros.
apply check_th with (2 := H).
apply A.BndValuator.eval_correct.
Qed.

Lemma interval_helper_bisection :
  forall bounds check formula prec depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => nth n (A.BndValuator.eval prec formula (b :: map A.interval_from_bp tail)) I.nai in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (x :: map A.xreal_from_bp bounds)) Xnan).
pose (fi := fun b => nth n (A.BndValuator.eval prec formula (b :: map A.interval_from_bp bounds)) I.nai).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f (Xreal x))).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (f x)) (2 := H) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (f y) (fi yi)) with (2 := Hb).
now apply A.BndValuator.eval_correct_ext.
Qed.

Lemma interval_helper_bisection_diff :
  forall bounds check formula prec depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => A.DiffValuator.eval prec formula (map A.interval_from_bp tail) n b in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (x :: map A.xreal_from_bp bounds)) Xnan).
pose (fi := fun b => A.DiffValuator.eval prec formula (map A.interval_from_bp bounds) n b).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f (Xreal x))).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (f x)) (2 := H) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (f y) (fi yi)) with (2 := Hb).
now apply A.DiffValuator.eval_correct_ext.
Qed.

Lemma interval_helper_bisection_taylor :
  forall bounds check formula prec deg depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => A.TaylorValuator.TM.eval (prec, deg)
      (nth n (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var ::
        map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) tail)) A.TaylorValuator.TM.dummy) b b in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec deg depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (Xreal x :: map A.xreal_from_bp bounds)) Xnan).
pose (fi := fun b => A.TaylorValuator.TM.eval (prec, deg)
  (nth n (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var ::
    map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds)) A.TaylorValuator.TM.dummy)
  b b).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f x)).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (Xbind f x)) (2 := H) (x := Xreal x) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (Xbind f y) (fi yi)) with (2 := Hb).
now apply A.TaylorValuator.eval_correct_ext.
Qed.

Definition prec_of_nat prec :=
  match Z_of_nat prec with Zpos p => F.PtoP p | _ => F.PtoP xH end.

Ltac do_interval vars prec depth rint_depth rint_prec rint_deg native nocheck eval_tac :=
  let prec := eval vm_compute in (prec_of_nat prec) in
  match nocheck with
  | true =>
    xalgorithm vars prec ;
    match goal with
    | |- A.check_p ?check (nth ?n (eval_ext ?formula (map Xreal ?constants)) Xnan) =>
      match get_bounds constants prec rint_depth rint_prec rint_deg with
      | (?bounds_, ?lw) =>
        let bounds := fresh "bounds" in
        pose (bounds := bounds_) ;
        change (map Xreal constants) with (map A.xreal_from_bp bounds) ;
        eval_tac bounds check formula prec depth n ;
        let ibounds := fresh "ibounds" in
        set (ibounds := map A.interval_from_bp bounds) ;
        cbv beta iota zeta delta [map A.interval_from_bp bounds] in ibounds ;
        clear ;
        match native with
        | true => native_cast_no_check (refl_equal true)
        | false => vm_cast_no_check (refl_equal true)
        end
      end
    end
  | false =>
    abstract (
    xalgorithm vars prec ;
    match goal with
    | |- A.check_p ?check (nth ?n (eval_ext ?formula (map Xreal ?constants)) Xnan) =>
      match get_bounds constants prec rint_depth rint_prec rint_deg with
      | (?bounds_, ?lw) =>
        let bounds := fresh "bounds" in
        pose (bounds := bounds_) ;
        change (map Xreal constants) with (map A.xreal_from_bp bounds) ;
        eval_tac bounds check formula prec depth n ;
        let ibounds := fresh "ibounds" in
        set (ibounds := map A.interval_from_bp bounds) ;
        cbv beta iota zeta delta [map A.interval_from_bp bounds] in ibounds ;
        clear ;
        (abstract
          (match native with
          | true => native_cast_no_check (refl_equal true)
          | false => vm_cast_no_check (refl_equal true)
          end))
        || warn_whole lw
      end
    end)
  end ||
  fail 1 "Numerical evaluation failed to conclude. You may want to adjust some parameters".

Ltac do_interval_eval bounds output formula prec depth n :=
  refine (interval_helper_evaluate bounds output formula prec n _).

Ltac do_interval_bisect bounds output formula prec depth n :=
  refine (interval_helper_bisection bounds output formula prec depth n _).

Ltac do_interval_bisect_diff bounds output formula prec depth n :=
  refine (interval_helper_bisection_diff bounds output formula prec depth n _).

Ltac do_interval_bisect_taylor deg bounds output formula prec depth n :=
  refine (interval_helper_bisection_taylor bounds output formula prec deg depth n _).

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | ?b => constr:(b :: l)
  | ?z => fail 100 "Unknown tactic parameter" z
  end.

Inductive interval_tac_method :=
  | itm_eval : interval_tac_method
  | itm_bisect : interval_tac_method
  | itm_bisect_diff : interval_tac_method
  | itm_bisect_taylor : nat -> interval_tac_method.

Ltac tac_of_itm itm :=
  match itm with
  | itm_eval => do_interval_eval
  | itm_bisect => do_interval_bisect
  | itm_bisect_diff => do_interval_bisect_diff
  | itm_bisect_taylor ?d => do_interval_bisect_taylor d
  end.

Ltac do_parse params depth :=
  let rec aux vars prec depth rint_depth rint_prec rint_deg native nocheck itm params :=
    match params with
    | nil => constr:((vars, prec, depth, rint_depth, rint_prec, rint_deg, native, nocheck, itm))
    | cons (i_prec ?p) ?t => aux vars p depth rint_depth rint_prec rint_deg native nocheck itm t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec depth rint_depth rint_prec rint_deg native nocheck itm_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec depth rint_depth rint_prec rint_deg native nocheck itm_bisect_diff t
    | cons (i_bisect_taylor ?x ?d) ?t => aux (cons x nil) prec depth rint_depth rint_prec rint_deg native nocheck (itm_bisect_taylor d) t
    | cons (i_depth ?d) ?t => aux vars prec d rint_depth rint_prec rint_deg native nocheck itm t
    | cons (i_integral_depth ?d) ?t => aux vars prec depth d rint_prec rint_deg native nocheck itm t
    | cons (i_integral_prec ?rint_prec) ?t => aux vars prec depth rint_depth (@inr F.type F.type (F.scale2 (F.fromZ 1) (F.ZtoS (- Z.of_nat rint_prec)))) rint_deg native nocheck itm t
    | cons (i_integral_width ?rint_prec) ?t => aux vars prec depth rint_depth (@inl F.type F.type (F.scale2 (F.fromZ 1) (F.ZtoS rint_prec))) rint_deg native nocheck itm t
    | cons (i_integral_deg ?rint_deg) ?t => aux vars prec depth rint_depth rint_prec rint_deg native nocheck itm t
    | cons i_native_compute ?t => aux vars prec depth rint_depth rint_prec rint_deg true nocheck itm t
    | cons i_delay ?t => aux vars prec depth rint_depth rint_prec rint_deg native true itm t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@nil R) 30%nat depth 3%nat (@inr F.type F.type (F.scale2 (F.fromZ 1) (F.ZtoS (-10)))) 10%nat false false itm_eval params.

Ltac do_interval_parse params :=
  match do_parse params 15%nat with
  | (?vars, ?prec, ?depth, ?rint_depth, ?rint_prec, ?rint_deg, ?native, ?nocheck, ?itm) =>
    let eval_tac := tac_of_itm itm in
    do_interval vars prec depth rint_depth rint_prec rint_deg native nocheck eval_tac
  end.

Ltac do_interval_generalize t b :=
  match goal with
  | |- ?P =>
    refine ((_ : contains (I.convert b) (Xreal t) -> P) _) ; [
    let H := fresh "H" in
    intro H ;
    match eval cbv -[IZR Rdiv] in (I.convert b) with
    | Inan => fail 5 "Inan: Nothing known about" t
    | Ibnd ?l ?u =>
      match l with
      | Xnan =>
        match u with
        | Xnan => fail 7 "Xnan: Nothing known about" t
        | Xreal ?u => change (True /\ t <= u)%R in H ; destruct H as [_ H]
        end
      | Xreal ?l =>
        match u with
        | Xnan => change (l <= t /\ True)%R in H ; destruct H as [H _]
        | Xreal ?u => change (l <= t <= u)%R in H
        end
      end
    end ;
    revert H |]
  end.

Ltac do_interval_intro_eval extend bounds formula prec depth :=
  let bounds' := eval cbv beta iota zeta delta [map A.interval_from_bp] in (map A.interval_from_bp bounds) in
  constr:(extend (nth 0 (A.BndValuator.eval prec formula bounds') I.nai)).

Ltac do_interval_intro_bisect extend bounds formula prec depth :=
  let bounds' := eval cbv beta iota zeta delta [map A.interval_from_bp] in (map A.interval_from_bp bounds) in
  constr:(match bounds' with
    | cons (Interval_interval_float.Ibnd l u) tail =>
      A.lookup_1d (fun b => nth 0 (A.BndValuator.eval prec formula (b :: tail)) I.nai) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro_bisect_diff extend bounds formula prec depth :=
  let bounds' := eval cbv beta iota zeta delta [map A.interval_from_bp] in (map A.interval_from_bp bounds) in
  constr:(match bounds' with
    | cons (Interval_interval_float.Ibnd l u) tail =>
      A.lookup_1d (fun b => A.DiffValuator.eval prec formula tail 0 b) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro_bisect_taylor deg extend bounds formula prec depth :=
  let bounds' := eval cbv beta iota zeta delta [map A.interval_from_bp] in (map A.interval_from_bp bounds) in
  constr:(match bounds' with
    | cons (Interval_interval_float.Ibnd l u) tail =>
      A.lookup_1d (fun b => A.TaylorValuator.TM.eval (prec, deg) (nth 0 (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const tail)) A.TaylorValuator.TM.dummy) b b) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro t extend params vars prec depth rint_depth rint_prec rint_deg native eval_tac :=
  let prec := eval vm_compute in (prec_of_nat prec) in
  match extract_algorithm t vars with
  | (?formula, ?constants) =>
    match get_bounds constants prec rint_depth rint_prec rint_deg with
    | (?bounds, ?lw) =>
      warn_whole lw ;
      let v := eval_tac extend bounds formula prec depth in
      let v := match native with true => eval native_compute in v | false => eval vm_compute in v end in
      do_interval_generalize t v ;
      [ | do_interval_parse params ]
    end
  end.

Ltac intro_tac_of_itm itm :=
  match itm with
  | itm_eval => do_interval_intro_eval
  | itm_bisect => do_interval_intro_bisect
  | itm_bisect_diff => do_interval_intro_bisect_diff
  | itm_bisect_taylor ?d => do_interval_intro_bisect_taylor d
  end.

Ltac do_interval_intro_parse t extend params :=
  match do_parse params 5%nat with
  | (?vars, ?prec, ?depth, ?rint_depth, ?rint_prec, ?rint_deg, ?native, ?nocheck, ?itm) =>
    let eval_tac := intro_tac_of_itm itm in
    do_interval_intro t extend params vars prec depth rint_depth rint_prec rint_deg native eval_tac
  end.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

End IntervalTactic.

(*Require Import Interval_stdz_carrier.*)
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module ITSFBI2 := IntervalTactic SFBI2.
Export ITSFBI2.

(* beginning of zone to comment out in releases *)

(* Require Import Interval_generic_ops. *)
(* Module GFSZ2 := GenericFloat Radix2. *)
(* Module ITGFSZ2 := IntervalTactic GFSZ2. *)
(* Export ITGFSZ2. *)

(* Goal True. *)
(* interval_intro *)
(*   (RInt_gen *)
(*      (fun x => (1 * (/ (x * (pow (ln x) 2))))) *)
(*      (at_right 0) *)
(*      (at_point (1/3))) with (i_integral_deg 2). *)
(* done. *)


(* Goal True. *)
(* interval_intro *)
(*   (RInt_gen *)
(*      (fun x => (1 / x * (/ (x * (ln x)^3)))) *)
(*      (at_point 10) *)
(*      (Rbar_locally p_infty)) with (i_integral_deg 0). *)
(* done. *)


(* Goal True. *)
(* interval_intro *)
(*   (RInt_gen *)
(*      (fun x => (1 / ((x^2 - 1)*(x^4 + 1)) * (powerRZ x 2 * (ln x)^1))) *)
(*      (at_right 0) *)
(*      (at_point (1/2))). *)
(* done. *)

(* Lemma blo0 : *)
(*    1 <= RInt (fun x => exp x) 0 1 <= 2. *)
(* Proof. *)
(* interval. *)
(* Qed. *)

(* Lemma blo1 : *)
(*   forall x, (Rabs x <= 15/3)%R -> *)
(*   (-4 <= x + 1)%R. *)
(* intros. *)
(* interval. *)
(* Qed. *)

(* Lemma blo2 : *)
(*   (2/3 <= 5/7)%R. *)
(* intros. *)
(* interval_intro (5/7)%R lower with (i_prec 4%nat). *)
(* apply Rle_trans with (2 := H). *)
(* interval. *)
(* Qed. *)

(* Lemma blo3 : *)
(*   forall x, (x <= 0)%R -> *)
(*   (0 <= x - x <= 0)%R. *)
(* intros. *)
(* Time interval with (i_bisect_diff x). *)
(* Qed. *)

(* Lemma blo4 : *)
(*   forall x, (3/2 <= x <= 2)%R -> *)
(*   forall y, (1 <= y <= 33/32)%R -> *)
(*   (Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768)%R. *)
(* intros. *)
(* interval with (i_bisect x). *)
(* Qed. *)

(* Lemma blo5 : *)
(*   forall x, (-1 <= x <= 1)%R -> *)
(*   (0 <= exp x - (1 + x) <= 3/4)%R. *)
(* Proof. *)
(* intros. *)
(* interval_intro (1 + x)%R with (i_bisect_taylor x 2). *)
(* split; try interval with (i_bisect_taylor x 2). *)
(* interval with (i_bisect_diff x). *)
(* Qed. *)

(* Lemma blo6 : 51/1000 <= RInt_gen (fun x => sin x * (powerRZ x (-5)%Z * pow (ln x) 1%nat)) (at_point R1) (Rbar_locally p_infty) <= 52/1000. *)
(* Proof. *)
(* interval. *)
(* Qed. *)

(* Lemma blo7 :  -962587772 * / 8589934592 <= *)
(*       RInt_gen (fun x : R => x * (powerRZ x 1 * ln x ^ 1))  *)
(*         (at_right 0) (at_point 1) <= -940939775 * / 8589934592. *)
(* Proof. *)
(* interval. *)
(* Qed. *)

(* Lemma blo8 : 876496966 * / 4398046511104 <= *)
(*       RInt_gen (fun x : R => 1 / x ^ 2 * exp (- x))  *)
(*         (at_point 5) (Rbar_locally p_infty) <= 876509397 * / 4398046511104. *)
(* Proof. *)
(* interval. *)
(* Qed. *)

(* Lemma pi10 : (31415926535/10000000000 < PI < 31415926536/10000000000)%R. *)
(* Proof. *)
(* split; interval with (i_prec 40). *)
(* Qed. *)
