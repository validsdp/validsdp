(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

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

Require Import ZArith.
From Flocq Require Import Raux.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import Interval_xreal.
Require Import Interval_interval.
Require Import Interval_missing.
Require Import Rstruct.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import poly_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolyBoundHornerQuad (I : IntervalOps) (Pol : PolyIntOps I)
  <: PolyBound I Pol.

Module Import Bnd := PolyBoundHorner I Pol.
Module J := IntervalExt I.

Definition ComputeBound (prec : Pol.U) (pol : Pol.T) (x : I.type) : I.type :=
  if 3 <= Pol.size pol then
    let a1 := Pol.nth pol 1 in
    let a2 := Pol.nth pol 2 in
    let a2t2 := I.add prec a2 a2 in
    let a2t4 := I.add prec a2t2 a2t2 in
    let b1 := I.div prec a1 a2t2 in
    let b2 := I.div prec (I.sqr prec a1) a2t4 in
    if (* I.bounded b1 && *) I.bounded b2 then
      I.add prec
            (I.add prec (I.sub prec (Pol.nth pol 0) b2)
                   (I.mul prec a2 (I.sqr prec (I.add prec x b1))))
            (I.mul prec (I.power_int prec x 3)
                   (Pol.horner prec (Pol.tail 3 pol) x))
    else Pol.horner prec pol x
  else Pol.horner prec pol x.

Import Pol.Notations. Local Open Scope ipoly_scope.

Theorem ComputeBound_correct prec pi p :
  pi >:: p ->
  J.extension (PolR.horner tt p) (ComputeBound prec pi).
Proof.
move=> Hnth X x Hx; rewrite /ComputeBound.
case E: (2 < Pol.size pi); last by apply: Bnd.ComputeBound_correct.
case Eb: I.bounded; last by apply: Bnd.ComputeBound_correct.
(* case Eb': I.bounded; last by apply: Bnd.ComputeBound_correct. *)
simpl.
set A0 := Pol.nth pi 0.
set A1 := Pol.nth pi 1.
set A2 := Pol.nth pi 2.
set Q3 := Pol.tail 3 pi.
pose a0 := PolR.nth p 0.
pose a1 := PolR.nth p 1.
pose a2 := PolR.nth p 2.
pose q3 := PolR.tail 3 p.
have Hi3: Pol.size pi = 3 + (Pol.size pi - 3) by rewrite subnKC //.
(* have Hx3: PolR.size p = 3 + (PolR.size p - 3) by rewrite -Hsiz -Hi3. *)
suff->: PolR.horner tt p x =
  (Rplus (Rplus (Rminus a0 (Rdiv (Rsqr a1) (Rplus (Rplus a2 a2) (Rplus a2 a2))))
              (Rmult a2 (Rsqr (Rplus x (Rdiv a1 (Rplus a2 a2))))))
        (Rmult (powerRZ x 3) (PolR.horner tt q3 x))).
have Hnth3 : Q3 >:: q3 by apply(*:*) Pol.tail_correct.
apply: J.add_correct;
  [apply: J.add_correct;
    [apply: J.sub_correct;
      [apply: Hnth
      |apply: J.div_correct;
        [apply: J.sqr_correct; apply: Hnth
        |apply: J.add_correct; apply: J.add_correct; apply: Hnth]]
    |apply: J.mul_correct;
      [apply: Hnth
      |apply: J.sqr_correct; apply: J.add_correct;
       [done
       |apply: J.div_correct;
         [apply: Hnth|apply: J.add_correct; apply: Hnth ]]]]
  |apply: J.mul_correct;
    [exact: J.power_int_correct|exact: Pol.horner_correct]].
rewrite 2!PolR.hornerE.
rewrite (@big_nat_leq_idx _ _ _ (3 + (PolR.size p - 3))).
rewrite big_mkord.
rewrite 3?big_ord_recl -/a0 -/a1 -/a2 ![Radd_monoid _]/= /q3 PolR.size_tail.
(* simpl Z.of_nat. *)
set x0 := powerRZ x 0.
set x1 := powerRZ x 1.
set x2 := powerRZ x 2.
set x3 := powerRZ x 3.
set s1 := bigop _ _ _.
set s2 := bigop _ _ _.
have H4 : (a2 + a2 + (a2 + a2) <> 0)%R.
  intro K.
  move: Eb.
  have Hzero : contains (I.convert
    (I.add prec (I.add prec (Pol.nth pi 2) (Pol.nth pi 2))
      (I.add prec (Pol.nth pi 2) (Pol.nth pi 2)))) (Xreal 0).
    rewrite -K.
    by apply: J.add_correct; apply: J.add_correct; apply: Hnth.
  case/(I.bounded_correct _) => _.
  case/(I.upper_bounded_correct _) => _.
  rewrite /I.bounded_prop.
  set d := I.div prec _ _.
  suff->: I.convert d = IInan by [].
  apply -> contains_Xnan.
  rewrite -(Xdiv_0_r (Xsqr (Xreal a1))).
  apply: I.div_correct =>//.
  apply: I.sqr_correct.
  by apply: Hnth; rewrite Hi3.
have H2 : (a2 + a2 <> 0)%R by intro K; rewrite K Rplus_0_r in H4.
suff->: s1 = Rmult x3 s2.
  have->: Rmult a0 x0 = a0 by simpl; rewrite /x0 powerRZ_O Rmult_1_r.
  rewrite -!Rplus_assoc /Rminus; congr Rplus.
  rewrite /x1 /x2 /Rsqr.
  field.
  split =>//.
by rewrite -Rplus_assoc in H4.
rewrite /s1 /s2 /x3; clear.
rewrite Rmult_comm.
rewrite big_mkord big_distrl.
apply: eq_bigr=> i _.
rewrite /PolR.tail /PolR.nth nth_drop.
(* some bookkeeping about powers *)
rewrite -!(pow_powerRZ _ 3).
rewrite /= !Rmult_assoc; f_equal; ring.
by rewrite addnC leq_subnK.
move=> i /andP [Hi _].
by rewrite PolR.nth_default ?Rmult_0_l.
Qed.

Lemma ComputeBound_propagate :
  forall prec pi,
  J.propagate (ComputeBound prec pi).
Proof.
red=> *; rewrite /ComputeBound /=.
by repeat match goal with [|- context [if ?b then _ else _]] => destruct b end;
  rewrite !(I.add_propagate_r,I.mul_propagate_l,J.power_int_propagate,
            Pol.horner_propagate).
Qed.

End PolyBoundHornerQuad.
