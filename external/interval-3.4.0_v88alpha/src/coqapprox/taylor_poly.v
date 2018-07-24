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


Require Import BinPos.
From Flocq Require Import Raux.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import Interval_interval.
Require Import poly_datatypes basic_rec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module TaylorPoly (C : FullOps) (P : PolyOps C).
(** Needs functions defining the recurrences, as well as rec1, rec2, grec1. *)

Definition cst_rec (x : C.T) (n : nat) := C.mask C.zero x.

Definition var_rec (a b : C.T) (n : nat) := C.mask (C.mask C.zero a) b.

Definition T_cst c (x : C.T) := P.rec1 cst_rec (C.mask c x).
(** Note that in addition to the Taylor expansion point that is
the 2nd parameter of T_cst, the first one is the value of
the constant itself. *)

Definition T_var x := P.rec2 var_rec x (C.mask C.one x).

Section PrecIsPropagated1.
Variable u : C.U.

Definition inv_rec (x : C.T) (a : C.T) (n : nat) : C.T := C.div u a (C.opp x).

Definition exp_rec (a : C.T) (n : nat) : C.T := C.div u a (C.from_nat n).

Definition sin_rec (a b : C.T) (n : nat) : C.T :=
  C.div u (C.opp a) (C.mul u (C.from_nat n) (C.from_nat n.-1)).

Definition cos_rec (a b : C.T) (n : nat) : C.T :=
  C.div u (C.opp a) (C.mul u (C.from_nat n) (C.from_nat n.-1)).

Definition pow_aux_rec (p : Z) (x : C.T) (_ : C.T) (n : nat)
  := if Z.ltb p Z0 || Z.geb p (Z.of_nat n) then
        C.power_int u x (p - Z.of_nat n)%Z
     else C.mask C.zero x.

(* Erik: These notations could be used globally *)
Local Notation "i + j" := (C.add u i j).
Local Notation "i - j" := (C.sub u i j).
Local Notation "i * j" := (C.mul u i j).
Local Notation "i / j" := (C.div u i j).

Definition sqrt_rec (x : C.T) (a : C.T) (n : nat) :=
  let nn := C.from_nat n in
  let n1 := C.from_nat n.-1 in
  let one := C.from_nat 1 in
  let two := C.from_nat 2 in
  (one - two * n1) * a / (two * x * nn).

Definition invsqrt_rec (x : C.T) (a : C.T) (n : nat) :=
  let nn := C.from_nat n in
  let n1 := C.from_nat n.-1 in
  let one := C.from_nat 1 in
  let two := C.from_nat 2 in
  C.opp (one + two * n1) * a / (two * x * nn).

(*
Definition ln_rec (x : T) (a b : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let n2 := tnat n.-2 in
  topp (n1 * b) / (nn * x).

Definition Deriv_atan J := tinv u (tnat 1 + (tsqr u J)).

(* (2*loc0+2*a*loc1-(loc0+2*a*loc1)*(i1+1))/((1+a^2)*(i1+1)) *)
Definition atan_rec (x0 : T) (a b : T) (np2 : nat) :=
  let n := tnat (np2.-2) in
  let one := tnat 1 in
  let two := tnat 2 in
(*(two*loc0+two*a*loc1-(loc0+two*a*loc1)*(nn))/((one+a*a)*(nn)). (*OLD*)*)
topp ((n*a+two*b*x0*n+two*b*x0) / (n+n*(tsqr u x0)+two+two*(tsqr u x0))).
(* topp ((nn*u+two*v*a*nn+two*v*a)/((one+(tsqr a))*(nn+two)). (*TESTER*)*)

Definition Deriv_asin (x : T) := (tinvsqrt u (tnat 1 - tsqr u x)).

(* -(u(n+1)*(n+1)*(1+2*n)*z0+n^2*u(n))/((n+1)*(n+2)*z0^2-(n+1)*(n+2)) *)
Definition asin_rec (x : T) (a b : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let n2 := tnat n.-2 in
  let one := tnat 1 in
  let two := tnat 2 in
  (b*(n1)*(one+two*n2)*x+n2*n2*a)/((n1)*(nn)*(one-tsqr u x)).

Definition Deriv_acos x := (* Eval unfold Deriv_asin in *)
  topp (Deriv_asin x).

Definition acos_rec := asin_rec. (* acos & asin satisfy the same diffeq *)
*)

End PrecIsPropagated1.

Section PrecIsPropagated2.
Variable u : P.U.

(*
Definition T_ln x := trec2 (ln_rec u x) (tln u x) (C.inv u x).
Definition T_atan x := trec2 (atan_rec u x) (tatan u x) (Deriv_atan u x).
Definition T_asin x := trec2 (asin_rec u x) (tasin u x) (Deriv_asin u x).
Definition T_acos x := trec2 (acos_rec u x) (tacos u x) (Deriv_acos u x).
*)

Definition T_inv x := P.rec1 (inv_rec u x) (C.inv u x).

Definition T_exp x := P.rec1 (exp_rec u) (C.exp u x).

Definition T_sin x := P.rec2 (sin_rec u) (C.sin u x) (C.cos u x).

Definition T_cos x := P.rec2 (cos_rec u) (C.cos u x) (C.opp (C.sin u x)).

Definition T_sqrt x := P.rec1 (sqrt_rec u x) (C.sqrt u x).

Definition T_invsqrt x := P.rec1 (invsqrt_rec u x) (C.invsqrt u x).

Definition T_power_int (p : Z) x (n : nat) :=
  P.dotmuldiv u (falling_seq p n) (fact_seq n)
              (P.rec1 (pow_aux_rec u p x) (C.power_int u x p) n).

Definition T_tan x :=
  let polyX := P.lift 1 P.one (* in monomial basis *) in
  let J := C.tan u x in
  let s := [::] in
  let F q n :=
    let q' := P.deriv u q in
    P.div_mixed_r u (P.add u q' (P.lift 2 q')) (C.from_nat n) in
  let G q _ := P.horner u q J (* in monomial basis *) in
  P.grec1 F G polyX s.

Definition T_atan x :=
  let q1 := P.one in
  let J := C.atan u x in
  let s := [:: J] in
  let F q n :=
    let q2nX := P.mul_mixed u (C.from_nat ((n.-1).*2)) (P.lift 1 q) in
    let q' := P.deriv u q in
    P.div_mixed_r u (P.sub u (P.add u q' (P.lift 2 q')) q2nX) (C.from_nat n) in
  let G q n :=
    C.div u (P.horner u q x)
      (C.power_int u (C.add u C.one (C.sqr u x)) (Z_of_nat n)) in
  P.grec1 F G q1 s.

Definition T_ln x n :=
  let lg := C.ln u x in
  let y := C.mask x lg in
  P.polyCons lg
  (if n is n'.+1 then
     let p1 := (-1)%Z in
     P.dotmuldiv u (falling_seq p1 n') (behead (fact_seq n))
                  (P.rec1 (pow_aux_rec u p1 y) (C.power_int u y p1) n')
   else P.polyNil).

End PrecIsPropagated2.
End TaylorPoly.
