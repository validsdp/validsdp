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

Require Import Reals Bool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Interval_missing.

Definition is_zero x := Req_bool x 0.
Definition is_positive x := Rlt_bool 0 x.
Definition is_negative x := Rlt_bool x 0.

Lemma is_zero_spec :
  forall x, Req_bool_prop x 0 (is_zero x).
Proof.
intros x.
exact (Req_bool_spec x 0).
Qed.

Lemma is_positive_spec :
  forall x, Rlt_bool_prop 0 x (is_positive x).
Proof.
exact (Rlt_bool_spec 0).
Qed.

Lemma is_negative_spec :
  forall x, Rlt_bool_prop x 0 (is_negative x).
Proof.
intros x.
exact (Rlt_bool_spec x 0).
Qed.

(*
 * Extended reals
 *)

Inductive ExtendedR : Set :=
  | Xnan : ExtendedR
  | Xreal : R -> ExtendedR.

Definition proj_val x :=
  match x with Xreal y => y | Xnan => R0 end.

Definition proj_fun v f x :=
  match f (Xreal x) with Xreal y => y | Xnan => v end.

(* useful to discriminate over an ExtendedR *)
Definition notXnan (xR : ExtendedR) : Prop :=
  match xR with
    | Xnan => false
    | Xreal _ => true end = true.

Inductive Xcomparison : Set :=
  Xeq | Xlt | Xgt | Xund.

Definition Xcmp x y :=
  match x, y with
  | Xreal u, Xreal v =>
    match Rcompare u v with
    | Lt => Xlt
    | Eq => Xeq
    | Gt => Xgt
    end
  | _, _ => Xund
  end.

Definition extension f fx := forall x,
  match fx x, x with
  | Xnan, _ => True
  | Xreal v, Xreal u => f u = v
  | _, _ => False
  end.

Definition Xbind f x :=
  match x with
  | Xreal x => f x
  | Xnan => Xnan
  end.

Definition Xbind2 f x y :=
  match x, y with
  | Xreal x, Xreal y => f x y
  | _, _ => Xnan
  end.

Notation Xlift f := (Xbind (fun x => Xreal (f x))).
Notation Xlift2 f := (Xbind2 (fun x y => Xreal (f x y))).

Lemma Xlift2_nan_r :
  forall f x, Xlift2 f x Xnan = Xnan.
Proof.
now intros f [|x].
Qed.

Notation Xneg := (Xlift Ropp).

Lemma Xneg_involutive :
  forall x, Xneg (Xneg x) = x.
Proof.
intros [|x].
easy.
apply (f_equal Xreal), Ropp_involutive.
Qed.

Definition Xinv' x := if is_zero x then Xnan else Xreal (/ x).
Definition Xsqrt' x := if is_negative x then Xnan else Xreal (sqrt x).
Definition Xdiv' x y := if is_zero y then Xnan else Xreal (x / y).

Notation Xinv := (Xbind Xinv').
Notation Xsqrt := (Xbind Xsqrt').
Notation Xabs := (Xlift Rabs).
Notation Xadd := (Xlift2 Rplus).
Notation Xsub := (Xlift2 Rminus).
Notation Xmul := (Xlift2 Rmult).
Notation Xdiv := (Xbind2 Xdiv').
Notation Xmin := (Xlift2 Rmin).
Notation Xmax := (Xlift2 Rmax).

Lemma Xsub_split :
  forall x y, Xsub x y = Xadd x (Xneg y).
Proof.
now intros [|x] [|y].
Qed.

Lemma Xdiv_split :
  forall x y, Xdiv x y = Xmul x (Xinv y).
Proof.
intros [|x] [|y] ; try split.
unfold Xbind2, Xbind, Xdiv', Xinv'.
now case (is_zero y).
Qed.

Definition Xtan' x := if is_zero (cos x) then Xnan else Xreal (tan x).
Definition Xln' x := if is_positive x then Xreal (ln x) else Xnan.
Definition Xpower_int' x n :=
  match n with
  | 0%Z => Xreal 1%R
  | Zpos p => Xreal (pow x (nat_of_P p))
  | Zneg p => if is_zero x then Xnan else Xreal (Rinv (pow x (nat_of_P p)))
  end.

Notation Xsqr := (Xlift Rsqr).
Notation Xcos := (Xlift cos).
Notation Xsin := (Xlift sin).
Notation Xtan := (Xbind Xtan').
Notation Xatan := (Xlift atan).
Notation Xexp := (Xlift exp).
Notation Xln := (Xbind Xln').
Definition Xpower_int x n := Xbind (fun x => Xpower_int' x n) x.

Lemma Xpower_int_correct :
  forall n, extension (fun x => powerRZ x n) (fun x => Xpower_int x n).
Proof.
intros [|n|n] [|x] ; try split.
unfold Xpower_int, Xpower_int', Xbind.
now case (is_zero x).
Qed.

(*
 * "Field" structure
 *)

Lemma Xadd_comm :
  forall x y,
  Xadd x y = Xadd y x.
Proof.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Rplus_comm.
Qed.

Lemma Xadd_0_l :
  forall x,
  Xadd (Xreal 0) x = x.
Proof.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rplus_0_l.
Qed.

Lemma Xadd_0_r :
  forall x,
  Xadd x (Xreal 0) = x.
Proof.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rplus_0_r.
Qed.

Lemma Xmul_comm :
  forall x y,
  Xmul x y = Xmul y x.
Proof.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Rmult_comm.
Qed.

Lemma Xmul_assoc :
  forall x y z,
  Xmul (Xmul x y) z = Xmul x (Xmul y z).
Proof.
intros [|x] [|y] [|z] ; try split.
simpl.
apply f_equal.
apply Rmult_assoc.
Qed.

Lemma Xmul_1_l :
  forall x,
  Xmul (Xreal 1) x = x.
Proof.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_1_l.
Qed.

Lemma Xmul_1_r :
  forall x,
  Xmul x (Xreal 1) = x.
Proof.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_1_r.
Qed.

Lemma Xmul_Xadd_distr_r :
  forall x y z,
  Xmul (Xadd x y) z = Xadd (Xmul x z) (Xmul y z).
Proof.
intros [|x] [|y] [|z] ; try split.
simpl.
apply f_equal.
apply Rmult_plus_distr_r.
Qed.

Lemma Xmul_Xneg_distr_l :
  forall x y,
  Xmul (Xneg x) y = Xneg (Xmul x y).
Proof.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Ropp_mult_distr_l_reverse.
Qed.

Lemma Xmul_Xneg_distr_r :
  forall x y,
  Xmul x (Xneg y) = Xneg (Xmul x y).
Proof.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Ropp_mult_distr_r_reverse.
Qed.

Lemma Xinv_Xmul_distr :
  forall x y,
  Xinv (Xmul x y) = Xmul (Xinv x) (Xinv y).
Proof.
intros [|x] [|y] ; try easy ; simpl ; unfold Xinv'.
now destruct (is_zero_spec x).
destruct (is_zero_spec x).
destruct (is_zero_spec (x * y)).
apply refl_equal.
elim H0.
rewrite H.
apply Rmult_0_l.
destruct (is_zero_spec y).
destruct (is_zero_spec (x * y)).
apply refl_equal.
elim H1.
rewrite H0.
apply Rmult_0_r.
destruct (is_zero_spec (x * y)).
elim (prod_neq_R0 _ _ H H0 H1).
apply (f_equal Xreal).
now apply Rinv_mult_distr.
Qed.

Definition Xmask x y :=
  match y with
  | Xreal _ => x
  | Xnan => Xnan
  end.

Lemma Xmul_Xinv :
  forall x,
  Xmul x (Xinv x) = Xmask (Xreal 1) (Xinv x).
Proof.
intros [|x] ; try easy ; simpl ; unfold Xinv'.
destruct (is_zero_spec x).
apply refl_equal.
apply (f_equal Xreal).
now apply Rinv_r.
Qed.

Lemma Xdiv_0_r :
  forall x,
  Xdiv x (Xreal 0) = Xnan.
Proof.
intros [|x] ; try easy ; simpl ; unfold Xdiv'.
case is_zero_spec.
easy.
intros H.
now elim H.
Qed.
