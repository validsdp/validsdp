(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

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

Require Import Rdefinitions Raxioms RIneq Rbasic_fun.
Require Import Epsilon FunctionalExtensionality.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.choice mathcomp.ssreflect.bigop mathcomp.algebra.ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure real_eqMixin := EqMixin eqrP.
Canonical Structure real_eqType := Eval hnf in EqType R real_eqMixin.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%N. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

Definition R_choiceMixin : choiceMixin R :=
  Choice.Mixin pickR_some pickR_ex pickR_ext.

Canonical R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Definition real_zmodMixin := ZmodMixin RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Canonical Structure real_zmodType := Eval hnf in ZmodType R real_zmodMixin.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

Definition real_ringMixin := RingMixin RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

Canonical Structure real_ringType := Eval hnf in RingType R real_ringMixin.
Canonical Structure real_comringType := Eval hnf in ComRingType R Rmult_comm.

Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.
