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
Require Import Rfunctions. (* for fact_simpl *)
Require Import NaryFunctions.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.fintype mathcomp.ssreflect.bigop mathcomp.ssreflect.tuple.
Require Import seq_compl.

(*
This library defines polymorphic definitions rec1up (resp. rec2up) that
make it possible to compute the list [:: u(0); u(1);...; u(n)] for
a given function u defined by an order-1 (resp. order-2) recurrence.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac flatten := repeat
  first[rewrite<-pred_of_minus in *| rewrite<-plusE in *|rewrite<-minusE in *].
Ltac iomega := intros; flatten; (omega || apply/leP; omega).
Ltac iomega_le := (repeat move/leP=>?); iomega.

(** * Additional lemmas about [seq] *)

Notation nth_defaults := set_nth_default. (* for backward compatibility *)

Lemma behead_rcons (T : Type) (s : seq T) (x : T) :
  s <> [::] -> behead (rcons s x) = rcons (behead s) x.
Proof. by case: s. Qed.

Lemma behead_rev_take (T : Type) (s : seq T) (n : nat) :
  n <= size s -> behead (rev (take n s)) = rev (take n.-1 s).
Proof.
elim: n s =>[//|n IHn] [//|x s] H //.
rewrite ltnS -/size in H.
rewrite /=.
case: n IHn H =>[//|n] /= IHn H; first by rewrite take0 //.
rewrite [in RHS]rev_cons -IHn // rev_cons behead_rcons //.
move/(f_equal size).
fold (@take T); fold (@size T) in H.
rewrite size_rev size_take.
case: leq =>//=.
by move=> top; rewrite top in H.
Qed.

(** * Order-1 recurrences *)

Section Defix1.

Variable T : Type.

Variable F : T -> nat -> T.
(** to be instantiated by a function satisfying u(n) = F(u(n-1), n). *)

Fixpoint loop1 (n p : nat) (a : T) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let c := F a p in loop1 m p.+1 c (c :: s)
  end.

Variable a0 : T.

Definition rec1down n := loop1 n 1 a0 [:: a0].

Definition rec1up n := rev (rec1down n).

Lemma size_loop1 n p a s : size (loop1 n p a s) = n + size s.
Proof. by elim: n p a s => [//|n IHn] *; rewrite IHn addSnnS. Qed.

Lemma size_rec1down n : size (rec1down n) = n.+1.
Proof. by case: n => [//|n]; rewrite size_loop1 addn1. Qed.

Lemma size_rec1up n : size (rec1up n) = n.+1.
Proof. by rewrite size_rev size_rec1down. Qed.

Variable d : T.

Lemma head_loop1S n s a p :
  head d s = a ->
  head d (loop1 n.+1 p a s) = F (head d (loop1 n p a s)) (n+p).
Proof.
by elim: n s a p => [_ _ _->//|n IHn s a p H]; rewrite !IHn // addSnnS.
Qed.

Theorem head_loop1 (n p : nat) a s :
  head d s = a ->
  head d (loop1 n p a s) = iteri n (fun i c => F c (i + p)) a.
Proof.
elim: n p a s =>[//|n IHn] p a s H.
move E: (n.+1) => n'.
rewrite /= -{}E IHn //.
clear; elim: n =>[//=|n IHn].
by rewrite /= IHn /= addSnnS.
Qed.

Lemma head_rec1downS n :
  head d (rec1down n.+1) = F (head d (rec1down n)) n.+1.
Proof. by rewrite head_loop1S ?addn1. Qed.

Lemma nth_rec1up_last k : nth d (rec1up k) k = last d (rec1up k).
Proof. by rewrite (last_nth d) size_rec1up. Qed.

Lemma last_rec1up k : last d (rec1up k) = head d (loop1 k 1 a0 [:: a0]).
Proof. by rewrite /rec1up /rec1down last_rev. Qed.

Lemma nth_rec1upS k :
  nth d (rec1up k.+1) k.+1 = F (nth d (rec1up k) k) k.+1.
Proof. by rewrite !nth_rec1up_last !last_rev head_rec1downS. Qed.

Lemma loop1S_ex n p a s :
  exists c, loop1 n.+1 p a s = c :: (loop1 n p a s).
Proof.
elim: n p a s=> [|n IH] p a s; first by exists (F a p).
remember (S n) as n'; simpl.
case: (IH p.+1 (F a p) (F a p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Lemma behead_rec1down n : behead (rec1down n.+1) = rec1down n.
Proof. by rewrite /rec1down; case: (loop1S_ex n 1 a0 [:: a0])=> [c ->]. Qed.

Lemma nth_rec1downD d1 p q n :
  nth d1 (rec1down (p+q+n)) (p+q) = nth d1 (rec1down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec1down.
Qed.

Lemma nth_rec1downD_dflt2 d1 d2 p q n :
  nth d1 (rec1down (p+q+n)) (p+q) = nth d2 (rec1down (p+n)) p.
Proof.
rewrite nth_rec1downD (nth_defaults d1 d2) // size_rec1down.
by iomega.
Qed.

Lemma nth_rec1down_indep d1 d2 m1 m2 n :
  n <= m1 -> n <= m2 ->
  nth d1 (rec1down m1) (m1 - n) = nth d2 (rec1down m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm; last first.
- by rewrite Hm (nth_defaults d1 d2) // size_rec1down; iomega.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n by rewrite -Hpq subnK.
  exact: nth_rec1downD_dflt2.
set p := m1 - n in h1' *.
rewrite -h1' addnC.
pose q := m2 - m1.
have Hpq : m2 - n = p + q.
  rewrite /p /q in h2' *.
  by rewrite addnC addnBA // subnK // ltnW.
rewrite Hpq.
have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec1downD_dflt2.
Qed.

Lemma nth_rec1up_indep d1 d2 m1 m2 n :
  n <= m1 -> n <= m2 ->
  nth d1 (rec1up m1) n = nth d2 (rec1up m2) n.
Proof.
move=> h1 h2.
rewrite !nth_rev; first last.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
rewrite !size_loop1 /= !addn1 !subSS.
exact: nth_rec1down_indep.
Qed.

Theorem nth_rec1up n k :
  nth d (rec1up n) k =
  if n < k then d
  else iteri k (fun i c => F c (i + 1)) a0.
Proof.
case: (ltnP n k) => H; first by rewrite nth_default // size_rec1up.
rewrite (@nth_rec1up_indep d d n k k) //.
by rewrite nth_rec1up_last last_rec1up head_loop1.
Qed.

(** For the base case *)

Lemma rec1down_co0 n: nth d (rec1down n) n = a0.
Proof.
elim: n=> [//|n IH].
by rewrite /rec1down; have [c ->] := loop1S_ex n 1 a0 [:: a0].
Qed.

Lemma rec1up_co0 n : nth d (rec1up n) 0 = a0.
Proof. by rewrite nth_rev size_rec1down // subn1 rec1down_co0. Qed.

End Defix1.

Section GenDefix1.

Variables A T : Type.

Variable F : A -> nat -> A. (* may involve symbolic differentiation *)
(** to be instantiated by a function satisfying a(n+1)=F(a(n),n+1). *)

Variable G : A -> nat -> T.
(** to be instantiated by a function satisfying u(N+n)=G(a(n),N+n).
Here, N is the size of the list [init]. *)

Fixpoint gloop1 (n p : nat) (a : A) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let r := G a p in
              let p1 := p.+1 in
              let c := F a p1 in gloop1 m p1 c (r :: s)
  end.

Variable a0 : A.

Variable init : seq T.
(** Remark: [init] can be nil *)

Definition grec1down n :=
  if (n.+1 - size init) is n'.+1
    then gloop1 n'.+1 (size init) a0 (rev init)
    else rev (take n.+1 init).

Lemma grec1downE (n : nat) :
  grec1down n =
  if n >= size init
    then gloop1 (n - size init).+1 (size init) a0 (rev init)
    else rev (take n.+1 init).
Proof.
rewrite /grec1down.
case: (leqP (size init) n)=>H; first by rewrite subSn //.
by move: H; rewrite -subn_eq0; move/eqP->.
Qed.

Definition grec1up n := rev (grec1down n).

Lemma size_gloop1 n p a s : size (gloop1 n p a s) = n + size s.
Proof. by elim: n p a s => [//|n IHn] *; rewrite IHn addSnnS. Qed.

Lemma size_grec1down n : size (grec1down n) = n.+1.
Proof.
rewrite /grec1down.
case E: (n.+1 - size init) =>[|k].
  rewrite size_rev size_take.
  move/eqP: E; rewrite subn_eq0 leq_eqVlt.
  case/orP; last by move->.
  move/eqP->; rewrite ifF //.
  by rewrite ltnn.
rewrite size_gloop1 /= -E.
by rewrite size_rev subnK // ltnW // -subn_gt0 E.
Qed.

Lemma size_grec1up n : size (grec1up n) = n.+1.
Proof. by rewrite size_rev size_grec1down. Qed.

Theorem grec1up_init n :
  n < size init ->
  grec1up n = take n.+1 init.
Proof. by rewrite /grec1up /grec1down -subn_eq0; move/eqP ->; rewrite revK. Qed.

Theorem last_grec1up (d : T) (n : nat) :
  size init <= n ->
  last d (grec1up n) =
  head d (gloop1 (n - size init).+1 (size init) a0 (rev init)).
Proof. by move=> Hn; rewrite /grec1up /grec1down subSn // last_rev. Qed.

Theorem head_gloop1 (d : T) (n p : nat) (a : A) (s : seq T):
  head d (gloop1 n.+1 p a s) = G (iteri n (fun i c => F c (i + p).+1) a) (n + p).
Proof.
elim: n p a s =>[//|n IHn] p a s.
move E: (n.+1) => n'.
rewrite /= -{}E IHn.
congr G; last by rewrite addSnnS.
clear; elim: n =>[//=|n IHn].
by rewrite /= IHn /= addSnnS.
Qed.

Lemma gloop1S_ex n p a s :
  exists c, gloop1 n.+1 p a s = c :: (gloop1 n p a s).
Proof.
elim: n p a s => [|n IH] p a s; first by exists (G a p).
remember (S n) as n'; simpl.
case: (IH p.+1 (F a p.+1) (G a p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Theorem behead_grec1down (n : nat) :
  behead (grec1down n.+1) = grec1down n.
Proof.
pose s := rev init.
pose m := size init.
rewrite !grec1downE.
case: (leqP (size init) n) => H.
  rewrite leqW // subSn //.
  have [c Hc] := gloop1S_ex (n - m).+1 m a0 s.
  by rewrite Hc.
rewrite leq_eqVlt in H; case/orP: H; [move/eqP|] => H.
  rewrite -H subnn /= ifT H //.
  by rewrite take_oversize.
rewrite ifF 1?leqNgt ?H //.
by rewrite behead_rev_take.
Qed.

Lemma nth_grec1downD d1 p q n:
  nth d1 (grec1down (p+q+n)) (p+q) = nth d1 (grec1down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_grec1down.
Qed.

Lemma nth_grec1downD_dflt2 d1 d2 p q n:
  nth d1 (grec1down (p+q+n)) (p+q) = nth d2 (grec1down (p+n)) p.
Proof.
rewrite nth_grec1downD (set_nth_default d1 d2) //.
by rewrite size_grec1down ltnS leq_addr.
Qed.

Theorem nth_grec1down_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (grec1down m1) (m1 - n) = nth d2 (grec1down m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm.
- set p := m1 - n in h1' *.
  rewrite -h1' addnC.
  pose q := m2 - m1.
  have Hpq : m2 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m2 = p + q + n.
    by rewrite -Hpq subnK.
  symmetry; exact: nth_grec1downD_dflt2.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n.
    by rewrite -Hpq subnK.
  exact: nth_grec1downD_dflt2.
- rewrite Hm (nth_defaults d1 d2) // size_grec1down.
  exact: leq_ltn_trans (@leq_subr n m2) _.
Qed.

Theorem nth_grec1up_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (grec1up m1) n = nth d2 (grec1up m2) n.
Proof.
move=> h1 h2; rewrite !nth_rev; try by rewrite size_grec1down.
rewrite !size_grec1down !subSS; exact: nth_grec1down_indep.
Qed.

Arguments nth_grec1up_indep [d1 d2 m1 m2 n] _ _.

Lemma nth_grec1up_last (d : T) k : nth d (grec1up k) k = last d (grec1up k).
Proof. by rewrite (last_nth d) size_grec1up. Qed.

Theorem nth_grec1up d n k :
  nth d (grec1up n) k =
  if n < k then d
  else
    if k < size init then nth d init k
    else G (iteri (k - size init) (fun i c => F c (i + size init).+1) a0) k.
Proof.
case: (ltnP n k) => H; first by rewrite nth_default // size_grec1up.
rewrite (nth_grec1up_indep (d2 := d) (m2 := k)) //.
case: (ltnP k (size init)) => H'; first by rewrite grec1up_init // nth_take.
rewrite nth_grec1up_last last_grec1up // head_gloop1; congr G.
by rewrite subnK.
Qed.

Arguments nth_grec1up [d] n k.

End GenDefix1.

Section Defix2.

Variable T : Type.

Variable F : T -> T -> nat -> T.
(** to be instantiated by a function satisfying u(n) = F(u(n-2), u(n-1), n). *)

Fixpoint loop2 (n p : nat) (a b : T) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let c := F a b p in loop2 m p.+1 b c (c :: s)
  end.

Variables a0 a1 : T.

Definition rec2down n :=
  if n is n'.+1 then (loop2 n' 2 a0 a1 [:: a1; a0]) else [:: a0].

Definition rec2up n := rev (rec2down n).

Lemma size_loop2 n p a b s : size (loop2 n p a b s) = n + size s.
Proof. by elim: n p a b s => [//|n IHn] *; rewrite IHn !addSnnS. Qed.

Lemma size_rec2down n : size (rec2down n) = n.+1.
Proof. by case: n => [//|[//|n]]; rewrite size_loop2 addn2. Qed.

Lemma size_rec2up n : size (rec2up n) = n.+1.
Proof. by rewrite size_rev size_rec2down. Qed.

Variable d : T.

Lemma head_loop2S n s a b p :
  hb d s = a -> head d s = b ->
  let s' := (loop2 n p a b s) in
  head d (loop2 n.+1 p a b s) = F (hb d s') (head d s') (n+p).
Proof.
elim: n s a b p => [|n IHn] s a b p Ha Hb; first by rewrite /= Ha Hb.
by rewrite IHn // addSnnS.
Qed.

Lemma head_rec2downSS n :
  head d (rec2down n.+2) =
  F (hb d (rec2down n.+1)) (head d (rec2down n.+1)) n.+2.
Proof. by case: n => [//|n]; rewrite head_loop2S ?addn2. Qed.

Lemma behead_loop2 n s a b p : behead (loop2 n.+1 p a b s) = loop2 n p a b s.
Proof. by elim: n s a b p => [//|n IHn] s a b p; rewrite IHn. Qed.

Lemma behead_rec2down n : behead (rec2down n.+1) = rec2down n.
Proof. by case: n => [//|n]; rewrite behead_loop2. Qed.

(* Let coa k := nth d (rec2up k) k.
Let coa' k := last d (rec2up k). *)

Lemma nth_rec2up_last k : nth d (rec2up k) k = last d (rec2up k).
Proof. by case: k => [//|k]; rewrite (last_nth d) size_rec2up. Qed.

Theorem last_rec2up k :
  last d (rec2up k.+1) = head d (loop2 k 2 a0 a1 [:: a1; a0]).
Proof. by rewrite /rec2up /rec2down last_rev. Qed.

Lemma nth_rec2downSS' k :
  nth d (rec2down k.+2) 0 =
  F (nth d (rec2down k) 0) (nth d (rec2down k.+1) 0) k.+2.
Proof. by rewrite !nth0 -[rec2down k]behead_rec2down head_rec2downSS. Qed.

Lemma nth_rec2upSS' k :
  nth d (rec2up k.+2) k.+2 =
  F (nth d (rec2up k) k) (nth d (rec2up k.+1) k.+1) k.+2.
Proof.
by rewrite /rec2up !nth_rev ?size_rec2down // !subnn nth_rec2downSS'.
Qed.

Lemma nth_rec2downD d1 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d1 (rec2down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec2down.
Qed.

Lemma nth_rec2downD_dflt2 d1 d2 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d2 (rec2down (p+n)) p.
Proof.
rewrite nth_rec2downD (nth_defaults d1 d2) // size_rec2down.
by iomega.
Qed.

Lemma nth_rec2down_indep d1 d2 m1 m2 n : n <= m1 -> n <= m2 ->
  nth d1 (rec2down m1) (m1 - n) = nth d2 (rec2down m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm; last first.
- rewrite Hm (nth_defaults d1 d2) //.
  by rewrite size_rec2down; iomega.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n by rewrite -Hpq subnK.
  exact: nth_rec2downD_dflt2.
- set p := m1 - n in h1' *.
  rewrite -h1' addnC.
  pose q := m2 - m1.
  have Hpq : m2 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec2downD_dflt2.
Qed.

Lemma nth_rec2up_indep d1 d2 m1 m2 n : n <= m1 -> n <= m2 ->
  nth d1 (rec2up m1) n = nth d2 (rec2up m2) n.
Proof.
move=> h1 h2.
rewrite !nth_rev; first last.
- by rewrite size_rec2down /=; move: h1 h2; iomega_le.
- by rewrite size_rec2down /=; move: h1 h2; iomega_le.
rewrite !size_rec2down /= !subSS.
exact: nth_rec2down_indep.
Qed.

End Defix2.

Section RecZ.

(* Helper functions to compute
[1/0!; p/1!; ...; p*(p-1)*...*(p-n+1)/n!] *)

Definition fact_rec (a : Z) (n : nat) : Z := Z.mul a (Z.of_nat n).
Definition fact_seq := rec1up fact_rec 1%Z.

Theorem fact_seq_correct (d : Z) (n k : nat) :
  k <= n ->
  nth d (fact_seq n) k = Z.of_nat (fact k).
Proof.
elim: k => [|k IHk] Hkn; first by rewrite rec1up_co0.
move/(_ (ltnW Hkn)) in IHk.
move: IHk.
rewrite /fact_seq.
rewrite (@nth_rec1up_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@nth_rec1up_indep _ _ _ d d _ k.+1) //.
rewrite nth_rec1upS IHk /fact_rec.
rewrite fact_simpl.
zify; ring.
Qed.

Lemma size_fact_seq n : size (fact_seq n) = n.+1.
Proof. by rewrite size_rec1up. Qed.

Definition falling_rec (p : Z) (a : Z) (n : nat) : Z :=
  (a * (p - (Z.of_nat n) + 1))%Z.
Definition falling_seq (p : Z) := rec1up (falling_rec p) 1%Z.

Canonical Zmul_monoid := Monoid.Law Z.mul_assoc Z.mul_1_l Z.mul_1_r.

Theorem falling_seq_correct (d : Z) (p : Z) (n k : nat) :
  k <= n ->
  nth d (falling_seq p n) k =
  \big[Z.mul/1%Z]_(0 <= i < k) (p - Z.of_nat i)%Z.
Proof.
elim: k => [|k IHk] Hkn; first by rewrite rec1up_co0 big_mkord big_ord0.
move/(_ (ltnW Hkn)) in IHk.
move: IHk.
rewrite /falling_seq.
rewrite (@nth_rec1up_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@nth_rec1up_indep _ _ _ d d _ k.+1) //.
rewrite nth_rec1upS IHk /falling_rec.
rewrite big_nat_recr //=.
congr Z.mul.
zify; ring.
Qed.

Lemma size_falling_seq p n : size (falling_seq p n) = n.+1.
Proof. by rewrite size_rec1up. Qed.

End RecZ.

(** Refinement proofs for rec1, rec2, grec1 *)

Section rec_proofs.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Hypothesis H0 : Rel dv dt.
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).

Lemma grec1up_correct (A := seq V) Fi (F : A -> nat -> A) Gi (G : A -> nat -> V) ai a si s n :
  (forall qi q m, RelP q qi -> RelP (F q m) (Fi qi m)) ->
  (forall qi q m, RelP q qi -> Rel (G q m) (Gi qi m)) ->
  RelP a ai ->
  RelP s si ->
  size s = size si ->
  RelP (grec1up F G a s n) (grec1up Fi Gi ai si n).
Proof.
move=> HF HG Ha Hs Hsize k.
pose s1 := (size (grec1up F G a s n)).-1.
case: (ltnP n k) => Hnk; first by rewrite !nth_default ?size_grec1up.
have H1 : k = (size (grec1up F G a s k)).-1 by rewrite size_grec1up.
have H2 : k = (size (grec1up Fi Gi ai si k)).-1 by rewrite size_grec1up.
rewrite ?(@nth_grec1up_indep _ _ _ _ _ _ dv dv n k k)
  ?(@nth_grec1up_indep _ _ _ _ _ _ dt dt n k k) //.
case: (ltnP k (size s)) => Hk.
- have Hki : k < size si by rewrite -Hsize.
  rewrite ?(grec1up_init _ _ _ Hk, grec1up_init _ _ _ Hki) ?nth_take_dflt ltnn.
  exact: Hs.
- have Hki : size si <= k by rewrite -Hsize.
  rewrite {4}H2 {2}H1 !nth_last !last_grec1up ?head_gloop1 // Hsize.
  apply: HG => j; set l := k - size si.
  elim: l j => [|l IHl] j /=; by [apply: Ha | apply: HF; apply: IHl].
Qed.

Lemma rec1up_correct fi f fi0 f0 n :
  (forall ai a m, Rel a ai -> Rel (f a m) (fi ai m)) ->
  Rel f0 fi0 ->
  RelP (rec1up f f0 n) (rec1up fi fi0 n).
Proof.
move=> Hf Hf0 k.
case: (ltnP n k) => Hnk; first by rewrite !nth_default ?size_rec1up.
have H1 : k = (size (rec1up f f0 k)).-1 by rewrite size_rec1up.
have H2 : k = (size (rec1up fi fi0 k)).-1 by rewrite size_rec1up.
rewrite (@nth_rec1up_indep _ _ _ dv dv n k k) //
        (@nth_rec1up_indep _ _ _ dt dt n k k) //.
rewrite !(nth_rec1up_last, last_rec1up).
rewrite !head_loop1 //.
elim: k Hnk {H1 H2} => [|k IHk] Hnk //=.
apply: Hf; apply: IHk; exact: ltnW.
Qed.

Lemma rec2up_correct fi f fi0 f0 fi1 f1 n :
  (forall ai bi a b m, Rel a ai -> Rel b bi -> Rel (f a b m) (fi ai bi m)) ->
  Rel f0 fi0 ->
  Rel f1 fi1 ->
  RelP (rec2up f f0 f1 n) (rec2up fi fi0 fi1 n).
Proof.
move=> Hf Hf0 Hf1 k.
case: (ltnP n k) => Hn; first by rewrite !nth_default ?size_rec2up.
have H1 : k = (size (rec2up f f0 f1 k)).-1 by rewrite size_rec2up.
have H2 : k = (size (rec2up fi fi0 fi1 k)).-1 by rewrite size_rec2up.
rewrite (@nth_rec2up_indep _ _ _ _ dv dv n k k) //
        (@nth_rec2up_indep _ _ _ _ dt dt n k k) //.
case: k Hn {H1 H2} => [//|k] Hn.
rewrite !(nth_rec2up_last, last_rec2up).
elim: k {-2}k (leqnn k) Hn => [|k IHk] k' Hk' Hn.
- by rewrite leqn0 in Hk'; move/eqP: Hk'->.
- rewrite leq_eqVlt in Hk'; case/orP: Hk'=> Hk'; last exact: IHk =>//.
  move/eqP: (Hk')->; rewrite !head_loop2S //; apply: Hf.
  + case: k IHk Hn Hk' => [|k] IHk Hn Hk' //.
    rewrite /hb !behead_loop2.
    apply: IHk =>//.
    move/eqP in Hk'; rewrite Hk' in Hn; apply: ltnW; exact: ltnW.
  + apply: IHk =>//.
    move/eqP in Hk'; rewrite Hk' in Hn; exact: ltnW.
Qed.

End rec_proofs.
