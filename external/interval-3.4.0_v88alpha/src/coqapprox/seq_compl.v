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

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Missing results about natural numbers *)

Section NatCompl.

Lemma leq_subnK: forall m n : nat, n <= (n - m) + m.
Proof. elim=> [|n IHn] m; first by rewrite addn0 subn0.
rewrite subnS -addSnnS.
move/(_ m) in IHn.
have H := leqSpred (m - n).
apply: leq_trans IHn _.
exact: leq_add H _.
Qed.

Lemma leq_addLR m n p : n <= p -> (m + n <= p) = (m <= p - n).
Proof. by move => H; rewrite -!subn_eq0 subnBA. Qed.

Lemma leq_addLRI m n p : (m + n <= p) -> (m <= p - n).
Proof.
move=> Hmnp.
- have Hnp : n <= p by exact: leq_trans (leq_addl _ _) Hmnp.
- move: Hmnp; rewrite -!subn_eq0 subnBA //.
Qed.

Lemma ltn_leqN m n : m < n <= m = false.
Proof. by apply/andP=> [[_n n_]]; have:= leq_ltn_trans n_ _n; rewrite ltnn. Qed.

Lemma max1n n : maxn 1 n = n.-1.+1.
Proof. by case: n =>//; case. Qed.

Lemma ltn_leq_pred m n : m < n -> m <= n.-1.
Proof. by move=> H; rewrite -ltnS (ltn_predK H). Qed.

Lemma addn_pred_leqI a b k i :
  (a + b).-1 <= k -> i <= k -> a <= i \/ b <= k - i.
Proof.
move=> Hk Hi; case: (leqP a i) => Ha; [by left|right].
apply: leq_addLRI.
apply: leq_trans _ Hk.
apply: ltn_leq_pred.
by rewrite addnC ltn_add2r.
Qed.

End NatCompl.

(** Missing result(s) about bigops *)

Section bigops.
Lemma big_nat_leq_idx :
  forall (R : Type) (idx : R) (op : Monoid.law idx) (m n : nat) (F : nat -> R),
  n <= m -> (forall i : nat, n <= i < m -> F i = idx) ->
  \big[op/idx]_(0 <= i < n) F i = \big[op/idx]_(0 <= i < m) F i.
Proof.
move=> R idx op m n F Hmn H.
rewrite [RHS](big_cat_nat _ (n := n)) //.
rewrite [in X in _ = op _ X]big_nat_cond.
rewrite [in X in _ = op _ X]big1 ?Monoid.mulm1 //.
move=> i; rewrite andbT; move=> *; exact: H.
Qed.
End bigops.

(** Missing results about lists (aka sequences) *)

Section Head_Last.
Variables (T : Type) (d : T).

Definition hb s := head d (behead s).

Lemma nth_behead s n : nth d (behead s) n = nth d s n.+1.
Proof. by case: s =>//; rewrite /= nth_nil. Qed.

Lemma last_rev : forall s, last d (rev s) = head d s.
Proof. by elim=> [//|s IHs]; rewrite rev_cons last_rcons. Qed.
End Head_Last.

Lemma nth_map_dflt (C : Type) (x0 : C) (f : C -> C) (n : nat) (s : seq C) :
  nth x0 (map f s) n = if size s <= n then x0 else f (nth x0 s n).
Proof.
case: (leqP (size s) n); last exact: nth_map.
by move=> ?; rewrite nth_default // size_map.
Qed.

Section Map2.
Variable C : Type.
Variable x0 : C.
Variable op : C -> C -> C.
Variable op' : C -> C. (* will be [id] or [opp] *)
Fixpoint map2 (s1 : seq C) (s2 : seq C) : seq C :=
  match s1, s2 with
    | _, [::] => s1
    | [::], b :: s4 => op' b :: map2 [::] s4
    | a :: s3, b :: s4 => op a b :: map2 s3 s4
  end.

Lemma size_map2 s1 s2 : size (map2 s1 s2) = maxn (size s1) (size s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs1] s2; elim: s2 => [|x2 s2 IHs2] //=.
- by rewrite IHs2 !max0n.
- by rewrite IHs1 maxnSS.
Qed.

Lemma nth_map2_dflt (n : nat) (s1 s2 : seq C) :
  nth x0 (map2 s1 s2) n =
    match size s1 <= n, size s2 <= n with
    | true, true => x0
    | true, false => op' (nth x0 s2 n)
    | false, true => nth x0 s1 n
    | false, false => op (nth x0 s1 n) (nth x0 s2 n)
    end.
Proof.
elim: s1 s2 n => [|x1 s1 IHs1] s2 n.
  elim: s2 n => [|x2 s2 /= IHs2] n //=; first by rewrite nth_nil.
  by case: n =>[|n] //=; rewrite IHs2.
case: s2 => [|x2 s2] /=.
  by case: leqP => H; last rewrite nth_default.
case: n => [|n] //=.
by rewrite IHs1.
Qed.
End Map2.

Lemma nth_mkseq_dflt (C : Type) (x0 : C) (f : nat -> C) (n i : nat) :
  nth x0 (mkseq f n) i = if n <= i then x0 else f i.
Proof.
case: (leqP n i); last exact: nth_mkseq.
by move=> ?; rewrite nth_default // size_mkseq.
Qed.

Lemma nth_take_dflt (n0 : nat) (T : Type) (x0 : T) (i : nat) (s : seq T) :
  nth x0 (take n0 s) i = if n0 <= i then x0 else nth x0 s i.
Proof.
case: (leqP n0 i) => Hi; last by rewrite nth_take.
by rewrite nth_default // size_take; case: ltnP=>// H'; apply: leq_trans H' Hi.
Qed.

(** Generic results to be instantiated for polynomials' opp, add, sub, mul... *)

Section map_proof.
Variables (V T : Type) (Rel : V -> T -> Prop).
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Variables (vop : V -> V) (top : T -> T).
Hypothesis H0 : Rel dv dt.
Hypothesis H0t : forall v : V, Rel v dt -> Rel (vop v) dt.
Hypothesis H0v : forall t : T, Rel dv t -> Rel dv (top t).
Hypothesis Hop : forall v t, Rel v t -> Rel (vop v) (top t).
Lemma map_correct :
  forall sv st, RelP sv st -> RelP (map vop sv) (map top st).
Proof.
move=> sv st Hnth k; move/(_ k) in Hnth.
rewrite !nth_map_dflt.
do 2![case:ifP]=> A B //; rewrite ?(nth_default _ A) ?(nth_default _ B) in Hnth.
- exact: H0v.
- exact: H0t.
- exact: Hop.
Qed.
End map_proof.

Section map2_proof.
Variables (V T : Type) (Rel : V -> T -> Prop).
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Variables (vop : V -> V -> V) (vop' : V -> V).
Variables (top : T -> T -> T) (top' : T -> T).
Hypothesis H0 : Rel dv dt.

Hypothesis H0t : forall v : V, Rel v dt -> Rel (vop' v) dt.
Hypothesis H0v : forall t : T, Rel dv t -> Rel dv (top' t).
Hypothesis Hop' : forall v t, Rel v t -> Rel (vop' v) (top' t).

Hypothesis H0eq : forall v, Rel v dt -> v = dv.

Hypothesis H0t1 : forall (v1 v2 : V) (t1 : T), Rel v1 t1 ->
                                               Rel v2 dt ->
                                               Rel (vop v1 v2) t1.
Hypothesis H0t2 : forall (v1 v2 : V) (t2 : T), Rel v1 dt ->
                                               Rel v2 t2 ->
                                               Rel (vop v1 v2) (top' t2).
Hypothesis H0v1 : forall (v1 : V) (t1 t2 : T), Rel v1 t1 ->
                                               Rel dv t2 ->
                                               Rel v1 (top t1 t2).
Hypothesis H0v2 : forall (v2 : V) (t1 t2 : T), Rel dv t1 ->
                                               Rel v2 t2 ->
                                               Rel (vop' v2) (top t1 t2).
Hypothesis Hop : forall v1 v2 t1 t2, Rel v1 t1 -> Rel v2 t2 -> Rel (vop v1 v2) (top t1 t2).

Lemma map2_correct :
  forall sv1 sv2 st1 st2,
    RelP sv1 st1 ->
    RelP sv2 st2 ->
    RelP (map2 vop vop' sv1 sv2) (map2 top top' st1 st2).
Proof using H0 H0t H0v Hop' H0eq H0t1 H0t2 H0v1 H0v2 Hop.
move=> sv1 sv2 st1 st2 H1 H2 k; move/(_ k) in H1; move/(_ k) in H2.
rewrite !nth_map2_dflt.
do 4![case:ifP]=> A B C D; rewrite
  ?(nth_default _ A) ?(nth_default _ B) ?(nth_default _ C) ?(nth_default _ D) //
  in H1 H2; try solve
  [exact: H0t1|exact: H0t2|exact: H0v1|exact: H0v2|exact: Hop'|exact: Hop|exact: H0t|exact: H0v].
- rewrite (H0eq (H0t H2)); exact: H1.
- rewrite (H0eq H1); apply: H0v; exact: H2.
Qed.
End map2_proof.

Section fold_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma foldr_correct fv ft sv st :
  RelP sv st ->
  (forall xv yv, Rel xv dt -> Rel yv dt -> Rel (fv xv yv) dt) ->
  (forall xt yt, Rel dv xt -> Rel dv yt -> Rel dv (ft xt yt)) ->
  (forall xv xt yv yt, Rel xv xt -> Rel yv yt -> Rel (fv xv yv) (ft xt yt)) ->
  Rel (foldr fv dv sv) (foldr ft dt st).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs => [ | xv sv IH1] st Hs /=.
- elim: st Hs => [ | xt st IH2] Hs //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change dt with (foldr ft dt [::]).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.

Lemma seq_foldr_correct fv ft sv st (zv := [::]) (zt := [::]) :
  RelP sv st ->
  (forall xv yv, Rel xv dt -> RelP yv zt -> RelP (fv xv yv) zt) ->
  (forall xt yt, Rel dv xt -> RelP zv yt -> RelP zv (ft xt yt)) ->
  (forall xv xt yv yt, Rel xv xt -> RelP yv yt -> RelP (fv xv yv) (ft xt yt)) ->
  RelP (foldr fv zv sv) (foldr ft zt st).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs => [ | xv sv IH1] st Hs /=.
- elim: st Hs => [ | xt st IH2] Hs //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change zt with (foldr ft zt [::]).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.

End fold_proof.

Section Foldri.
Variables (T R : Type) (f : T -> nat -> R -> R) (z0 : R).

Fixpoint foldri (s : seq T) (i : nat) : R :=
  match s with
  | [::] => z0
  | x :: s' => f x i (foldri s' i.+1)
  end.
End Foldri.

Section foldri_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma seq_foldri_correct fv ft sv st (zv := [::]) (zt := [::]) i :
  RelP sv st ->
  (* RelP zv zt -> *)
  (forall xv yv i, Rel xv dt -> RelP yv zt -> RelP (fv xv i yv) zt) ->
  (forall xt yt i, Rel dv xt -> RelP zv yt -> RelP zv (ft xt i yt)) ->
  (forall xv xt yv yt i, Rel xv xt -> RelP yv yt -> RelP (fv xv i yv) (ft xt i yt)) ->
  RelP (foldri fv zv sv i) (foldri ft zt st i).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs i => [ | xv sv IH1] st Hs i /=.
- elim: st Hs i => [ | xt st IH2] Hs i //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change zt with (foldri ft zt [::] i.+1).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.
End foldri_proof.

Section mkseq_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma mkseq_correct fv ft (mv mt : nat) :
  (forall k : nat, Rel (fv k) (ft k)) ->
  (* the following 2 hyps hold if mv <> mt *)
  (forall k : nat, mv <= k < mt -> fv k = dv) ->
  (forall k : nat, mt <= k < mv -> fv k = dv) ->
  RelP (mkseq fv mv) (mkseq ft mt).
Proof.
move=> Hk Hv1 Hv2 k; rewrite !nth_mkseq_dflt.
do 2![case: ifP]=> A B.
- exact: H0.
- by rewrite -(Hv1 k) // B ltnNge A.
- by rewrite (Hv2 k) // A ltnNge B.
- exact: Hk.
Qed.
End mkseq_proof.

Section misc_proofs.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Lemma set_nth_correct sv st bv bt n :
  RelP sv st ->
  Rel bv bt ->
  RelP (set_nth dv sv n bv) (set_nth dt st n bt).
Proof. by move=> Hs Hb k; rewrite !nth_set_nth /=; case: ifP. Qed.

Lemma drop_correct sv st n :
  RelP sv st ->
  RelP (drop n sv) (drop n st).
Proof. by move=> Hs k; rewrite !nth_drop; apply: Hs. Qed.

Hypothesis H0 : Rel dv dt.
Lemma ncons_correct sv st n :
  RelP sv st ->
  RelP (ncons n dv sv) (ncons n dt st).
Proof. by move=> Hs k; rewrite !nth_ncons; case: ifP. Qed.

End misc_proofs.
