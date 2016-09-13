From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype.
From CoqEAL Require Import hrel param refinements.
Require Import seqmx_complements.  (* for Rord *)

(** * A generic implementation of [iteri] *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments refines A%type B%type R%rel _ _.  (* TODO: il y a un preoblème de scope sur refine *)

Implicit Types n : nat.

(** ** Definition of type classes *)
Class I0_class I n := I0 : I n.
Class succ0_class I n := succ0 : I n -> I n.
Class nat_of_class I n := nat_of : I n -> nat.

Class nat_spec I n `{!I0_class I n, !succ0_class I n, !nat_of_class I n} :=
  {I0_prop : nat_of I0 = 0%N;
   succ0_prop : forall i : I n, ((nat_of i).+1 < n)%N -> nat_of (succ0 i) = (nat_of i).+1;
   nat_of_inj : forall i j : I n, nat_of i = nat_of j -> i = j}.

(** ** Generic definitions *)
Section generic_iteri.

Context {ord : nat -> Type}.
Context {n : nat}.
Context `{!I0_class ord n, !succ0_class ord n, !nat_of_class ord n}.

(** when [j <= n], [iteri_ord j f x] returns
[[
  for k : ordT n from 0 to (j - 1) do
    x := f k x
  done;
  x
]]
*)
Fixpoint iteri_ord_rec T k i (f : ord n -> T -> T) (x : T) :=
  match k with
    | O => x
    | S k => iteri_ord_rec k (succ0 i) f (f i x)
  end.
Definition iteri_ord T j (f : ord n -> T -> T) x := iteri_ord_rec j I0 f x.

End generic_iteri.

(** ** Main instantiations *)
Section theory_nat_of.

Context {n : nat}.
Global Instance I0_ssr : I0_class ordinal n.+1 := ord0.
Global Instance succ0_ssr : succ0_class ordinal n.+1 := fun i => inord i.+1.
Global Instance nat_of_ssr : nat_of_class ordinal n.+1 := @nat_of_ord n.+1.
Global Instance nat_spec_ssr : nat_spec (I := ordinal) (n := n.+1).
Proof.
constructor.
- done.
- by move=> i H; rewrite /nat_of /nat_of_ssr inordK.
- exact: ord_inj.
Qed.

Global Instance I0_instN : I0_class ord_instN n.+1 := O.
Global Instance succ0_instN : succ0_class ord_instN n.+1 := S.
Global Instance nat_of_instN : nat_of_class ord_instN n.+1 := id.
Global Instance nat_spec_instN : nat_spec (I := ord_instN) (n := n.+1).
Proof. done. Qed.

End theory_nat_of.

Section theory_nat_of2.

(** Extra refinement lemmas *)
Lemma Rord_I0 n1 n2 (rn : nat_R n1 n2) :
  Rord (nat_R_S_R rn) I0_ssr (@I0_instN n2).
Proof. done. Qed.

Global Instance Rord_nat_of n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> eq) nat_of_ssr (nat_of_instN (n:=n2)).
Proof. by rewrite refinesE /Rord=> x y <-. Qed.

End theory_nat_of2.

(** ** Generic proofs *)
Section theory_iteri.

Context {n : nat} {ord : nat -> Type}.
Context `{!I0_class ord n.+1, !succ0_class ord n.+1, !nat_of_class ord n.+1}.

(*
(* Definition RordC : 'I_n.+1 -> ord n.+1 -> Prop :=
   (Rord \o fun_hrel nat_of_class0)%rel. *)

(* Useful? *)

Definition RordC (i : 'I_n.+1) (i' : ord n.+1) : Prop :=
  nat_of_ssr i = nat_of i'.
Instance RordC_nat_of : param (RordC ==> Logic.eq) nat_of_ssr nat_of.
Proof. by rewrite paramE. Qed.
 *)

Context `{!nat_spec (I := ord) (n := n.+1)}.

Lemma iteri_ord_rec_ind M P (f : ord n.+1 -> M -> M) :
  forall j, (j <= n.+1)%N ->
  (forall (i : ord n.+1) s,
    (nat_of i < n.+1)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall (i : ord n.+1) s, (nat_of i <= j)%N ->
    P (nat_of i) s -> P j (iteri_ord_rec (j - nat_of i)%N i f s).
Proof.
move=> j Hj Hind i s Hi H.
move Hk: (j - nat_of i)%N => k.
move: i Hi Hk s H; elim: k => [|k IHk] i Hi Hk s H /=.
{ replace j with (nat_of i); [by []|].
  by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. }
case (ltnP (nat_of i) j) => [Hij|]; [|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n) => Hjn.
{ have Hsisn : ((nat_of i).+1 < n.+1)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply IHk.
  by rewrite (succ0_prop Hsisn).
  rewrite (succ0_prop Hsisn) =>//.
  { by rewrite subnS Hk. }
  rewrite (succ0_prop Hsisn) =>//.
  by apply Hind; [apply leqW|]. }
have Hj' : j = n.+1.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi' : nat_of i = n.
{ apply anti_leq; rewrite Hjn Bool.andb_true_r.
  apply (@leq_trans j.-1); [|by rewrite Hj'].
  by rewrite (pred_Sn (nat_of i)); apply /leP /le_pred /leP. }
have Hk' : k = 0%N.
{ apply sym_eq; move: Hk; rewrite Hi' Hj' subSnn; apply eq_add_S. }
by rewrite Hk' Hj' /= -Hi'; apply Hind; [rewrite Hi'|].
Qed.

Lemma iteri_ord_ind M P (f : ord n.+1 -> M -> M) :
  forall j, (j <= n.+1)%N ->
  (forall (i : ord n.+1) s,
    (nat_of i < n.+1)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall s, P 0%N s -> P j (iteri_ord j f s).
Proof.
move=> j Hj Hind s HP; rewrite /iteri_ord.
replace j with (j - nat_of I0)%N at 2.
by apply: iteri_ord_rec_ind =>//; rewrite I0_prop.
by rewrite I0_prop subn0.
Qed.

(* above lemma for P j s := forall i, nat_of i < j -> P i s *)
Lemma iteri_ord_ind_strong M P (f : ord n.+1 -> M -> M) :
  (forall (i : ord n.+1) s, (nat_of i < n.+1)%N ->
   (forall (j : ord n.+1), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ord n.+1), (nat_of j < (nat_of i).+1)%N -> P j (f i s)) ->
  forall (i : ord n.+1) s, (nat_of i < n.+1)%N -> P i (iteri_ord n.+1 f s).
Proof.
move=> Hind i s Hi.
set P' := fun j s => forall (i : ord n.+1), (nat_of i < j)%N -> P i s.
set io := _ _ _ _; suff: P' n.+1 io; first by move=> H; apply H, Hi.
have : P' O s by done.
by eapply iteri_ord_ind.
Qed.

Lemma iteri_ord_ind_strong_cases M P (f : ord n.+1 -> M -> M) :
  (forall (i : ord n.+1) s, (nat_of i < n.+1)%N ->
   (forall (j : ord n.+1), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ord n.+1), (nat_of j < nat_of i)%N -> P j (f i s)) ->
  (forall (i : ord n.+1) s, (nat_of i < n.+1)%N ->
   (forall (j : ord n.+1), (nat_of j < nat_of i)%N -> P j s) -> P i (f i s)) ->
  forall (i : ord n.+1) s, (nat_of i < n.+1)%N -> P i (iteri_ord n.+1 f s).
Proof.
move=> H1 H2; apply iteri_ord_ind_strong with (f := f) => // i s Hi H j Hj.
case (ltnP (nat_of j) (nat_of i)) => Hji; [by apply H1|].
have H' : j = i.
{ apply nat_of_inj => //; apply anti_leq.
  rewrite Hji Bool.andb_true_r; apply Hj. }
rewrite -H'; apply H2; rewrite H' //.
Qed.

Section Ind2.

Context {ord' : nat -> Type}.
Context `{!I0_class ord' n.+1, !succ0_class ord' n.+1, !nat_of_class ord' n.+1}.
Context `{!nat_spec (I := ord') (n := n.+1)}.

Lemma iteri_ord_rec_ind2 M M' P
      (f : ord n.+1 -> M -> M) (f' : ord' n.+1 -> M' -> M') :
  forall (j : nat), (j <= n.+1)%N ->
  (forall (i : ord n.+1) (i' : ord' n.+1) s s',
    (nat_of i <= n.+1)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall (i : ord n.+1) (i' : ord' n.+1) s s',
    (nat_of i <= j)%N -> nat_of i' = nat_of i ->
    P s s' ->
    P (iteri_ord_rec (j - nat_of i)%N i f s)
      (iteri_ord_rec (j - nat_of i')%N i' f' s').
Proof.
move=> j Hj Hind i i' s s' Hi Hi' H; rewrite Hi'.
move Hk: (j - nat_of i)%N => k.
elim: k i i' Hi Hi' Hk s s' H => // k IHk i i' Hi Hi' Hk s s' H /=.
case (ltnP (nat_of i) j); [move=> Hij|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n) => Hjn.
{ have Hsisn : ((nat_of i).+1 < n.+1)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply: IHk; first by rewrite succ0_prop.
  { rewrite !succ0_prop ?Hi' //. }
  { by rewrite succ0_prop // subnS Hk. }
  apply Hind; by [apply: leq_trans Hi Hj|]. }
have Hj' : j = n.+1.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi'n : nat_of i = n.
{ apply anti_leq; rewrite Hjn andbT.
  apply (@leq_trans j.-1); [|by rewrite Hj'].
  by rewrite (pred_Sn (nat_of i)); apply /leP /le_pred /leP. }
have Hk' : k = 0%N.
{ by rewrite Hi'n Hj' subSnn in Hk; case: Hk. }
by rewrite Hk'; apply: Hind =>//; apply (leq_trans Hi).
Qed.

Lemma iteri_ord_ind2 M M' P (f : ord n.+1 -> M -> M) (f' : ord' n.+1 -> M' -> M') :
  forall (j : nat), (j <= n.+1)%N ->
  (forall (i : ord n.+1) (i' : ord' n.+1) s s',
    (nat_of i <= n.+1)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall s s', P s s' -> P (iteri_ord j f s) (iteri_ord j f' s').
Proof.
move=> j Hj Hind s s' HP; rewrite /iteri_ord.
replace j with (j - @nat_of ord _ _ I0)%N at 1; [|by rewrite I0_prop subn0].
replace j with (j - nat_of I0)%N at 2; [|by rewrite I0_prop subn0].
by apply iteri_ord_rec_ind2; rewrite // !I0_prop.
Qed.

End Ind2.

End theory_iteri.
