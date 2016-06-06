(* TODO: coqdoc *)

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssrnat mathcomp.ssreflect.ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types n : nat.

Class I0_class I n := I0 : I n.
Class succ0_class I n := succ0 : I n -> I n.
Class nat_of_class I n := nat_of : I n -> nat.

Section Def.

Context {ord : nat -> Type}.
Context {n : nat}.
Context `{!I0_class ord n, !succ0_class ord n, !nat_of_class ord n}.

(* when j <= n, [iteri_ord j f x] returns
 *
 * for k : ordT n from 0 to (j - 1) do
 *   x := f k x
 * done;
 * x *)
Fixpoint iteri_ord_rec T k i (f : ord n -> T -> T) (x : T) :=
  match k with
    | O => x
    | S k => iteri_ord_rec k (succ0 i) f (f i x)
  end.
Definition iteri_ord T j (f : ord n -> T -> T) x := iteri_ord_rec j I0 f x.

End Def.

Section nat_theory.
Variables (ord : nat -> Type) (n : nat).

Class I0_spec `{!I0_class ord n, !nat_of_class ord n} :=
  I0_prop : nat_of I0 = 0%N.

Class succ0_spec `{!succ0_class ord n, !nat_of_class ord n} :=
  succ0_prop :
  forall i : ord n, ((nat_of i).+1 < n)%N -> nat_of (succ0 i) = (nat_of i).+1.

Class nat_of_spec `{!nat_of_class ord n} :=
  nat_of_prop :
  forall i j : ord n, nat_of i = nat_of j -> i = j.
End nat_theory.
Arguments I0_spec _ _ {_ _}.
Arguments succ0_spec _ _ {_ _}.
Arguments nat_of_spec _ _ {_}.

Section Props.

Context {ord : nat -> Type} {n' : nat}.
Let n := n'.+1.
Context `{!I0_class ord n, !succ0_class ord n, !nat_of_class ord n}.
Context `{!I0_spec ord n, !succ0_spec ord n, !nat_of_spec ord n}.

Lemma iteri_ord_rec_ind M P (f : ord n -> M -> M) :
  forall j, (j <= n)%N ->
  (forall (i : ord n) s,
    (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall (i : ord n) s, (nat_of i <= j)%N ->
    P (nat_of i) s -> P j (iteri_ord_rec (j - nat_of i)%N i f s).
Proof.
move=> j Hj Hind i s Hi H.
move Hk: (j - nat_of i)%N => k.
move: i Hi Hk s H; elim: k => [|k IHk] i Hi Hk s H /=.
{ replace j with (nat_of i); [by []|].
  by apply anti_leq; rewrite Hi /= -subn_eq0 Hk. }
case (ltnP (nat_of i) j) => [Hij|]; [|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply IHk; erewrite (succ0_prop Hsisn) =>//.
  { by rewrite subnS Hk. }
  by apply Hind; [apply leqW|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi' : nat_of i = n'.
{ apply anti_leq; rewrite Hjn Bool.andb_true_r.
  apply (@leq_trans j.-1); [|by rewrite Hj'].
  by rewrite (pred_Sn (nat_of i)); apply /leP /le_pred /leP. }
have Hk' : k = 0%N.
{ apply sym_eq; move: Hk; rewrite Hi' Hj' subSnn; apply eq_add_S. }
by rewrite Hk' Hj' /n /= -Hi'; apply Hind; [rewrite Hi'|].
Qed.

Lemma iteri_ord_ind M P (f : ord n -> M -> M) :
  forall j, (j <= n)%N ->
  (forall (i : ord n) s,
    (nat_of i < n)%N -> P (nat_of i) s -> P (nat_of i).+1 (f i s)) ->
  forall s, P 0%N s -> P j (iteri_ord j f s).
Proof.
move=> j Hj Hind s HP; rewrite /iteri_ord.
replace j with (j - nat_of I0)%N at 2; [|by rewrite I0_prop subn0].
by apply iteri_ord_rec_ind => //; rewrite I0_prop.
Qed.

(* above lemma for P j s := forall i, nat_of i < j -> P i s *)
Lemma iteri_ord_ind_strong M P (f : ord n -> M -> M) :
  (forall (i : ord n) s, (nat_of i < n)%N ->
   (forall (j : ord n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ord n), (nat_of j < (nat_of i).+1)%N -> P j (f i s)) ->
  forall (i : ord n) s, (nat_of i < n)%N -> P i (iteri_ord n f s).
Proof.
move=> Hind i s Hi.
set P' := fun j s => forall (i : ord n), (nat_of i < j)%N -> P i s.
set io := _ _ _ _; suff: P' n io; [by move=> H; apply H, Hi|]; rewrite /io.
by have P0 : P' O s; [|move: P0; apply iteri_ord_ind].
Qed.

Lemma iteri_ord_ind_strong_cases M P (f : ord n -> M -> M) :
  (forall (i : ord n) s, (nat_of i < n)%N ->
   (forall (j : ord n), (nat_of j < nat_of i)%N -> P j s) ->
   forall (j : ord n), (nat_of j < nat_of i)%N -> P j (f i s)) ->
  (forall (i : ord n) s, (nat_of i < n)%N ->
   (forall (j : ord n), (nat_of j < nat_of i)%N -> P j s) -> P i (f i s)) ->
  forall (i : ord n) s, (nat_of i < n)%N -> P i (iteri_ord n f s).
Proof.
move=> H1 H2; apply iteri_ord_ind_strong with (f := f) => // i s Hi H j Hj.
case (ltnP (nat_of j) (nat_of i)) => Hji; [by apply H1|].
have H' : j = i.
{ apply (@nat_of_prop _ _ nat_of_class0) => //; apply anti_leq.
  rewrite Hji Bool.andb_true_r; apply Hj. }
rewrite -H'; apply H2; rewrite H' //.
Qed.

Section Ind2.

Context {ord' : nat -> Type}.
Context `{!I0_class ord' n, !succ0_class ord' n, !nat_of_class ord' n}.
Context `{!I0_spec ord' n, !succ0_spec ord' n}.

Lemma iteri_ord_rec_ind2 M M' P
      (f : ord n -> M -> M) (f' : ord' n -> M' -> M') :
  forall (j : nat), (j <= n)%N ->
  (forall (i : ord n) (i' : ord' n) s s',
    (nat_of i <= n)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall (i : ord n) (i' : ord' n) s s',
    (nat_of i <= j)%N -> nat_of i' = nat_of i ->
    P s s' ->
    P (iteri_ord_rec (j - nat_of i)%N i f s)
      (iteri_ord_rec (j - nat_of i')%N i' f' s').
Proof.
move=> j Hj Hind i i' s s' Hi Hi' H; rewrite Hi'.
move Hk: (j - nat_of i)%N => k.
elim: k i i' Hi Hi' Hk s s' H => // k IHk i i' Hi Hi' Hk s s' H /=.
case (ltnP (nat_of i) j); [move=> Hij|by rewrite /ssrnat.leq Hk].
case (ltnP (nat_of i) n') => Hjn.
{ have Hsisn : ((nat_of i).+1 < n)%N.
  { by move: Hjn; rewrite -(ltn_add2r 1) !addn1. }
  apply: IHk; first by rewrite succ0_prop.
  { rewrite !succ0_prop ?Hi' //. }
  { by rewrite succ0_prop // subnS Hk. }
  apply Hind; by [apply: leq_trans Hi Hj|]. }
have Hj' : j = n.
{ by apply anti_leq; rewrite Hj /=; apply (leq_ltn_trans Hjn). }
have Hi'n : nat_of i = n'.
{ apply anti_leq; rewrite Hjn andbT.
  apply (@leq_trans j.-1); [|by rewrite Hj'].
  by rewrite (pred_Sn (nat_of i)); apply /leP /le_pred /leP. }
have Hk' : k = 0%N.
{ by rewrite Hi'n Hj' subSnn in Hk; case: Hk. }
by rewrite Hk'; apply: Hind =>//; apply (leq_trans Hi).
Qed.

Lemma iteri_ord_ind2 M M' P (f : ord n -> M -> M) (f' : ord' n -> M' -> M') :
  forall (j : nat), (j <= n)%N ->
  (forall (i : ord n) (i' : ord' n) s s',
    (nat_of i <= n)%N -> nat_of i' = nat_of i ->
    P s s' -> P (f i s) (f' i' s')) ->
  forall s s', P s s' -> P (iteri_ord j f s) (iteri_ord j f' s').
Proof.
move=> j Hj Hind s s' HP; rewrite /iteri_ord.
replace j with (j - @nat_of ord _ _ I0)%N at 1; [|by rewrite I0_prop subn0].
replace j with (j - nat_of I0)%N at 2; [|by rewrite I0_prop subn0].
by apply iteri_ord_rec_ind2 => //; rewrite I0_prop.
Qed.

End Ind2.

Variable T : Type.

Lemma iteri_ord_ext j (f g : ord n -> T -> T) x : (j <= n)%N ->
  f =2 g -> iteri_ord j f x = iteri_ord j g x.
Proof.
move=> Hj Hfg; apply iteri_ord_ind2 =>//.
move=> i i' s s' Hi Hi' Hs; rewrite Hfg.
f_equal =>//; eapply nat_of_prop => //.
Qed.

End Props.
