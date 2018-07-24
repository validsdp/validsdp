Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.fintype mathcomp.ssreflect.bigop.
Require Import poly_datatypes Rstruct.

Import PolR.

Lemma Rpol_continuous p (x : R) : continuous (horner tt p) x.
Proof.
have Hext : forall t, foldr (fun a b =>
                                (b * t) + a) 0 (toSeq p) =
                      horner tt p t  => [t|].
by rewrite PolR.horner_seq.
apply: (continuous_ext _ _ _ Hext). (* implicit parameters? *)
elim: (toSeq p) => [|a q HI] /=.
- exact: continuous_const.
- apply: continuous_plus; last by exact: continuous_const.
  by apply: continuous_mult => //; exact: continuous_id.
Qed.

Lemma Rpol_integrable p (x1 x2 : R) : ex_RInt (horner tt p) x1 x2.
Proof.
apply: ex_RInt_continuous => x _.
exact: Rpol_continuous.
Qed.

Lemma ex_Rpol_derive p (x : R) : ex_derive (horner tt p) x.
Proof.
have Hext : forall t, foldr (fun a b =>
                                (b * t) + a) 0 (toSeq p) =
                      horner tt p t  => [t|].
by rewrite PolR.horner_seq.
apply: (ex_derive_ext _ _ _ Hext). (* implicit parameters? *)
elim: (toSeq p) => [|a q HI] /=.
- exact: ex_derive_const.
- apply: ex_derive_plus; last by exact: ex_derive_const.
  by apply: ex_derive_mult => //; exact: ex_derive_id.
Qed.


(* Check Derive_sum_n. *)

Lemma ex_derive_big I (s : seq I) :
   forall
   (f : I -> R -> R)
   (x : R),
   (forall k : I, ex_derive (f k) x) ->
 ex_derive (fun x0 : Rdefinitions.R => \big[Rplus/0]_(i <- s) f i x0) x.
Proof.
move => f x Hf.
elim: s => [ | a b Hrec] => /= .
apply: (ex_derive_ext (fun x0 => 0)) => [t|]; first by rewrite big_nil.
apply: ex_derive_const.
apply: (ex_derive_ext (fun t => f a t + \big[Rplus/0]_(j <- b) f j t)).
  by move => t; rewrite big_cons.
apply: ex_derive_plus.
  by apply: Hf.
by apply: Hrec.
Qed.

Lemma derive_big I (s : seq I) :
   forall
   (f : I -> R -> R)
   (x : R),
   (forall k : I, ex_derive (f k) x) ->
   Derive (fun y : Rdefinitions.R =>
             \big[Rplus/0]_(i <- s) (f i y)) x =
   \big[(fun _ : unit => Rplus) tt/0]_(i <- s) ((Derive (f i)) x).
Proof.
move => f x Hf.
elim: s => [ | a b Hrec] => /= .
- rewrite (Derive_ext _ (fun x0 => 0)) => [|t].
    by rewrite big_nil Derive_const.
  by rewrite big_nil.
- rewrite (Derive_ext _ (fun t => f a t + \big[Rplus/0]_(j <- b) f j t)).
  + rewrite Derive_plus ?big_cons.
     * congr Rplus.
       by rewrite Hrec.
     * by apply: Hf.
     * by apply: ex_derive_big.
  + move => t.
    by rewrite big_cons.
Qed.

Lemma horner_primitive (c : R) (p : T) (t : R):  horner tt (primitive tt c p) t =
c + \big[Rplus/0]_(0 <= i < (size p)) (nth (primitive tt c p) i.+1 *
                                                 powerRZ t (Z.of_nat i.+1)).
Proof.
rewrite hornerE size_primitive big_nat_recl //.
congr (_ + _); first by rewrite /= Rmult_1_r.
by apply: eq_big_nat => i Hi; rewrite Interval_missing.pow_powerRZ.
Qed.

Lemma Rpol_derive p (c : R) (x : R) : Derive (horner tt (primitive tt c p)) x = horner tt p x.
Proof.
have derMonom : forall k : (* ordinal_finType (size p), *) nat,
   ex_derive
     (fun y : Rdefinitions.R =>
      nth (primitive tt c p) k.+1 * powerRZ y (Z.of_nat k.+1)) x.
move => k.
apply: ex_derive_mult.
apply: ex_derive_const.
apply: (ex_derive_ext (fun x => x ^ (k.+1))).
  by move => t; rewrite -Interval_missing.pow_powerRZ.
apply: ex_derive_pow; apply: ex_derive_id.
rewrite hornerE.
rewrite (Derive_ext _ _  _ (horner_primitive c p)).
(* visibily there lack some implicit parameters *)
set X := RHS.
have -> : X = 0 + X by rewrite Rplus_0_l.
rewrite Derive_plus; [ |by apply: ex_derive_const |].
- congr (_ + _); first by apply: Derive_const.
rewrite derive_big.
rewrite [LHS]big_nat_cond /X [RHS]big_nat_cond.
apply: eq_bigr => i; rewrite andbT => Hi.
rewrite Derive_mult.
have -> :
  Derive (fun _ : Rdefinitions.R => nth (primitive tt c p) i.+1) x = 0.
  by apply: Derive_const.
ring_simplify.
rewrite (Derive_ext _ (fun x => x ^ (i.+1))); last first.
 by move => t; rewrite -Interval_missing.pow_powerRZ.
rewrite nth_primitive ifF /int_coeff => //.
rewrite Derive_pow ?Derive_id -?pred_Sn. field.
apply: not_0_INR => // .
exact: ex_derive_id.
by apply/negbTE; rewrite -leqNgt; case/andP: Hi.
apply: ex_derive_const.
apply: (ex_derive_ext (fun x => x ^ (i.+1))).
  by move => t; rewrite -Interval_missing.pow_powerRZ.
apply: ex_derive_pow; apply: ex_derive_id.
by [].
by apply: ex_derive_big.
Qed.

Lemma Rpol_integral_0 (x1 x2 : R) (p : T) : RInt (horner tt p) x1 x2 =
            horner tt (primitive tt R0 p) x2 - horner tt (primitive tt R0 p) x1.
Proof.
apply is_RInt_unique.
apply: (is_RInt_ext (Derive (horner tt (primitive tt R0 p)))).
by move => x _; rewrite  Rpol_derive.
apply: is_RInt_derive.
move => x _; apply: Derive_correct; apply: ex_Rpol_derive.
move => x _. apply: (continuous_ext (horner tt p) ) => [t|] .
  by rewrite Rpol_derive.
exact: Rpol_continuous.
Qed.
