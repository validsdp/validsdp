(** * Bounds on the rounding error of summation $\sum_{i=0}^n a_i$#\sum_{i=0}^n a_i#

    The lemmas [*_err_gamma] are of the form
    \exists \theta_i, fl(\sum_i a_i) = \sum_i (1 + \theta_i) a_i /\ \forall i, |\theta_i| <= \gamma_n (sometime required).

    The lemmas [*_err] are of the form
    \exists \theta, |\theta| <= fl(\sum_i a_i) = \sum_i a_i + \theta \sum_i |a_i| /\ |\theta| <= \gamma_n (probably the most useful one).

    The lemmas [*_err_abs] are of the form
    |fl(\sum_i a_i) - \sum_i a_i| <= \gamma_n \sum_i |a_i| (compact but not very convenient).

    The primed versions are for c + \sum_i a_i with no error term on c but rather on fl(\sum_i a_i). *)

Require Import Reals Flocq.Core.Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Export float_spec.

Section Fsum.

Variable fs : Float_spec.

(** Sum [c + \sum a_i] computed in float from left to right. *)
Fixpoint fsum_l2r_rec n (c : FS fs) : FS fs ^ n -> FS fs :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (fplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

(** Sum [\sum a_i] computed in float from left to right. *)
Definition fsum_l2r n : FS fs ^ n -> FS fs :=
  match n with
    | 0%N => fun _ => F0 fs
    | n'.+1 =>
      fun a => fsum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.

Lemma fsum_l2r_rec_eq n (c1 : FS fs) (a1 : FS fs ^ n)
      (c2 : FS fs) (a2 : FS fs ^ n) :
  (c1 = c2 :> R) -> (forall i, a1 i = a2 i :> R) ->
  fsum_l2r_rec c1 a1 = fsum_l2r_rec c2 a2 :> R.
Proof.
elim: n c1 a1 c2 a2 => [//|n IHn] c1 a1 c2 a2 Hc Ha.
by apply IHn; [rewrite /fplus Hc Ha|move=> i; rewrite !ffunE].
Qed.

Lemma fsum_l2r_eq n (a1 : FS fs ^ n) (a2 : FS fs ^ n) :
  (forall i, a1 i = a2 i :> R) -> fsum_l2r a1 = fsum_l2r a2 :> R.
Proof.
case: n a1 a2 => [//|n] a1 a2 Ha.
by apply fsum_l2r_rec_eq; [|move=> i; rewrite !ffunE].
Qed.

Lemma fsum_l2r_rec_r n (c : FS fs) (a : FS fs ^ n.+1) :
  fsum_l2r_rec c a
  = fplus (fsum_l2r_rec c [ffun i : 'I_n => a (inord i)]) (a (inord n)) :> R.
Proof.
elim: n c a => [|n IHn] c a; rewrite /fsum_l2r_rec.
{ simpl; apply f_equal, f_equal2; [by []|].
  by apply f_equal, ord_inj; rewrite inordK. }
rewrite -/fsum_l2r_rec (IHn (fplus _ _) _) ffunE.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE; do 2 apply f_equal.
  { apply Rplus_eq_compat_l; do 2 apply f_equal.
    by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite inordK /=.
  { by apply f_equal2; [by []|apply inordK, (ltn_trans (ltn_ord i))]. }
    apply ltn_trans with i.+2; [by []|].
  rewrite -addn2 -(addn2 n) ltn_add2r; apply ltn_ord. }
do 2 apply f_equal; apply ord_inj; rewrite lift0 inordK // inordK //.
Qed.

Lemma fsum_l2r_r n (a : FS fs ^ n.+2) :
  fsum_l2r a
  = fplus (fsum_l2r [ffun i : 'I_n.+1 => a (inord i)]) (a (inord n.+1)) :> R.
Proof.
rewrite /fsum_l2r fsum_l2r_rec_r.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE; do 2 apply f_equal.
  { by apply ord_inj; rewrite inordK. }
  apply ord_inj; rewrite !lift0 inordK.
  { rewrite inordK // -addn2 -(addn2 n) leq_add2r; apply ltnW, ltn_ord. }
  apply ltnW, ltn_ord. }
rewrite ffunE; do 2 apply f_equal.
apply ord_inj; rewrite lift0 inordK // inordK //.
Qed.

End Fsum.
