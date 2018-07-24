Require Import Reals Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import coquelicot_compl Interval_missing.
Require Import mathcomp.ssreflect.bigop.
Require Import ZArith Psatz.
Require Import Fourier_util.
Require Import interval_compl.

(* ultimately, any common results should be put in a different file *)
Require Import bertrand.

(* This file aims to prove results about various integrals, mainly to be    *)
(* used to integrate bounded functions against them at singularities
or at infinity *)


(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* the exponential function *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)

Definition expn lam x := exp (- (lam * x)).

Lemma continuous_expn lam x : continuous (expn lam) x.
Proof.
apply: continuous_comp.
  apply: continuous_opp; apply: continuous_mult.
  exact: continuous_const.
  exact: continuous_id.
exact: continuous_exp.
Qed.

Lemma Rbar_mult_p_l_neg : forall y : R, y < 0 -> Rbar_mult y p_infty = m_infty.
Proof.
move => y Hy.
rewrite /Rbar_mult /Rbar_mult'.
case: (Rle_dec 0 y) => [Hy1|Hy1] // .
exfalso; lra.
Qed.

Lemma Rbar_mult_p_r_neg : forall y : R, y < 0 -> Rbar_mult p_infty y = m_infty.
Proof.
move => y Hy; rewrite Rbar_mult_comm; exact: Rbar_mult_p_l_neg.
Qed.


Lemma is_RInt_gen_exp_infty a lam (Hlam : 0 < lam) : is_RInt_gen (fun x => exp (- (lam * x))) (at_point a) (Rbar_locally p_infty) (exp (-(lam * a)) / lam).
rewrite /is_RInt_gen.
rewrite prodi_to_single_l.
apply: (filterlimi_lim_ext_loc (* (fun x => - (exp(- lam * x) - exp(-lam * a)) / lam) *)).
  exists a.
  move => x Hx.
  apply: (is_RInt_derive (fun x => - exp (-(lam * x)) / lam)).
    move => x0 Hx0.
    by auto_derive => // ; try field; lra.
  move => x0 Hx0; exact: continuous_expn.

rewrite /=.
apply: (filterlim_ext (fun x => minus (exp (-(lam * a)) / lam) (exp (-(lam * x)) / lam))).
move => x;rewrite /minus plus_comm; congr plus. rewrite /opp /=; field; lra.
rewrite /opp /=; field; lra.
rewrite /minus.
apply: (filterlim_comp _ _ _ (fun x => opp (exp (-(lam * x)) / lam)) (fun x => plus (exp (- (lam * a)) / lam) x) (Rbar_locally p_infty) (locally (0)) (locally (exp (- (lam * a)) / lam))); last first.
  rewrite -[X in (_ _ _ (locally X))]Rplus_0_r.
  apply: (continuous_plus (fun x => exp (-(lam*a)) / lam) (fun x => x) 0).
  exact: continuous_const.
  exact: continuous_id.
  apply: filterlim_comp; last first. rewrite -[0]Ropp_involutive. exact: filterlim_opp.
have -> : - 0 = Rbar_mult (Finite 0) (Finite (/ lam)) by rewrite /=; ring.
rewrite /Rdiv.
apply: (is_lim_mult (fun x => exp (-(lam * x))) (fun x => / lam) p_infty 0 (/ lam)) => // .
  apply: is_lim_comp.
    exact: is_lim_exp_m.
    apply: (is_lim_ext (fun x => (-lam) * x)).
      move => y; ring.
    have -> : m_infty = (Rbar_mult (- lam) p_infty).
      by rewrite Rbar_mult_p_l_neg //; lra.
    apply: (is_lim_mult (fun x => (- lam)) (fun x => x) p_infty (-lam) p_infty) => // .
      exact: is_lim_const.
      rewrite /ex_Rbar_mult; lra.
      exists 0 => // .
exact: is_lim_const.
Qed.

Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.

Module ExpNInterval (F : FloatOps with Definition even_radix := true) (I : IntervalOps with Definition bound_type := F.type with Definition precision := F.precision with Definition convert_bound := F.toX).

Module J := IntervalExt I.

Section EffectiveExpN.

Variable prec : F.precision.

(* This is overly verbose for the exponential, but the aim is to
provide guidance for the structure of possibly more complicated
functions *)

Section Infinity.

Variable a : R.
Variable lam : R.
Variable A : I.type.
Variable Lam : I.type.
Let iA := I.convert A.
Let iLam := I.convert Lam.

Hypothesis Hcontainsa : contains iA (Xreal a).
Hypothesis HcontainsLam : contains iLam (Xreal lam).

Definition ExpN := I.div prec (I.exp prec ((I.neg (I.mul prec Lam A)))) (Lam).

Lemma ExpN_correct (Hlam : lam <> 0) : contains (I.convert ExpN) (Xreal ((expn lam a) / lam)).
Proof.
have -> : Xreal (expn lam a / lam) = Xdiv (Xreal (expn lam a)) (Xreal lam).
rewrite/= /Xdiv'.
by move/xreal_ssr_compat.zeroF: Hlam ->.
apply: I.div_correct => // .
apply: J.exp_correct.
apply: J.neg_correct.
exact: J.mul_correct.
Qed.

End Infinity.
End EffectiveExpN.

End ExpNInterval.