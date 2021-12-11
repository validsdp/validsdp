Require Import ZArith Bool Reals mathcomp.analysis.Rstruct Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype.

Require Import float_spec binary64 float_infnan_spec binary64_infnan.

Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLX.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Core.Round_NE.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Floats.
Require Import Flocq.IEEE754.PrimFloat.

Section Primitive_float_infnan.

  Definition finite (x : float) := is_finite x = true.

  Lemma finite_equiv x : finite (B2Prim x) <-> binary64_infnan.finite x.
  Proof.
    by split; unfold finite, binary64_infnan.finite;
      rewrite is_finite_equiv Prim2B_B2Prim.
  Qed.

  Lemma finite_notnan x : finite x -> is_nan x = false.
  Proof.
    move=> H.
    unfold finite, is_finite in H.
    rewrite Bool.negb_orb in H.
    apply andb_true_iff in H.
    destruct H as (H,_).
    by rewrite -negb_true_iff.
  Qed.

  Lemma finite0 : finite zero.
  Proof. by compute. Qed.

  Lemma finite1 : finite one.
  Proof. by compute. Qed.

  Definition FI2FS (x : float) : FS fis :=
    binary64_infnan.FI2FS (Prim2B x).

  Definition FI2FS_spec x : (FI2FS x <> 0 :> R) -> finite x.
    unfold FI2FS.
    move=> H.
    rewrite <- (B2Prim_Prim2B x).
    rewrite finite_equiv.
    by apply binary64_infnan.FI2FS_spec.
  Qed.

  Lemma FI2FS0 : FI2FS (zero) = F0 fis :> R.
  Proof. by compute. Qed.

  Lemma FI2FS1 : FI2FS (one) = F1 fis :> R.
  Proof. by apply Rinv_r, IZR_neq. Qed.

  Definition firnd (x : R) :=
    B2Prim (binary64_infnan.firnd x).

  Lemma firnd_spec x : finite (firnd x) -> FI2FS (firnd x) = frnd fis x :> R.
  Proof.
    unfold firnd.
    move=> H.
    unfold FI2FS.
    rewrite Prim2B_B2Prim.
    apply binary64_infnan.firnd_spec.
    by rewrite <- finite_equiv.
  Qed.

  Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
  Proof.
    move=> H.
    unfold firnd.
    rewrite finite_equiv.
    by apply binary64_infnan.firnd_spec_f.
  Qed.

  Lemma fiopp_spec_f1 x : finite (-x) -> finite x.
  Proof.
    rewrite -(B2Prim_Prim2B (- x)) -(B2Prim_Prim2B x).
    rewrite opp_equiv Prim2B_B2Prim !finite_equiv.
    apply binary64_infnan.fiopp_spec_f1.
  Qed.

  Lemma fiopp_spec_f x : finite x -> finite (-x).
  Proof.
    rewrite -(B2Prim_Prim2B (- x)) -(B2Prim_Prim2B x).
    rewrite opp_equiv Prim2B_B2Prim !finite_equiv.
    apply binary64_infnan.fiopp_spec_f.
  Qed.

  Lemma fiopp_spec x : finite (-x) -> FI2FS (-x)%float = fopp (FI2FS x) :> R.
  Proof.
    move=> Hf.
    unfold FI2FS.
    rewrite <- (B2Prim_Prim2B x).
    rewrite opp_equiv.
    rewrite !Prim2B_B2Prim.
    apply binary64_infnan.fiopp_spec.
    rewrite -finite_equiv.
    unfold binary64_infnan.fiopp.
    rewrite -opp_equiv.
    by rewrite B2Prim_Prim2B.
  Qed.

  Lemma fiplus_spec_fl x y : finite (x + y) -> finite x.
  Proof.
    rewrite -(B2Prim_Prim2B (x + y)) -(B2Prim_Prim2B x).
    rewrite add_equiv !finite_equiv Prim2B_B2Prim.
    apply binary64_infnan.fiplus_spec_fl.
  Qed.

  Lemma fiplus_spec_fr x y : finite (x + y) -> finite y.
  Proof.
    rewrite -(B2Prim_Prim2B (x + y)) -(B2Prim_Prim2B y).
    rewrite add_equiv !finite_equiv Prim2B_B2Prim.
    apply binary64_infnan.fiplus_spec_fr.
  Qed.

  Lemma fiplus_spec_f x y :
    finite x -> finite y -> Rabs (fplus (FI2FS x) (FI2FS y)) < m -> finite (x + y).
  Proof.
    rewrite -(B2Prim_Prim2B (x + y)) -(B2Prim_Prim2B x) -(B2Prim_Prim2B y).
    rewrite add_equiv !finite_equiv !B2Prim_Prim2B.
    apply binary64_infnan.fiplus_spec_f.
  Qed.

  Lemma fiplus_spec x y :
    finite (x + y) -> FI2FS (x + y)%float = fplus (FI2FS x) (FI2FS y) :> R.
  Proof.
    move=> H.
    rewrite -binary64_infnan.fiplus_spec.
    + by rewrite /FI2FS /fiplus /= add_equiv.
    + move: H.
      by rewrite -(B2Prim_Prim2B (x + y)) finite_equiv add_equiv.
  Qed.

  Lemma fimult_spec_fl x y : finite (x * y) -> finite x.
  Proof.
    rewrite -(B2Prim_Prim2B (x * y)) -(B2Prim_Prim2B x).
    rewrite mul_equiv !finite_equiv Prim2B_B2Prim.
    apply binary64_infnan.fimult_spec_fl.
  Qed.

  Lemma fimult_spec_fr x y : finite (x * y) -> finite y.
  Proof.
    rewrite -(B2Prim_Prim2B (x * y)) -(B2Prim_Prim2B y).
    rewrite mul_equiv !finite_equiv Prim2B_B2Prim.
    apply binary64_infnan.fimult_spec_fr.
  Qed.

  Lemma fimult_spec_f x y :
    finite x -> finite y -> Rabs (fmult (FI2FS x) (FI2FS y)) < m -> finite (x * y).
  Proof.
    rewrite -(B2Prim_Prim2B (x * y)) -(B2Prim_Prim2B x) -(B2Prim_Prim2B y).
    rewrite mul_equiv !finite_equiv !B2Prim_Prim2B.
    apply binary64_infnan.fimult_spec_f.
  Qed.

  Lemma fimult_spec x y :
    finite (x * y) -> FI2FS (x * y)%float = fmult (FI2FS x) (FI2FS y) :> R.
  Proof.
    move=> H.
    rewrite -binary64_infnan.fimult_spec.
    + by rewrite /FI2FS /fimult /= mul_equiv.
    + move: H.
      by rewrite -(B2Prim_Prim2B (x * y)) finite_equiv mul_equiv.
  Qed.

  Lemma fidiv_spec_fl x y : finite (x / y) -> finite y -> finite x.
  Proof.
    rewrite -(B2Prim_Prim2B (x / y)) -(B2Prim_Prim2B x) -(B2Prim_Prim2B y).
    rewrite div_equiv !finite_equiv !Prim2B_B2Prim.
    apply binary64_infnan.fidiv_spec_fl.
  Qed.

  Lemma fidiv_spec_f x y :
    finite x -> (FI2FS y <> 0 :> R) -> Rabs (fdiv (FI2FS x) (FI2FS y)) < m -> finite (x / y).
  Proof.
    rewrite -(B2Prim_Prim2B (x / y)) -(B2Prim_Prim2B x) -(B2Prim_Prim2B y).
    rewrite div_equiv !finite_equiv !B2Prim_Prim2B.
    apply binary64_infnan.fidiv_spec_f.
  Qed.

  Lemma fidiv_spec x y :
    finite (x / y) -> finite y -> FI2FS (x / y)%float = fdiv (FI2FS x) (FI2FS y) :> R.
  Proof.
    move=> H Hy.
    rewrite -binary64_infnan.fidiv_spec.
    + by rewrite /FI2FS /fidiv /= div_equiv.
    + move: H.
      by rewrite -(B2Prim_Prim2B (x / y)) finite_equiv div_equiv.
    + by rewrite -finite_equiv B2Prim_Prim2B.
  Qed.

  Lemma fisqrt_spec_f1 x : finite (sqrt x) -> finite x.
  Proof.
    rewrite -(B2Prim_Prim2B (sqrt x)) -(B2Prim_Prim2B x).
    rewrite sqrt_equiv !finite_equiv !Prim2B_B2Prim.
    apply binary64_infnan.fisqrt_spec_f1.
  Qed.

  Lemma fisqrt_spec_f x : finite x -> FI2FS x >= 0 -> finite (sqrt x).
  Proof.
    rewrite -(B2Prim_Prim2B (sqrt x)) -(B2Prim_Prim2B x).
    rewrite sqrt_equiv !finite_equiv !B2Prim_Prim2B.
    apply binary64_infnan.fisqrt_spec_f.
  Qed.

  Lemma fisqrt_spec x :
    finite (sqrt x) -> FI2FS (sqrt x) = fsqrt (FI2FS x) :> R.
  Proof.
    move=> H.
    rewrite -binary64_infnan.fisqrt_spec.
    + by rewrite /FI2FS /fidiv /= sqrt_equiv.
    + move: H.
      by rewrite -(B2Prim_Prim2B (sqrt x)) finite_equiv sqrt_equiv.
  Qed.

  Lemma ficompare_spec x y :
    finite x -> finite y ->
    (x ?= y)%float = flatten_cmp_opt (Some (Rcompare (FI2FS x) (FI2FS y))).
  Proof.
    rewrite -(B2Prim_Prim2B x) -(B2Prim_Prim2B y) !finite_equiv => Hx Hy.
    rewrite compare_equiv !Prim2B_B2Prim.
    by rewrite -binary64_infnan.ficompare_spec !Prim2B_B2Prim.
  Qed.

  Lemma ficompare_spec_eq x y : (x ?= y)%float = FEq -> FI2FS x = FI2FS y :> R.
  Proof.
    rewrite compare_equiv.
    apply binary64_infnan.ficompare_spec_eq.
  Qed.

  Lemma ficompare_spec_eq_f x y : (x ?= y)%float = FEq -> finite x <-> finite y.
  Proof.
    rewrite compare_equiv => /binary64_infnan.ficompare_spec_eq_f H.
    by rewrite -(B2Prim_Prim2B x) -(B2Prim_Prim2B y) !finite_equiv.
  Qed.

  Definition primitive_float_infnan : Float_infnan_spec :=
    Build_Float_infnan_spec
      finite0
      finite1
      m_ge_2
      FI2FS_spec
      FI2FS0
      FI2FS1
      firnd_spec
      firnd_spec_f
      fiopp_spec
      fiopp_spec_f1
      fiopp_spec_f
      fiplus_spec
      fiplus_spec_fl
      fiplus_spec_fr
      fiplus_spec_f
      fimult_spec
      fimult_spec_fl
      fimult_spec_fr
      fimult_spec_f
      fidiv_spec
      fidiv_spec_fl
      fidiv_spec_f
      fisqrt_spec
      fisqrt_spec_f1
      fisqrt_spec_f
      ficompare_spec
      ficompare_spec_eq
      ficompare_spec_eq_f.

End Primitive_float_infnan.

Section Primitive_float_round_up_infnan.
  Definition fieps := ldexp one (-53)%Z.
  Lemma fieps_spec : eps primitive_float_infnan <= FI2FS fieps.
    unfold fieps.
    cbn.
    unfold Defs.F2R.
    simpl.
    apply (Rmult_le_reg_r (IZR (Z.pow_pos 2 105))).
    { exact/IZR_lt/Zaux.Zpower_pos_gt_0. }
    rewrite Rmult_assoc Rinv_l.
    unfold Z.pow_pos.
    simpl.
    lra.
    apply IZR_neq.
    apply BigNumPrelude.Zlt0_not_eq.
    exact: Zaux.Zpower_pos_gt_0.
  Qed.

  Definition fieta := ldexp one (-1074)%Z.
  Lemma fieta_spec : eta primitive_float_infnan <= FI2FS fieta.
    unfold fieta.
    cbn.
    unfold Defs.F2R.
    simpl.
    apply (Rmult_le_reg_r (IZR (Z.pow_pos 2 1074))).
    { exact/IZR_lt/Zaux.Zpower_pos_gt_0. }
    rewrite Rmult_assoc Rinv_l.
    unfold Z.pow_pos.
    simpl.
    lra.
    apply IZR_neq.
    apply BigNumPrelude.Zlt0_not_eq.
    exact: Zaux.Zpower_pos_gt_0.
  Qed.

  (* TODO: to build a Float_round_up_infnan_spec, we need (next_up x) finite
     to imply x finite, whereas next_up -oo = -max_float *)
  Definition next_up_finite x :=
    match (x ?= neg_infinity)%float with
    | FEq => x
    | _ => next_up x
    end.

  Lemma next_up_finite_spec_f1 x : finite (next_up_finite x) -> finite x.
  Proof.
    unfold next_up_finite => H.
    rewrite -(B2Prim_Prim2B x) finite_equiv.
    move: H; rewrite compare_equiv.
    rewrite -(B2Prim_Prim2B (next_up x)) next_up_equiv.
    rewrite -(B2Prim_Prim2B (match flatten_cmp_opt _ with FEq => x | _ => _ end)).
    rewrite finite_equiv.
    change neg_infinity with (B2Prim (BinarySingleNaN.B754_infinity true)).
    rewrite -(B2Prim_Prim2B x) !Prim2B_B2Prim.
    case (Prim2B x) => [sx|sx| |sx mx ex Bx] //.
    by case sx; simpl; rewrite Prim2B_B2Prim.
  Qed.

  Definition fiplus_up x y := next_up_finite (x + y)%float.

  Lemma fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x.
  Proof.
    by intro Fuxy; apply (fiplus_spec_fl x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y.
  Proof.
    by intro Fuxy; apply (fiplus_spec_fr x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma Hemax : (2 < emax)%Z.
  Proof. now compute. Qed.

  Lemma next_up_finite_spec x :
    finite x ->
    finite (next_up_finite x) ->
    FI2FS (next_up_finite x) = succ radix2 (fexp prec emax) (FI2FS x) :> R.
  Proof.
    rewrite -(B2Prim_Prim2B x) finite_equiv => Fx.
    rewrite B2Prim_Prim2B.
    have -> : next_up_finite x = next_up x.
    { rewrite -(B2Prim_Prim2B x).
      move: Fx.
      case: (Prim2B x) => [[] | [] | |] // s m e Hme.
      unfold next_up_finite.
      change neg_infinity with (B2Prim (BinarySingleNaN.B754_infinity true)).
      by rewrite compare_equiv !Prim2B_B2Prim /=. }
    rewrite -(B2Prim_Prim2B (next_up x)) finite_equiv next_up_equiv.
    move: (Fx) => /(BinarySingleNaN.Bsucc_correct _ _ Hprec Hmax).
    case (Rlt_bool _).
    { move=> [Hsucc [Hsuccf _]] _.
      by rewrite /FI2FS -Hsucc Prim2B_B2Prim. }
    move=> Hsucc_inf Hsucc_fin; exfalso; move: Hsucc_fin.
    by rewrite /binary64_infnan.finite -BinarySingleNaN.is_finite_SF_B2SF Hsucc_inf.
  Qed.

  Lemma fiplus_up_spec x y :
    finite (fiplus_up x y) -> FI2FS x + FI2FS y <= FI2FS (fiplus_up x y).
  Proof.
    move=> Fuxy.
    have Fxy := next_up_finite_spec_f1 _ Fuxy.
    rewrite /fiplus_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fiplus_spec _ _ Fxy) /fplus /frnd /=.
    by apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Definition fimult_up x y := next_up_finite (x * y)%float.

  Lemma fimult_up_spec x y :
    finite (fimult_up x y) -> FI2FS x * FI2FS y <= FI2FS (fimult_up x y).
  Proof.
    move=> Fuxy.
    have Fxy := next_up_finite_spec_f1 _ Fuxy.
    rewrite /fimult_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fimult_spec _ _ Fxy) /fmult /frnd /=.
    by apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Lemma fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x.
  Proof.
    by move=> Fuxy; apply (fimult_spec_fl x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y.
  Proof.
    by move=> Fuxy; apply (fimult_spec_fr x y); apply next_up_finite_spec_f1.
  Qed.

  Definition fidiv_up x y := next_up_finite (x / y)%float.

  Lemma fidiv_up_spec x y :
    finite (fidiv_up x y) -> finite y -> FI2FS x / FI2FS y <= FI2FS (fidiv_up x y).
  Proof.
    move=> Fuxy Fy.
    have Fxy := next_up_finite_spec_f1 _ Fuxy.
    rewrite /fidiv_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fidiv_spec _ _ Fxy Fy) /fdiv /frnd /=.
    by apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Lemma fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x.
  Proof.
    by intro Fuxy; apply (fidiv_spec_fl x y); apply next_up_finite_spec_f1.
  Qed.

  Definition primitive_float_round_up_infnan : Float_round_up_infnan_spec :=
    Build_Float_round_up_infnan_spec
      fieps_spec
      fieta_spec
      fiplus_up_spec
      fiplus_up_spec_fl
      fiplus_up_spec_fr
      fimult_up_spec
      fimult_up_spec_fl
      fimult_up_spec_fr
      fidiv_up_spec
      fidiv_up_spec_fl.

End Primitive_float_round_up_infnan.
