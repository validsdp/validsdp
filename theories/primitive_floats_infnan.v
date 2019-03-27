Require Import float_spec binary64 float_infnan_spec binary64_infnan.
Require Import ZArith Bool.

From Flocq.Core
Require Import Raux Generic_fmt FLX FLT Ulp Round_NE.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits.

Require Import Float.
Require Import FlocqNativeLayer.

Require Import Psatz.

Section Primitive_float_infnan.

  Definition nan_pl : { pl: bool * positive | Binary.nan_pl prec (snd pl) = true } :=
    exist _ (false, 1%positive) (eq_refl true).

  Definition ex_nan : {f : Binary.binary_float prec emax |
                       Binary.is_nan prec emax f = true} :=
    exist _ (Binary.B754_nan (fst (proj1_sig nan_pl)) (snd (proj1_sig nan_pl))
                             (proj2_sig nan_pl)) (eq_refl true).

  Definition finite (x : float) := is_finite x = true.

  Lemma finite_equiv x : finite (B2Prim x) <-> binary64_infnan.finite x.
    split; unfold finite, binary64_infnan.finite; intro.
    now rewrite <- is_finite_spec.
    now rewrite is_finite_spec.
  Qed.

  Lemma finite_notnan x : finite x -> is_nan x = false.
    intro H.
    unfold finite, is_finite in H.
    rewrite Bool.negb_orb in H.
    apply andb_true_iff in H.
    destruct H as (H,_).
    now rewrite negb_true_iff in H.
  Qed.

  Lemma finite0 : finite zero.
    now compute.
  Qed.

  Lemma finite1 : finite one.
    now compute.
  Qed.

  Definition FI2FS (x : float) : FS fis :=
    binary64_infnan.FI2FS (Prim2B nan_pl x).

  Definition FI2FS_spec x : (FI2FS x <> 0 :> R) -> finite x.
    unfold FI2FS.
    intro.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite finite_equiv.
    now apply binary64_infnan.FI2FS_spec.
  Qed.

  Lemma FI2FS0 : FI2FS (zero) = F0 fis :> R.
    now compute.
  Qed.

  Lemma FI2FS1 : FI2FS (one) = F1 fis :> R.
    apply Rinv_r.
    now apply IZR_neq.
  Qed.

  Definition firnd (x : R) :=
    B2Prim (binary64_infnan.firnd x).

  Lemma firnd_spec x : finite (firnd x) -> FI2FS (firnd x) = frnd fis x :> R.
    unfold firnd.
    intro.
    unfold FI2FS.
    rewrite Prim2B_B2Prim_notnan.
    - apply binary64_infnan.firnd_spec.
      now rewrite <- finite_equiv.
    - apply finite_notnan in H.
      now rewrite <- is_nan_spec.
  Qed.

  Lemma firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x).
    intro.
    unfold firnd.
    rewrite finite_equiv.
    now apply binary64_infnan.firnd_spec_f.
  Qed.

  Lemma fiopp_spec_f1 x : finite (-x) -> finite x.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPopp_Bopp unop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fiopp_spec_f1.
  Qed.

  Lemma fiopp_spec_f x : finite x -> finite (-x).
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPopp_Bopp unop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fiopp_spec_f.
  Qed.

  Lemma fiopp_spec x : finite (-x) -> FI2FS (-x)%float = fopp (FI2FS x) :> R.
    intro Hf.
    unfold FI2FS.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPopp_Bopp unop_nan_pl64).
    rewrite !Prim2B_B2Prim_notnan.
    - apply binary64_infnan.fiopp_spec.
      rewrite <- finite_equiv.
      unfold binary64_infnan.fiopp, b64_opp.
      rewrite <- FPopp_Bopp.
      now rewrite B2Prim_Prim2B.
    - rewrite <- is_nan_spec.
      rewrite B2Prim_Prim2B.
      apply fiopp_spec_f1 in Hf.
      now apply finite_notnan in Hf.
    - rewrite <- is_nan_spec.
      rewrite <- FPopp_Bopp.
      rewrite B2Prim_Prim2B.
      now apply finite_notnan in Hf.
  Qed.

  Lemma fiplus_spec_fl x y : finite (x + y) -> finite x.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPplus_Bplus binop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fiplus_spec_fl.
  Qed.

  Lemma fiplus_spec_fr x y : finite (x + y) -> finite y.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPplus_Bplus binop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fiplus_spec_fr.
  Qed.

  Lemma fiplus_spec_f x y : finite x -> finite y -> Rabs (fplus (FI2FS x) (FI2FS y)) < m -> finite (x + y).
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPplus_Bplus binop_nan_pl64).
    rewrite !finite_equiv.
    unfold FI2FS.
    intros Hx Hy.
    rewrite !Prim2B_B2Prim_notnan.
    - now apply binary64_infnan.fiplus_spec_f.
    - rewrite <- finite_equiv in Hy.
      apply finite_notnan in Hy.
      now rewrite is_nan_spec in Hy.
    - rewrite <- finite_equiv in Hx.
      apply finite_notnan in Hx.
      now rewrite is_nan_spec in Hx.
  Qed.

  Lemma fiplus_spec x y :
    finite (x + y) -> FI2FS (x + y)%float = fplus (FI2FS x) (FI2FS y) :> R.
    intro.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPplus_Bplus binop_nan_pl64).
    unfold FI2FS.
    rewrite !Prim2B_B2Prim_notnan.
    - rewrite <- binary64_infnan.fiplus_spec.
      + now unfold fiplus, prec, emax.
      + rewrite <- finite_equiv. unfold fiplus, b64_plus.
        rewrite <- FPplus_Bplus.
        now rewrite !B2Prim_Prim2B.
    - apply fiplus_spec_fr in H.
      apply finite_notnan in H.
      rewrite <- is_nan_spec.
      now rewrite B2Prim_Prim2B.
    - apply fiplus_spec_fl in H.
      apply finite_notnan in H.
      rewrite <- is_nan_spec.
      now rewrite B2Prim_Prim2B.
    - apply finite_notnan in H.
      rewrite <- (B2Prim_Prim2B nan_pl x) in H.
      rewrite <- (B2Prim_Prim2B nan_pl y) in H.
      rewrite (FPplus_Bplus binop_nan_pl64) in H.
      now rewrite is_nan_spec in H.
  Qed.

  Lemma fimult_spec_fl x y : finite (x * y) -> finite x.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPmult_Bmult binop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fimult_spec_fl.
  Qed.

  Lemma fimult_spec_fr x y : finite (x * y) -> finite y.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPmult_Bmult binop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fimult_spec_fr.
  Qed.

  Lemma fimult_spec_f x y : finite x -> finite y -> Rabs (fmult (FI2FS x) (FI2FS y)) < m -> finite (x * y).
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPmult_Bmult binop_nan_pl64).
    rewrite !finite_equiv.
    unfold FI2FS.
    intros Hx Hy.
    rewrite !Prim2B_B2Prim_notnan.
    - now apply binary64_infnan.fimult_spec_f.
    - rewrite <- finite_equiv in Hy.
      apply finite_notnan in Hy.
      now rewrite is_nan_spec in Hy.
    - rewrite <- finite_equiv in Hx.
      apply finite_notnan in Hx.
      now rewrite is_nan_spec in Hx.
  Qed.

  Lemma fimult_spec x y :
    finite (x * y) -> FI2FS (x * y)%float = fmult (FI2FS x) (FI2FS y) :> R.
    intro.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPmult_Bmult binop_nan_pl64).
    unfold FI2FS.
    rewrite !Prim2B_B2Prim_notnan.
    - rewrite <- binary64_infnan.fimult_spec.
      + now unfold fimult, prec, emax.
      + rewrite <- finite_equiv. unfold fimult, b64_mult.
        rewrite <- FPmult_Bmult.
        now rewrite !B2Prim_Prim2B.
    - apply fimult_spec_fr in H.
      apply finite_notnan in H.
      rewrite <- is_nan_spec.
      now rewrite B2Prim_Prim2B.
    - apply fimult_spec_fl in H.
      apply finite_notnan in H.
      rewrite <- is_nan_spec.
      now rewrite B2Prim_Prim2B.
    - apply finite_notnan in H.
      rewrite <- (B2Prim_Prim2B nan_pl x) in H.
      rewrite <- (B2Prim_Prim2B nan_pl y) in H.
      rewrite (FPmult_Bmult binop_nan_pl64) in H.
      now rewrite is_nan_spec in H.
  Qed.

  Lemma fidiv_spec_fl x y : finite (x / y) -> finite y -> finite x.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPdiv_Bdiv binop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fidiv_spec_fl.
  Qed.

  Lemma fidiv_spec_f x y : finite x -> (FI2FS y <> 0 :> R) -> Rabs (fdiv (FI2FS x) (FI2FS y)) < m -> finite (x / y).
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPdiv_Bdiv binop_nan_pl64).
    rewrite !finite_equiv.
    unfold FI2FS.
    intros Hx Hy.
    rewrite B2Prim_Prim2B in Hy.
    rewrite !Prim2B_B2Prim_notnan.
    - now apply binary64_infnan.fidiv_spec_f.
    - destruct (Prim2B _ y) ; auto.
      exfalso.
      now apply Hy.
    - rewrite <- finite_equiv in Hx.
      apply finite_notnan in Hx.
      now rewrite is_nan_spec in Hx.
  Qed.

  Lemma fidiv_spec x y : finite (x / y) -> finite y -> FI2FS (x / y)%float = fdiv (FI2FS x) (FI2FS y) :> R.
    intros H Hy.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite (FPdiv_Bdiv binop_nan_pl64).
    unfold FI2FS.
    rewrite !Prim2B_B2Prim_notnan.
    - rewrite <- binary64_infnan.fidiv_spec.
      + now unfold fidiv, prec, emax.
      + rewrite <- finite_equiv.
        unfold fidiv, b64_div.
        rewrite <- FPdiv_Bdiv.
        now rewrite !B2Prim_Prim2B.
      + rewrite <- finite_equiv.
        now rewrite B2Prim_Prim2B.
    - apply finite_notnan in Hy.
      rewrite <- is_nan_spec.
      now rewrite B2Prim_Prim2B.
    - apply (fidiv_spec_fl x y) in H.
      + apply finite_notnan in H.
        rewrite <- is_nan_spec.
        now rewrite B2Prim_Prim2B.
      + assumption.
    - apply finite_notnan in H.
      rewrite <- (B2Prim_Prim2B nan_pl x) in H.
      rewrite <- (B2Prim_Prim2B nan_pl y) in H.
      rewrite (FPdiv_Bdiv binop_nan_pl64) in H.
      now rewrite is_nan_spec in H.
  Qed.

  Lemma fisqrt_spec_f1 x : finite (sqrt x) -> finite x.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPsqrt_Bsqrt unop_nan_pl64).
    rewrite !finite_equiv.
    apply binary64_infnan.fisqrt_spec_f1.
  Qed.

  Lemma fisqrt_spec_f x : finite x -> FI2FS x >= 0 -> finite (sqrt x).
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPsqrt_Bsqrt unop_nan_pl64).
    rewrite !finite_equiv.
    unfold FI2FS.
    rewrite B2Prim_Prim2B.
    apply binary64_infnan.fisqrt_spec_f.
  Qed.

  Lemma fisqrt_spec x : finite (sqrt x) -> FI2FS (sqrt x) = fsqrt (FI2FS x) :> R.
    intro Hf.
    unfold FI2FS.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite (FPsqrt_Bsqrt unop_nan_pl64).
    rewrite !Prim2B_B2Prim_notnan.
    - apply binary64_infnan.fisqrt_spec.
      rewrite <- finite_equiv.
      unfold binary64_infnan.fisqrt, b64_sqrt.
      rewrite <- FPsqrt_Bsqrt.
      now rewrite B2Prim_Prim2B.
    - rewrite <- is_nan_spec.
      rewrite B2Prim_Prim2B.
      apply fisqrt_spec_f1 in Hf.
      now apply finite_notnan in Hf.
    - rewrite <- is_nan_spec.
      rewrite <- FPsqrt_Bsqrt.
      rewrite B2Prim_Prim2B.
      now apply finite_notnan in Hf.
  Qed.

  Lemma ficompare_spec x y : finite x -> finite y -> (x ?= y)%float = flatten_cmp_opt (Some (Rcompare (FI2FS x) (FI2FS y))).
    intros Hx Hy.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !B2Prim_Prim2B.
    apply binary64_infnan.ficompare_spec; rewrite <- finite_equiv;
      now rewrite B2Prim_Prim2B.
  Qed.

  Lemma ficompare_spec_eq x y : (x ?= y)%float = FEq -> FI2FS x = FI2FS y :> R.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !B2Prim_Prim2B.
    now apply binary64_infnan.ficompare_spec_eq.
  Qed.

  Lemma ficompare_spec_eq_f x y : (x ?= y)%float = FEq -> finite x <-> finite y.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !finite_equiv.
    now apply binary64_infnan.ficompare_spec_eq_f.
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
    {
      apply IZR_lt.
      apply Zpower_pos_gt_0.
      lia.
    }
    rewrite Rmult_assoc, Rinv_l.
    unfold Z.pow_pos.
    simpl.
    lra.
    apply IZR_neq.
    apply BigNumPrelude.Zlt0_not_eq.
    apply Zpower_pos_gt_0.
    lia.
  Qed.

  Definition fieta := ldexp one (-1074)%Z.
  Lemma fieta_spec : eta primitive_float_infnan <= FI2FS fieta.
    unfold fieta.
    cbn.
    unfold Defs.F2R.
    simpl.
    apply (Rmult_le_reg_r (IZR (Z.pow_pos 2 1074))).
    {
      apply IZR_lt.
      apply Zpower_pos_gt_0.
      lia.
    }
    rewrite Rmult_assoc, Rinv_l.
    unfold Z.pow_pos.
    simpl.
    lra.
    apply IZR_neq.
    apply BigNumPrelude.Zlt0_not_eq.
    apply Zpower_pos_gt_0.
    lia.
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
    unfold next_up_finite.
    rewrite <- (SF2Prim_Prim2SF (next_up x)).
    rewrite next_up_SFsucc.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    change neg_infinity with (B2Prim (Binary.B754_infinity true)).
    rewrite FPcompare_Bcompare.
    case (Prim2B nan_pl x);
      [now intro s; case s|now intro s; case s|now easy|].
    now intros s m e Hme _; unfold finite; rewrite is_finite_spec.
  Qed.

  Definition fiplus_up x y := next_up_finite (x + y)%float.

  Lemma fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x.
  Proof.
    now intro Fuxy; apply (fiplus_spec_fl x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y.
  Proof.
    now intro Fuxy; apply (fiplus_spec_fr x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma next_up_finite_spec x :
    finite x ->
    finite (next_up_finite x) ->
    FI2FS (next_up_finite x) = succ radix2 (fexp prec emax) (FI2FS x) :> R.
  Proof.
    intros Fx.
    assert (H : next_up_finite x = next_up x); [|rewrite H; clear H].
    { revert Fx.
      rewrite <-(B2Prim_Prim2B nan_pl x).
      case (Prim2B nan_pl x);
        [now intro s; case s|now intro s; case s|now intro s; case s|].
      intros s m e Hme.
      unfold next_up_finite.
      change neg_infinity with (B2Prim (Binary.B754_infinity true)).
      now rewrite FPcompare_Bcompare. }
    revert Fx.
    rewrite <-(B2Prim_Prim2B nan_pl x).
    pose (succ_nan := fun _ : Binary.binary_float prec emax => ex_nan).
    rewrite (FPnext_up_Bsucc succ_nan).
    unfold finite; rewrite !is_finite_spec.
    unfold FI2FS, binary64_infnan.FI2FS; simpl.
    intro Fx.
    generalize (Bsucc_correct prec emax FlocqNativeLayer.prec_gt_0 Hmax Hemax
                succ_nan (Prim2B nan_pl x) Fx).
    case (Rlt_bool _).
    { intros (Hsucc, (Hsuccf, _)) _.
      rewrite Prim2B_B2Prim_notnan;
        [|now revert Hsuccf; case (Bsucc _ _ _ _ _ _ _)].
      fold prec; fold emax; rewrite Hsucc.
      now rewrite Prim2B_B2Prim_notnan; [|revert Hsuccf; case (Prim2B _ _)]. }
    intros Hsucc_inf Hsucc_fin; exfalso; revert Hsucc_fin.
    rewrite <-(Binary.FF2B_B2FF_valid prec emax _).
    now rewrite Binary.is_finite_FF2B,  Hsucc_inf.
  Qed.

  Lemma fiplus_up_spec x y : finite (fiplus_up x y) -> FI2FS x + FI2FS y <= FI2FS (fiplus_up x y).
  Proof.
    intro Fuxy.
    assert (Fxy := next_up_finite_spec_f1 _ Fuxy).
    unfold fiplus_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fiplus_spec _ _ Fxy); unfold fplus, frnd; simpl.
    now apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Definition fimult_up x y := next_up_finite (x * y)%float.

  Lemma fimult_up_spec x y : finite (fimult_up x y) -> FI2FS x * FI2FS y <= FI2FS (fimult_up x y).
    intro Fuxy.
    assert (Fxy := next_up_finite_spec_f1 _ Fuxy).
    unfold fimult_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fimult_spec _ _ Fxy); unfold fmult, frnd; simpl.
    now apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Lemma fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x.
  Proof.
    now intro Fuxy; apply (fimult_spec_fl x y); apply next_up_finite_spec_f1.
  Qed.

  Lemma fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y.
  Proof.
    now intro Fuxy; apply (fimult_spec_fr x y); apply next_up_finite_spec_f1.
  Qed.

  Definition fidiv_up x y := next_up_finite (x / y)%float.

  Lemma fidiv_up_spec x y : finite (fidiv_up x y) -> finite y -> FI2FS x / FI2FS y <= FI2FS (fidiv_up x y).
    intros Fuxy Fy.
    assert (Fxy := next_up_finite_spec_f1 _ Fuxy).
    unfold fidiv_up.
    rewrite (next_up_finite_spec _ Fxy Fuxy).
    rewrite (fidiv_spec _ _ Fxy Fy); unfold fdiv, frnd; simpl.
    now apply succ_round_ge_id; [apply FLT_exp_valid|apply valid_rnd_N].
  Qed.

  Lemma fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x.
  Proof.
    now intro Fuxy; apply (fidiv_spec_fl x y); apply next_up_finite_spec_f1.
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
