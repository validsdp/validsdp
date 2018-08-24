Require Import float_spec binary64 float_infnan_spec binary64_infnan.
Require Import ZArith Bool.

Require Import Flocq.Core.Raux.
Require Import Flocq.IEEE754.Bits.

Require Import Float.
Require Import FlocqNativeLayer.

Section Primitive_float_infnan.

  Definition nan_pl : { pl: bool * positive | Binary.nan_pl prec (snd pl) = true } :=
    exist _ (false, 1%positive) (eq_refl true).

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

  Lemma ficompare_spec x y : finite x -> finite y -> (x ?= y)%float = Some (Rcompare (FI2FS x) (FI2FS y)).
    intros Hx Hy.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !B2Prim_Prim2B.
    apply binary64_infnan.ficompare_spec; rewrite <- finite_equiv;
      now rewrite B2Prim_Prim2B.
  Qed.

  Lemma ficompare_spec_eq x y : (x ?= y)%float = Some Eq -> FI2FS x = FI2FS y :> R.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !B2Prim_Prim2B.
    apply binary64_infnan.ficompare_spec_eq.
  Qed.

  Lemma ficompare_spec_eq_f x y : (x ?= y)%float = Some Eq -> finite x <-> finite y.
    rewrite <- (B2Prim_Prim2B nan_pl x).
    rewrite <- (B2Prim_Prim2B nan_pl y).
    rewrite FPcompare_Bcompare.
    unfold FI2FS.
    rewrite !finite_equiv.
    apply binary64_infnan.ficompare_spec_eq_f.
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

Require Import Psatz.

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

  Require Import Flocq.Core.Generic_fmt.
  Require Import Flocq.Core.FLX.
  Require Import Flocq.Core.FLT.
  Require Import Flocq.Core.Ulp.
  Require Import Flocq.Core.Round_NE.

  Lemma error_le_ulp_round :
    forall (beta : radix) (fexp : Z -> Z),
    Valid_exp fexp ->
    Monotone_exp fexp ->
    forall rnd : R -> Z, Valid_rnd rnd ->
    forall x : R,
    Rabs (round beta fexp rnd x - x) <= ulp beta fexp (round beta fexp rnd x).
  Proof.
    intros beta fexp Vexp Mexp rnd Vrnd x.
    destruct (Req_dec x 0) as [Zx|Nzx].
    { rewrite Zx, round_0; [|exact Vrnd].
      unfold Rminus; rewrite Ropp_0, Rplus_0_l, Rabs_R0; apply ulp_ge_0. }
    now apply Rlt_le, error_lt_ulp_round.
  Qed.

  (** Adding [ulp] is a, somewhat reasonable, overapproximation of [succ]. *)
  Lemma succ_le_plus_ulp beta fexp (Mexp : Monotone_exp fexp) x :
    succ beta fexp x <= x + ulp beta fexp x.
  Proof.
    destruct (Rle_or_lt 0 x) as [Px|Nx]; [now right; apply succ_eq_pos|].
    replace (_ + _) with (- (-x - ulp beta fexp x)) by ring.
    unfold succ; rewrite (Rle_bool_false _ _ Nx), <-ulp_opp.
    apply Ropp_le_contravar; unfold pred_pos.
    destruct (Req_dec (-x) (bpow beta (mag beta (-x) - 1))) as [Hx|Hx].
    { rewrite (Req_bool_true _ _ Hx).
      apply (Rplus_le_reg_r x); ring_simplify; apply Ropp_le_contravar.
      unfold ulp; rewrite Req_bool_false; [|lra].
      apply bpow_le, Mexp; lia. }
    now rewrite (Req_bool_false _ _ Hx); right.
  Qed.

  (** And it also lies in the format. *)
  Lemma generic_format_plus_ulp beta fexp (Vexp : Valid_exp fexp)
        (Mexp : Monotone_exp fexp) x :
    generic_format beta fexp x ->
    generic_format beta fexp (x + ulp beta fexp x).
  Proof.
    intro Fx.
    destruct (Rle_or_lt 0 x) as [Px|Nx].
    { now rewrite <-(succ_eq_pos _ _ _ Px); apply generic_format_succ. }
    apply generic_format_opp in Fx.
    replace (_ + _) with (- (-x - ulp beta fexp x)) by ring.
    apply generic_format_opp; rewrite <-ulp_opp.
    destruct (Req_dec (-x) (bpow beta (mag beta (-x) - 1))) as [Hx|Hx].
    { unfold ulp; rewrite Req_bool_false; [|lra].
      rewrite Hx at 1.
      unfold cexp.
      set (e := mag _ _).
      assert (Hfe : (fexp e < e)%Z).
      { now apply mag_generic_gt; [|lra|]. }
      replace (e - 1)%Z with (e - 1 - fexp e + fexp e)%Z by ring.
      rewrite bpow_plus.
      set (m := bpow _ (_ - _)).
      replace (_ - _) with ((m - 1) * bpow beta (fexp e)); [|unfold m; ring].
      case_eq (e - 1 - fexp e)%Z.
      { intro He; unfold m; rewrite He; simpl; ring_simplify (1 - 1).
        rewrite Rmult_0_l; apply generic_format_0. }
      { intros p Hp; unfold m; rewrite Hp; simpl.
        pose (f := {| Defs.Fnum := (Z.pow_pos beta p - 1)%Z;
                      Defs.Fexp := fexp e |} : Defs.float beta).
        apply (generic_format_F2R' _ _ _ f); [|intro Hm'; unfold f; simpl].
        { now unfold Defs.F2R; simpl; rewrite minus_IZR. }
        unfold cexp.
        replace (IZR _) with (bpow beta (Z.pos p)); [|now simpl].
        rewrite <-Hp.
        assert (He : (1 <= e - 1 - fexp e)%Z); [lia|].
        set (e' := mag _ (_ * _)).
        assert (H : (e' = e - 1 :> Z)%Z); [|rewrite H; apply Mexp; lia].
        unfold e'; apply mag_unique.
        rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|apply bpow_ge_0].
        rewrite Rabs_pos_eq;
          [|apply (Rplus_le_reg_r 1); ring_simplify;
            change 1 with (bpow beta 0); apply bpow_le; lia].
        assert (beta_pos : 0 < IZR beta).
        { apply (Rlt_le_trans _ 2); [lra|].
          apply IZR_le, Z.leb_le, radix_prop. }
        split.
        { replace (e - 1 - 1)%Z with (e - 1 - fexp e + -1  + fexp e)%Z by ring.
          rewrite bpow_plus.
          apply Rmult_le_compat_r; [apply bpow_ge_0|].
          rewrite bpow_plus; simpl; unfold Z.pow_pos; simpl.
          rewrite Zmult_1_r.
          apply (Rmult_le_reg_r _ _ _ beta_pos).
          rewrite Rmult_assoc, Rinv_l; [|lra]; rewrite Rmult_1_r.
          apply (Rplus_le_reg_r (IZR beta)); ring_simplify.
          apply (Rle_trans _ (2 * bpow beta (e - 1 - fexp e))).
          { change 2 with (1 + 1); rewrite Rmult_plus_distr_r, Rmult_1_l.
            apply Rplus_le_compat_l.
            rewrite <-bpow_1; apply bpow_le; lia. }
          rewrite Rmult_comm; apply Rmult_le_compat_l; [apply bpow_ge_0|].
          apply IZR_le, Z.leb_le, radix_prop. }
        apply (Rmult_lt_reg_r (bpow beta (- fexp e))); [apply bpow_gt_0|].
        rewrite Rmult_assoc, <-!bpow_plus.
        replace (fexp e + - fexp e)%Z with 0%Z by ring; simpl.
        rewrite Rmult_1_r; unfold Zminus; lra. }
      intros p Hp; exfalso; lia. }
    replace (_ - _) with (pred_pos beta fexp (-x)).
    { now apply generic_format_pred_pos; [| |lra]. }
    now unfold pred_pos; rewrite Req_bool_false.
  Qed.

  Lemma succ_round_ge_id beta fexp (Vexp : Valid_exp fexp)
        rnd (Vrnd : Valid_rnd rnd) x :
    x <= succ beta fexp (round beta fexp rnd x).
  Proof.
    apply (Rle_trans _ (round beta fexp Raux.Zceil x)).
    { now apply round_UP_pt. }
    destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
    { now apply UP_le_succ_DN. }
    apply succ_ge_id.
  Qed.

  Lemma plus_ulp_rnd_ge x :
    let rx := round radix2 (FLT_exp emin prec) ZnearestE x in
    x <= round radix2 (FLT_exp emin prec) ZnearestE
               (rx + ulp radix2 (FLT_exp emin prec) rx).
  Proof.
    simpl.
    set (rx := round _ _ _ x).
    assert (Vexp : Valid_exp (FLT_exp emin prec)); [now apply FLT_exp_valid|].
    assert (Vrnd : Valid_rnd ZnearestE); [now apply valid_rnd_N|].
    apply (Rle_trans _ (succ radix2 (FLT_exp emin prec) rx)).
    { now apply succ_round_ge_id. }
    rewrite round_generic; [|now simpl|].
    { apply succ_le_plus_ulp, FLT_exp_monotone. }
    now apply generic_format_plus_ulp;
      [|apply FLT_exp_monotone|apply generic_format_round].
  Qed.
  
  (* TODO: Place that in FloatValue *)
  Definition ulp x := ldexp one (fexp prec emax (snd (frexp x))).
  Definition up x := (x + ulp x)%float.
  
  Definition fiplus_up x y := up (x + y)%float.

  Lemma fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x.
  Proof.
    intro Fuxy; apply (fiplus_spec_fl x y); revert Fuxy; apply fiplus_spec_fl.
  Qed.

  Lemma fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y.
  Proof.
    intro Fuxy; apply (fiplus_spec_fr x y); revert Fuxy; apply fiplus_spec_fl.
  Qed.

  Print EFfrexp.
  
  Lemma EFfrexp_spec x :
    (FI2FS x <> 0%R :> R) ->
    snd (EFfrexp prec emax (Prim2EF x)) = mag radix2 (FI2FS x).
  Proof.
    intro Nzx.
    generalize (FI2FS_spec _ Nzx).
    unfold finite.
    rewrite <-(B2Prim_Prim2B nan_pl x) at 1.
    rewrite is_finite_spec.
    unfold Prim2B.
    rewrite Binary.is_finite_FF2B.
    revert Nzx.
    unfold FI2FS, Prim2B, binary64_infnan.FI2FS; simpl.
    rewrite Binary.B2R_FF2B.
    case (Prim2EF x).
    { intro s; simpl; lra. }
    { intro s; simpl; discriminate. }
    { simpl; discriminate. }
    intros s m e Nzm' _.
    assert (Nzm : (Zaux.cond_Zopp s (Z.pos m) <> 0)%Z).
    { intro H; apply Nzm'.
      unfold Binary.FF2R, Defs.F2R; simpl.
      now rewrite H, Rmult_0_l. }
    unfold EFfrexp.
    case Pos.eqb_spec.
    { simpl; intro M53.
      rewrite Float_prop.mag_F2R_Zdigits; [|exact Nzm].
      rewrite Zplus_comm; f_equal.
      unfold prec; rewrite <-M53, Digits.Zpos_digits2_pos.
      now case s. }
    simpl;intro Nm53.
    rewrite Float_prop.mag_F2R_Zdigits; [|exact Nzm].
    rewrite Z.pos_sub_spec.
    case Pos.compare_spec.
    { now intro H; exfalso; apply Nm53. }
    { intro H.
      change (Z.neg _) with (Z.opp (Z.pos (digits2_pos m - 53))).
      rewrite (Pos2Z.inj_sub _ _ H); unfold prec; ring_simplify.
      rewrite Digits.Zpos_digits2_pos.
      now case s. }
    intro H; rewrite (Pos2Z.inj_sub _ _ H); unfold prec; ring_simplify.
    rewrite Digits.Zpos_digits2_pos.
    now case s.
  Qed.

  Lemma all_conversions x :
    Binary.is_nan_FF x = false ->
    valid_binary (FlocqEmulatedLayer.FF2EF x) = true ->
    Binary.B2R 53 1024 (Prim2B nan_pl (EF2Prim (FlocqEmulatedLayer.FF2EF x))) = Binary.FF2R radix2 x.
  Proof.
    intros Nnan Vx.
    unfold Prim2B; rewrite Binary.B2R_FF2B.
    rewrite (Prim2EF_EF2Prim _ Vx).
    now rewrite EF2FF_FF2EF_notnan.
  Qed.

  Lemma negligible_exp_FLT emin prec (Hprec : Prec_gt_0 prec) :
    exists n, negligible_exp (FLT_exp emin prec) = Some n /\ (n <= emin)%Z.
  Proof.
    case (negligible_exp_spec (FLT_exp emin prec)).
    { intro H; exfalso; specialize (H emin); revert H.
      apply Zle_not_lt, Z.le_max_r. }
    intros n Hn; exists n; split; [now simpl|].
    destruct (Z.max_spec (n - prec) emin) as [(Hm, Hm')|(Hm, Hm')].
    { now revert Hn; unfold FLT_exp; rewrite Hm'. }
    revert Hn Hprec; unfold FLT_exp, Prec_gt_0; rewrite Hm'; omega.
  Qed.

  Lemma bounded_generic_format m e :
    bounded prec emax m e = true ->
    generic_format radix2 (FLT_exp (-1074) prec)
                   (Defs.F2R ({| Defs.Fnum := Z.pos m; Defs.Fexp := e |} :
                                Defs.float radix2)).
  Proof.
    intro Bme; apply andb_prop in Bme; destruct Bme as (Bm, Be).
    apply Zeq_bool_eq in Bm.
    apply generic_format_F2R; intros _.
    unfold cexp; replace (mag _ _ : Z) with (Z.pos (digits2_pos m) + e)%Z.
    { apply Z.eq_le_incl, Bm. }
    rewrite Digits.Zpos_digits2_pos.
    now symmetry; apply Float_prop.mag_F2R_Zdigits.
  Qed.

  Lemma of_int63_bounded m e :
    bounded prec emax m e = true ->
    exists e,
      (0 <= e)%Z /\
      Prim2EF (of_int63 (Int63Op.of_pos m))
      = E754_finite false (m * (match e with Z.pos p => 2 ^ p | _ => 1 end)) (Z.opp e).
  Proof.
    intro Bme; apply andb_prop in Bme; destruct Bme as (Bm, Be).
    assert (Bm' := Bm).
    apply Zeq_bool_eq in Bm.
    rewrite Z.leb_le in Be.
    rewrite Digits.Zpos_digits2_pos in Bm.
    rewrite <-Float_prop.mag_F2R_Zdigits in Bm; [|now simpl].
    assert (Pprec : Prec_gt_0 prec) by now simpl.
    assert (Hmax : (prec < emax)%Z) by now simpl.
    assert (Hm'' : (mag radix2 (IZR (Z.pos m)) <= prec)%Z).
    { apply (Zplus_le_reg_r _ _ e).
      rewrite <-mag_mult_bpow; [|now apply IZR_neq].
      unfold Defs.F2R, fexp in Bm; simpl in Bm.
      fold prec; lia. }
    assert (Hm' : (Z.pos m < 2 ^ 53)%Z).
    { apply lt_IZR.
      rewrite <-(Rabs_pos_eq (IZR (Z.pos _))); [|now apply IZR_le].
      apply (Rlt_le_trans _ _ _ (bpow_mag_gt radix2 _)).
      change (IZR (2 ^ 53)) with (bpow radix2 53).
      now apply bpow_le. }
    assert (Hm : Int63Op.to_Z (Int63Op.of_pos m) = Z.pos m).
    { rewrite Int63Properties.of_pos_spec.
      rewrite Zmod_small; [now simpl|]; split; [apply Zle_0_pos|].
      apply (Zlt_le_trans _ _ _ Hm').
      unfold Int63Axioms.wB.
      change 2%Z with (radix2 : Z); apply Zpower_le.
      now compute; discriminate. }
    rewrite of_int63_spec, Hm.
    rewrite (FlocqEmulatedLayer.binary_normalize_equiv _ _ Pprec Hmax).
    generalize (Binary.binary_normalize_correct
                  _ _ Pprec Hmax Binary.mode_NE
                  (Z.pos m) 0 false).
    set (F2R_m_0 := Defs.F2R _).
    assert (F_F2R_m_0 : generic_format radix2 (FLT_exp emin prec) F2R_m_0).
    { apply generic_format_F2R; intros _.
      unfold cexp, FLT_exp, Defs.F2R; simpl; rewrite Rmult_1_r.
      apply Z.max_lub; [|unfold emin, emax, prec]; lia. }
    rewrite round_generic; [|apply valid_rnd_N|apply F_F2R_m_0].
    replace (Rabs _) with (IZR (Z.pos m));
      [|now unfold F2R_m_0, Defs.F2R; simpl; rewrite Rmult_1_r, Rabs_pos_eq;
        [|apply IZR_le, Zle_0_pos]].
    rewrite Rlt_bool_true;
      [|apply IZR_lt; rewrite Z.pow_pos_fold; apply (Zlt_le_trans _ _ _ Hm');
        change 2%Z with (radix2 : Z); apply Zpower_le; lia].
    set (bn_m_0 := Binary.binary_normalize _ _ _ _ _ _ _ _).
    intros (Hr, (F_bn_m_0, Hs)).
    assert (V_bn_m_0 := valid_binary_B2EF bn_m_0).
    revert Hs Hr F_bn_m_0 V_bn_m_0.
    case bn_m_0.
    { intros s _; simpl.
      unfold F2R_m_0, Defs.F2R; simpl; rewrite Rmult_1_r.
      intro H0; apply eq_IZR in H0; discriminate H0. }
    { intros s _; simpl; discriminate. }
    { intros s pl Hpl _; simpl; discriminate. }
    intros s m' e' Hm'e'; simpl.
    rewrite Rcompare_Gt;
      [|unfold F2R_m_0, Defs.F2R; simpl; rewrite Rmult_1_r; apply IZR_lt; lia].
    intro Hs; rewrite Hs; simpl.
    intros Hr _ Bm'e'.
    apply andb_prop in Bm'e'; destruct Bm'e' as (Bm'', _).
    generalize (Binary.canonical_canonical_mantissa _ _ false _ _ Bm'').
    unfold canonical; simpl; rewrite Hr.
    unfold cexp, FLT_exp, F2R_m_0, Defs.F2R; simpl; rewrite Rmult_1_r.
    unfold FlocqEmulatedLayer.B2EF; simpl.
    revert Hr; unfold F2R_m_0, Defs.F2R; simpl; rewrite Rmult_1_r.
    case e'.
    { rewrite Rmult_1_r.
      intro Hm'''; apply eq_IZR in Hm'''.
      inversion Hm''' as (Hm'''').
      now intros _; exists Z0; split; [|f_equal; lia]. }
    { intros p _.
      destruct (Z.max_spec (mag radix2 (IZR (Z.pos m)) - prec) (-1074)) as [(H, H')|(H, H')].
      { rewrite H'; discriminate. }
      intro H''.
      assert (Z.pos p <= 0)%Z; [rewrite H'', H'; lia|exfalso; lia]. }
    intros p; simpl; intros Hm''' _.
    exists (Z.pos p); split; [lia|]; f_equal.
    assert (H : Z.pos m' = Z.pos (m * 2 ^ p)); [|now inversion H].
    apply eq_IZR, (Rmult_eq_reg_r (/ IZR (Z.pow_pos 2 p)));
      [|rewrite Z.pow_pos_fold;
        apply Rinv_neq_0_compat, IZR_neq, Z.pow_nonzero; lia].
    rewrite Hm''', Pos2Z.inj_mul, Pos2Z.inj_pow, mult_IZR, Z.pow_pos_fold.
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r; [now simpl|].
    apply IZR_neq, Z.pow_nonzero; lia.
  Qed.
    
  Lemma EFopp_binary_round s m e :
    EFopp (FlocqEmulatedLayer.FF2EF (Binary.binary_round prec emax Binary.mode_NE s m e))
    = FlocqEmulatedLayer.FF2EF (Binary.binary_round prec emax Binary.mode_NE (negb s) m e).
  Proof.
    unfold Binary.binary_round.
    case (Binary.shl_align_fexp _ _ _ _); intros m' e'.
    unfold Binary.binary_round_aux.
    case (Binary.shr_fexp _ _ _ _ _).
    intros mrs' e''; simpl.
    case (Binary.shr_fexp _ _ _ _ _).
    intros mrs'' e'''.
    case (Binary.shr_m mrs''); simpl; [reflexivity| |reflexivity].
    now intro mrs'''; case (_ <=? _)%Z.
  Qed.    
    
  Lemma finite_bounded x :
    finite x ->
    Rabs (FI2FS x) < bpow radix2 emax.
  Proof.
    rewrite <-(EF2Prim_Prim2EF x); generalize (Prim2EF_valid x).
    case (Prim2EF x).
    { intros s _ _; simpl; unfold Prim2B; rewrite Binary.B2R_FF2B.
      case s; simpl.
      { change (Prim2EF neg_zero) with (E754_zero true); simpl.
        now rewrite Rabs_R0; apply IZR_lt. }
      change (Prim2EF zero) with (E754_zero false); simpl.
      now rewrite Rabs_R0; apply IZR_lt. }
    { intros s _; simpl; case s; unfold finite, is_finite, is_infinity; simpl.
      { replace (_ ?= _)%float with (Some Lt) by now compute.
        replace (_ ?= _)%float with (Some Eq) by now compute.
        now rewrite orb_true_r. }
      replace (_ ?= _)%float with (Some Eq) by now compute.
      now rewrite orb_true_r. }
    { intros _; simpl; unfold finite, is_finite, is_nan.
      now replace (_ ?= _)%float with (None : option comparison);
        [|now compute]. }
    intros s m e; simpl; intros Bme _.
    assert (Bme' := Binary.bounded_lt_emax _ _ _ _ Bme).
    unfold Prim2B; rewrite Binary.B2R_FF2B.
    assert (Pprec : Prec_gt_0 prec) by now simpl.
    assert (Hmax : (prec < emax)%Z) by now simpl.
    destruct (of_int63_bounded _ _ Bme) as (e', (Ne', He')).
    pose (m' := (m * match e' with Z.pos p => 2 ^ p | _ => 1 end)%positive).
    assert (Eme' : Defs.F2R ({| Defs.Fnum := Z.pos m'; Defs.Fexp := -e' + e |} : Defs.float radix2)
                   = Defs.F2R ({| Defs.Fnum := Z.pos m; Defs.Fexp := e |} : Defs.float radix2)).
    { unfold Defs.F2R, m'; simpl.
      rewrite bpow_plus, <-Rmult_assoc; f_equal.
      rewrite Pos2Z.inj_mul, mult_IZR, Rmult_assoc.
      rewrite <-(Rmult_1_r (IZR _)) at 2; f_equal.
      revert Ne'; case e'.
      { now simpl; rewrite Rmult_1_l. }
      { intros p _.
        rewrite Pos2Z.inj_pow_pos.
        change (IZR (Z.pow_pos _ _)) with (bpow radix2 (Z.pos p)).
        now rewrite <-bpow_plus, Z.add_opp_diag_r. }
      intros p H; exfalso; lia. }
    assert (Bme'' : Defs.F2R ({| Defs.Fnum := Z.pos m'; Defs.Fexp := -e' + e |} : Defs.float radix2) < bpow radix2 emax).
    { now revert Bme'; apply Rle_lt_trans; right. }
    assert (Hlt : Rabs (round radix2 (FLT_exp (-1074) prec) ZnearestE
                              (Defs.F2R ({| Defs.Fnum := Zaux.cond_Zopp s (Z.pos m');
                                            Defs.Fexp := -e' + e |} : Defs.float radix2))) <
                  IZR (Z.pow_pos 2 1024)).
    { case s; simpl.
      { replace (Defs.F2R _)
          with (- Defs.F2R ({| Defs.Fnum := Z.pos m';
                               Defs.Fexp := -e' + e |} :
                              Defs.float radix2));
          [|now unfold Defs.F2R; simpl; rewrite Ropp_mult_distr_l].
        rewrite round_NE_opp, Rabs_Ropp.
        rewrite round_generic; [|apply valid_rnd_N|].
        { rewrite Rabs_pos_eq; [now apply Bme''|].
          now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
        now rewrite Eme'; apply bounded_generic_format. }
      rewrite round_generic; [|apply valid_rnd_N|].
      { rewrite Rabs_pos_eq; [now apply Bme''|].
        now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
      now rewrite Eme'; apply bounded_generic_format. }
    generalize (Binary.binary_round_correct _ _ Pprec Hmax Binary.mode_NE s m' (-e' + e)).
    simpl.
    rewrite (Rlt_bool_true _ _ Hlt).
    intros (H, (H', (H'', H'''))); revert H H' H'' H''' Hlt.
    case s.
    { rewrite FPopp_EFopp, ldexp_spec, He'; fold m'; simpl.
      rewrite FlocqEmulatedLayer.binary_round_equiv.
      rewrite EFopp_binary_round; simpl.
      case (Binary.binary_round _ _ _ _ _ _).
      { now intros s' _ _ _ _ _; simpl; rewrite Rabs_R0; apply IZR_lt. }
      { now intros s' _. }
      { now intros s' pl Hpl _. }
      intros s' m'' e''; simpl; intros _ H _ _ Hlt.
      rewrite H; apply Hlt. }
    rewrite ldexp_spec, He'; fold m'; simpl.
    rewrite FlocqEmulatedLayer.binary_round_equiv.
    case (Binary.binary_round _ _ _ _ _ _).
    { now intros s' _ _ _ _ _; simpl; rewrite Rabs_R0; apply IZR_lt. }
    { now intros s' _. }
    { now intros s' pl Hpl _. }
    intros s' m'' e''; simpl; intros _ H _ _ Hlt.
    rewrite H; apply Hlt.
  Qed.
    
  Lemma ulp_spec x :
    finite x ->
    FI2FS (ulp x) = Ulp.ulp radix2 (fexp prec emax) (FI2FS x) :> R.
  Proof.
    intros Fx.
    unfold ulp.
    rewrite <-(EF2Prim_Prim2EF (ldexp _ _)).
    rewrite ldexp_spec.
    replace (Prim2EF one) with (E754_finite false 4503599627370496 (-52));
      [|now compute].
    unfold EFldexp, fexp.
    rewrite FlocqEmulatedLayer.binary_round_equiv.
    unfold Ulp.ulp, Generic_fmt.cexp.
    destruct (Req_dec (FI2FS x) 0) as [Zx|Nzx].
    { rewrite (Req_bool_true _ _ Zx).
      destruct (negligible_exp_FLT emin prec) as (n, (Hn, Hn')); [now simpl|].
      change (fun _ => Z.max _ _) with (FLT_exp emin prec); rewrite Hn.
      rewrite (Z.max_r (n - prec));
        [|unfold prec, EmulatedFloat.emin; unfold emin, prec in Hn'; lia].
      clear n Hn Hn'.
      rewrite Z.max_r.
      { change (Binary.binary_round _ _ _ _ _ _)
          with (Binary.F754_finite false 1 (-1074)); simpl.
        unfold Prim2B; rewrite Binary.B2R_FF2B; simpl.
        change (Prim2EF (ldexp (of_int63 (Int63Op.of_pos 1)) (-1074)))
          with (E754_finite false 1 (-1074)); simpl.
        now unfold Defs.F2R; simpl; rewrite Rmult_1_l. }
      generalize (frexp_spec x); case (frexp x); intros m e; simpl.
      revert Fx Zx; unfold finite, FI2FS, Prim2B; simpl.
      rewrite <-(B2Prim_Prim2B nan_pl x) at 1.
      rewrite is_finite_spec, Binary.B2R_FF2B; simpl.
      unfold Prim2B; rewrite Binary.is_finite_FF2B.
      case (Prim2EF x).
      { intros s _ _; unfold EFfrexp; intro H.
        now change e with (snd (Prim2EF m, e)); rewrite H. }
      { now simpl. }
      { now simpl. }
      intros s m' e' _; simpl; unfold Defs.F2R; simpl; intro H; exfalso.
      destruct (Rmult_integral _ _ H) as [H'|H'].
      { now apply eq_IZR in H'; revert H'; case s. }
      revert H'; apply Rgt_not_eq, Rlt_gt, bpow_gt_0. }
    rewrite (Req_bool_false _ _ Nzx).
    assert (Hfrexp := frexp_spec x).    
    case (frexp x) as (m, e) in Hfrexp |- *.
    change (snd (m, e)) with (snd (Prim2EF m, e)); rewrite Hfrexp.
    rewrite (EFfrexp_spec _ Nzx).
    set (e' := Z.max _ _).
    assert (H := Binary.binary_round_correct
                   prec emax (eq_refl _) (eq_refl _)
                   Binary.mode_NE false 4503599627370496 (-52 + e')).
    destruct H as (H, H').
    unfold Defs.F2R in H'.
    rewrite Rlt_bool_true in H'.
    { destruct H' as (H', (H'', H''')).
      set (e'' := (-52 + e')%Z).
      unfold FI2FS, binary64_infnan.FI2FS; simpl.
      rewrite all_conversions.
      + unfold e''; rewrite H'; fold e''.
        simpl.
        replace 4503599627370496%R with (bpow radix2 52); [|now compute].
        rewrite <-bpow_plus.
        replace (52 + e'')%Z with e'; [|now unfold e''; ring].
        apply Generic_fmt.round_generic.
        * now apply Generic_fmt.valid_rnd_N.
        * now apply FLT.FLT_format_bpow; [|apply Z.le_max_r].
      + now revert H''; fold e''; case (Binary.binary_round _ _ _ _ _ _).
      + now revert H; fold e''; case (Binary.binary_round _ _ _ _ _ _). }
    set (e'' := (-52 + e')%Z).
    simpl.
    replace 4503599627370496%R with (bpow radix2 52); [|now compute].
    rewrite <-bpow_plus.
    rewrite Generic_fmt.round_generic.
    + rewrite Rabs_pos_eq; [|apply bpow_ge_0].
      change (IZR _) with (bpow radix2 1024); apply bpow_lt.
      unfold e''; ring_simplify; unfold e'.
      apply Z.max_lub_lt; [|now simpl].
      apply (Zplus_lt_reg_r _ _ prec); unfold prec; ring_simplify.
      apply (Zle_lt_trans _ 1024); [|now simpl].
      apply (mag_le_bpow _ _ _ Nzx).
      now apply finite_bounded.
    + now apply Generic_fmt.valid_rnd_N.
    + apply FLT.FLT_format_bpow; [now simpl|].
      unfold e''; ring_simplify; apply Z.le_max_r.
  Qed.

  Lemma fiplus_up_spec x y : finite (fiplus_up x y) -> FI2FS x + FI2FS y <= FI2FS (fiplus_up x y).
    intro Fuxy.
    assert (Fxy := fiplus_spec_fl _ _ Fuxy).
    unfold fiplus_up, up.
    rewrite (fiplus_spec _ _ Fuxy); unfold fplus, frnd; simpl.
    change (Binary.B2R _ _ (_ _ (x + y)%float) : R) with (FI2FS (x + y) : R).
    change (Binary.B2R _ _ (_ _ (ulp _)) : R) with (FI2FS (ulp (x + y)) : R).
    rewrite (ulp_spec _ Fxy).
    rewrite (fiplus_spec _ _ Fxy); unfold fplus, frnd; simpl.
    change (Binary.B2R _ _ (_ _ x) : R) with (FI2FS x : R).
    change (Binary.B2R _ _ (_ _ y) : R) with (FI2FS y : R).
    apply plus_ulp_rnd_ge.
  Qed.

  Lemma is_nan_EF2Prim x :
    valid_binary x = true ->
    is_nan (EF2Prim x)
    = match x with
      | E754_zero _ => false
      | E754_infinity _ => false
      | E754_nan => true
      | E754_finite _ _ _ => false
      end.
  Proof.
    intro Vx.
    unfold is_nan; rewrite FPcompare_EFcompare; unfold EFcompare.
    now rewrite (Prim2EF_EF2Prim _ Vx); case x.
  Qed.      
      
  Lemma is_infinity_EF2Prim x :
    valid_binary x = true ->
    is_infinity (EF2Prim x)
    = match x with
      | E754_zero _ => false
      | E754_infinity _ => true
      | E754_nan => false
      | E754_finite _ _ _ => false
      end.
  Proof.
    intro Vx.
    unfold is_infinity; rewrite !FPcompare_EFcompare; unfold EFcompare.
    rewrite (Prim2EF_EF2Prim _ Vx).
    case x.
    + now intro b; case b.
    + now intro b; case b.
    + now simpl.
    + now intros b p e; case b;
        (replace (Prim2EF infinity) with (E754_infinity false); [|now cbv]);
        (replace (Prim2EF neg_infinity) with (E754_infinity true); [|now cbv]).
  Qed.
      
  Lemma is_finite_EF2Prim x :
    valid_binary x = true ->
    is_finite (EF2Prim x)
    = match x with
      | E754_zero _ => true
      | E754_infinity _ => false
      | E754_nan => false
      | E754_finite _ _ _ => true
      end.
  Proof.
    intro Vx.
    unfold is_finite.
    rewrite (is_nan_EF2Prim _ Vx), (is_infinity_EF2Prim _ Vx).
    now case x.
  Qed.
    
  Definition fimult_up x y := up (x * y)%float.

  Lemma fimult_up_spec x y : finite (fimult_up x y) -> FI2FS x * FI2FS y <= FI2FS (fimult_up x y).
    intro Fuxy.
    assert (Fxy := fiplus_spec_fl _ _ Fuxy).
    unfold fimult_up, up.
    rewrite (fiplus_spec _ _ Fuxy); unfold fplus, frnd; simpl.
    change (Binary.B2R _ _ (_ _ (x * y)%float) : R) with (FI2FS (x * y) : R).
    change (Binary.B2R _ _ (_ _ (ulp _)) : R) with (FI2FS (ulp (x * y)) : R).
    rewrite (ulp_spec _ Fxy).
    rewrite (fimult_spec _ _ Fxy); unfold fmult, frnd; simpl.
    change (Binary.B2R _ _ (_ _ x) : R) with (FI2FS x : R).
    change (Binary.B2R _ _ (_ _ y) : R) with (FI2FS y : R).
    apply plus_ulp_rnd_ge.
  Qed.

  Lemma fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x.
  Proof.
    intro Fuxy; apply (fimult_spec_fl x y); revert Fuxy; apply fiplus_spec_fl.
  Qed.

  Lemma fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y.
  Proof.
    intro Fuxy; apply (fimult_spec_fr x y); revert Fuxy; apply fiplus_spec_fl.
  Qed.

  Definition fidiv_up x y := up (x / y)%float.

  Lemma fidiv_up_spec x y : finite (fidiv_up x y) -> finite y -> FI2FS x / FI2FS y <= FI2FS (fidiv_up x y).
    intros Fuxy Fy.
    assert (Fxy := fiplus_spec_fl _ _ Fuxy).
    unfold fidiv_up, up.
    rewrite (fiplus_spec _ _ Fuxy); unfold fplus, frnd; simpl.
    change (Binary.B2R _ _ (_ _ (x / y)%float) : R) with (FI2FS (x / y) : R).
    change (Binary.B2R _ _ (_ _ (ulp _)) : R) with (FI2FS (ulp (x / y)) : R).
    rewrite (ulp_spec _ Fxy).
    rewrite (fidiv_spec _ _ Fxy Fy); unfold fdiv, frnd; simpl.
    change (Binary.B2R _ _ (_ _ x) : R) with (FI2FS x : R).
    change (Binary.B2R _ _ (_ _ y) : R) with (FI2FS y : R).
    apply plus_ulp_rnd_ge.
  Qed.

  Lemma fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x.
  Proof.
    intro Fuxy; apply (fidiv_spec_fl x y); revert Fuxy; apply fiplus_spec_fl.
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
