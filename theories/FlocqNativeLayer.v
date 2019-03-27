Require Import ZArith Flocq.IEEE754.Binary Flocq.Core.Zaux Float FlocqSpecLayer.

Lemma can_inj : forall {A} {B} {f : A -> B} {g : B -> A}, (forall x, g (f x) = x) -> (forall x y, f x = f y -> x = y).
  intros A B f g Hcan x y Heq. rewrite <- Hcan. symmetry. rewrite <- Hcan. rewrite Heq. reflexivity.
Qed.

(** Conversion to Flocq full_float *)

Definition SF2FF '(b, pl) x :=
  match x with
  | E754_finite s m e => F754_finite s m e
  | E754_infinity s => F754_infinity s
  | E754_zero s => F754_zero s
  | E754_nan => F754_nan b pl
  end.

Lemma FF2SF_SF2FF : forall nan x, FF2SF (SF2FF nan x) = x.
  intros. destruct x, nan; auto.
Qed.

Definition FFpayload x :=
  match x with
  | F754_nan b pl => (b, pl)
  | _ => (false, 1%positive)
  end.

Lemma SF2FF_FF2SF : forall x, SF2FF (FFpayload x) (FF2SF x) = x.
  intro. destruct x; auto.
Qed.

Lemma SF2FF_FF2SF_notnan : forall nan x, is_nan_FF x = false -> SF2FF nan (FF2SF x) = x.
  intros.
  destruct x, nan; auto.
  discriminate.
Qed.

Lemma SF2FF_inj : forall nan x y, SF2FF nan x = SF2FF nan y -> x = y.
  intro. exact (can_inj (FF2SF_SF2FF nan)).
Qed.

Lemma FF2SF_inj : forall x y, FF2SF x = FF2SF y -> FFpayload x = FFpayload y -> x = y.
  intros x y Heq Hpl.
  rewrite <- SF2FF_FF2SF. symmetry. rewrite <- SF2FF_FF2SF.
  rewrite Heq, Hpl. reflexivity.
Qed.

(** Conversions from/to Flocq binary_float *)

Program Definition Prim2B (nan : { pl : bool * positive | nan_pl prec (snd pl) = true }) x :=
  FF2B prec emax (SF2FF nan (Prim2SF x)) _.
Next Obligation.
  remember (Prim2SF x). destruct s; auto.
  rewrite <- valid_binary_equiv.
  rewrite FF2SF_SF2FF.
  rewrite Heqs.
  apply Prim2SF_valid.
  reflexivity.
Qed.

Definition B2Prim (x : binary_float prec emax) := (SF2Prim (B2SF x)).

Lemma B2Prim_Prim2B : forall nan x, B2Prim (Prim2B nan x) = x.
  intros. unfold Prim2B, B2Prim. unfold B2SF. rewrite B2FF_FF2B. rewrite FF2SF_SF2FF.
  apply SF2Prim_Prim2SF.
Qed.

Lemma FF2B_proof_irr (x y : Binary.full_float) (Heq : x = y) (Hx : Binary.valid_binary prec emax x = true) (Hy : Binary.valid_binary prec emax y = true) : FF2B prec emax x Hx = FF2B prec emax y Hy.
  unfold FF2B.
  revert Heq Hx Hy.
  case x, y; auto; try discriminate; try (intro H; inversion H; intros; reflexivity);
  intro H; inversion H; intros; rewrite (eqbool_irrelevance _ Hx Hy); reflexivity.
Qed.

Lemma valid_binary_B2SF : forall (x : binary_float prec emax), valid_binary (B2SF x) = true.
  intro. destruct x ; now simpl.
Qed.

Program Definition Bpayload (x : binary_float prec emax) : { pl : bool * positive | nan_pl prec (snd pl) = true } :=
  match x with
  | B754_nan b pl Hpl => exist _ (b, pl) _
  | _ => exist _ (false, 1%positive) _
  end.

Lemma Bpayload_FFpayload : forall x, proj1_sig (Bpayload x) = FFpayload (B2FF x).
  intro. destruct x; easy.
Qed.

Lemma Prim2B_B2Prim : forall x, Prim2B (Bpayload x) (B2Prim x) = x.
  intros. unfold Prim2B, B2Prim. unfold B2SF.
  assert (Hy : Binary.valid_binary prec emax (B2FF x) = true).
  {
    apply valid_binary_B2FF.
  }
  assert (Heq : SF2FF (proj1_sig (Bpayload x)) (Prim2SF (SF2Prim (B2SF x))) = B2FF x).
  {
    rewrite Prim2SF_SF2Prim. unfold B2SF. rewrite Bpayload_FFpayload. rewrite SF2FF_FF2SF. reflexivity.
    apply valid_binary_B2SF.
  }
  rewrite (FF2B_proof_irr _ _ Heq _ Hy).
  apply FF2B_B2FF.
Qed.

Lemma Prim2B_B2Prim_notnan : forall nan x, Binary.is_nan prec emax x = false -> Prim2B nan (B2Prim x) = x.
  intros.
  unfold Prim2B, B2Prim.
  unfold B2SF.
  assert (Hy : Binary.valid_binary prec emax (B2FF x) = true).
  {
    apply valid_binary_B2FF.
  }
  assert (Heq : SF2FF (proj1_sig nan) (Prim2SF (SF2Prim (B2SF x))) = B2FF x).
  {
    rewrite Prim2SF_SF2Prim.
    unfold B2SF.
    rewrite SF2FF_FF2SF_notnan.
    reflexivity.
    rewrite <- (FF2B_B2FF prec emax x Hy) in H.
    rewrite is_nan_FF2B in H.
    assumption.
    apply valid_binary_B2SF.
  }
  rewrite (FF2B_proof_irr _ _ Heq _ Hy).
  apply FF2B_B2FF.
Qed.

Lemma Prim2B_inj : forall nan x y, Prim2B nan x = Prim2B nan y -> x = y.
  intro. exact (can_inj (B2Prim_Prim2B nan)).
Qed.

Lemma B2Prim_inj : forall x y, B2Prim x = B2Prim y -> FFpayload (B2FF x) = FFpayload (B2FF y) -> x = y.
  unfold B2Prim. intros x y Heq Hpl. apply SF2Prim_inj in Heq; try apply valid_binary_B2SF.
  case x, y; try discriminate; unfold B2SF in Heq; simpl in Heq; inversion Heq; try reflexivity.
  * simpl in Hpl. inversion Hpl. revert e. rewrite H1. intro. now rewrite (eqbool_irrelevance _ _ e0).
  * revert e0 Hpl. rewrite H1, H2. intros e0 Hpl. now rewrite (eqbool_irrelevance _ _ e2).
Qed.

Lemma B2SF_Prim2B : forall pl x, B2SF (Prim2B pl x) = Prim2SF x.
  intros. unfold Prim2B. unfold B2SF. rewrite B2FF_FF2B. rewrite FF2SF_SF2FF. reflexivity.
Qed.

Lemma Prim2SF_B2Prim : forall x, Prim2SF (B2Prim x) = B2SF x.
Proof.
intro x; unfold B2Prim.
now rewrite Prim2SF_SF2Prim; [|apply valid_binary_B2SF].
Qed.

(** Basic properties of the Binary64 format *)

Lemma prec_gt_0 : FLX.Prec_gt_0 prec.
  unfold FLX.Prec_gt_0. now compute.
Qed.

Lemma Hmax : (prec < emax)%Z.
  now compute.
Qed.

(** Equivalence between prim_float and Flocq binary_float operations *)

Ltac prove_FP2B SFop_Bop FPop_SFop op_nan :=
  intros; unfold B2Prim; rewrite <- SFop_Bop; apply Prim2SF_inj; rewrite FPop_SFop;
  rewrite !Prim2SF_SF2Prim by (try (rewrite (SFop_Bop _ _ op_nan));
                               try (rewrite (SFop_Bop _ _ prec_gt_0 Hmax op_nan));
                               apply valid_binary_B2SF);
  reflexivity.

Theorem FPopp_Bopp : forall opp_nan x, (-(B2Prim x))%float = B2Prim (Bopp prec emax opp_nan x).
  prove_FP2B @SFopp_Bopp opp_SFopp opp_nan.
Qed.

Theorem FPabs_Babs : forall abs_nan x, abs (B2Prim x) = B2Prim (Babs prec emax abs_nan x).
  prove_FP2B @SFabs_Babs abs_SFabs abs_nan.
Qed.

Theorem FPcompare_Bcompare : forall x y,
  ((B2Prim x) ?= (B2Prim y))%float = flatten_cmp_opt (Bcompare prec emax x y).
  intros. rewrite compare_SFcompare. rewrite <- SFcompare_Bcompare. unfold B2Prim.
  rewrite !Prim2SF_SF2Prim by apply valid_binary_B2SF. reflexivity.
Qed.

Theorem FPmult_Bmult : forall mult_nan x y, ((B2Prim x)*(B2Prim y))%float = B2Prim (Bmult prec emax eq_refl eq_refl mult_nan mode_NE x y).
  prove_FP2B @SFmult_Bmult mult_SFmult mult_nan.
Qed.

Theorem FPplus_Bplus : forall plus_nan x y, ((B2Prim x)+(B2Prim y))%float = B2Prim (Bplus prec emax eq_refl eq_refl plus_nan mode_NE x y).
  prove_FP2B @SFplus_Bplus plus_SFplus plus_nan.
Qed.

Theorem FPminus_Bminus : forall minus_nan x y, ((B2Prim x)-(B2Prim y))%float = B2Prim (Bminus prec emax eq_refl eq_refl minus_nan mode_NE x y).
  prove_FP2B @SFminus_Bminus minus_SFminus minus_nan.
Qed.

Theorem FPdiv_Bdiv : forall div_nan x y, ((B2Prim x)/(B2Prim y))%float = B2Prim (Bdiv prec emax eq_refl eq_refl div_nan mode_NE x y).
  prove_FP2B @SFdiv_Bdiv div_SFdiv div_nan.
Qed.

Theorem FPsqrt_Bsqrt : forall sqrt_nan x, sqrt (B2Prim x) = B2Prim (Bsqrt prec emax eq_refl eq_refl sqrt_nan mode_NE x).
  prove_FP2B @SFsqrt_Bsqrt sqrt_SFsqrt sqrt_nan.
Qed.

Theorem FPnormfr_mantissa_Bnormfr_mantissa :
  forall x,
  normfr_mantissa (B2Prim x) = Int63.of_Z (Z.of_N (Bnormfr_mantissa prec emax x)).
Proof.
intro x; unfold B2Prim.
rewrite <-SFnormfr_mantissa_Bnormfr_mantissa.
rewrite <-(Prim2SF_SF2Prim (B2SF x)) at 2; [|apply valid_binary_B2SF].
rewrite <-normfr_mantissa_SFnormfr_mantissa.
now rewrite Int63.of_to_Z.
Qed.

Theorem FPldexp_Bldexp :
  forall x e,
  ldexp (B2Prim x) e = B2Prim (Bldexp prec emax prec_gt_0 Hmax mode_NE x e).
Proof.
intros x e; unfold B2Prim.
rewrite <-SFldexp_Bldexp.
rewrite <-(Prim2SF_SF2Prim (B2SF x)) at 2; [|apply valid_binary_B2SF].
rewrite <-ldexp_spec.
now rewrite SF2Prim_Prim2SF.
Qed.

Lemma Hemax : (3 <= emax)%Z.
Proof. now compute. Qed.

Theorem FPfrexp_Bfrexp :
  forall x,
  fst (frexp (B2Prim x)) = B2Prim (fst (Bfrexp prec emax prec_gt_0 Hemax x)) /\
  snd (frexp (B2Prim x)) = snd (Bfrexp prec emax prec_gt_0 Hemax x).
Proof.
intro x; unfold B2Prim.
rewrite <-(proj1 (SFfrexp_Bfrexp prec_gt_0 Hemax _)).
rewrite <-(proj2 (SFfrexp_Bfrexp prec_gt_0 Hemax _)).
rewrite <-(Prim2SF_SF2Prim (B2SF x)) at 2 4; [|apply valid_binary_B2SF].
generalize (frexp_spec (SF2Prim (B2SF x))).
case_eq (frexp (SF2Prim (B2SF x))); intros f z Hfz Hfrexp.
now rewrite <-Hfrexp; simpl; rewrite SF2Prim_Prim2SF.
Qed.

Theorem FPone_Bone : one = B2Prim (Bone prec emax prec_gt_0 Hmax).
Proof. now unfold B2Prim; rewrite <-SFone_Bone; compute. Qed.

Theorem FPulp_Bulp :
  forall x,
  ulp (B2Prim x) = B2Prim (Bulp prec emax prec_gt_0 Hmax Hemax x).
Proof.
intros x; unfold B2Prim, ulp.
rewrite <-SFulp_Bulp; unfold SFulp.
generalize (frexp_spec (SF2Prim (B2SF x))).
case_eq (frexp (SF2Prim (B2SF x))); intros f z Hfz.
rewrite Prim2SF_SF2Prim; [|apply valid_binary_B2SF].
intro Hfrexp; rewrite <-Hfrexp; unfold snd.
change (SFone prec emax) with (Prim2SF one).
now rewrite <-ldexp_spec, SF2Prim_Prim2SF.
Qed.

Theorem FPnext_up_Bsucc :
  forall succ_nan x,
  next_up (B2Prim x)
  = B2Prim (Bsucc prec emax prec_gt_0 Hmax Hemax succ_nan x).
Proof.
intros succ_nan x; unfold B2Prim.
rewrite <-SFsucc_Bsucc.
rewrite <-(Prim2SF_SF2Prim (B2SF x)) at 2; [|apply valid_binary_B2SF].
rewrite <-next_up_SFsucc.
now rewrite SF2Prim_Prim2SF.
Qed.

Theorem FPnext_down_Bpred :
  forall pred_nan x,
  next_down (B2Prim x)
  = B2Prim (Bpred prec emax prec_gt_0 Hmax Hemax pred_nan x).
Proof.
intros pred_nan x; unfold B2Prim.
rewrite <-SFpred_Bpred.
rewrite <-(Prim2SF_SF2Prim (B2SF x)) at 2; [|apply valid_binary_B2SF].
rewrite <-next_down_SFpred.
now rewrite SF2Prim_Prim2SF.
Qed.

Lemma is_nan_spec : forall x, is_nan (B2Prim x) = Binary.is_nan prec emax x.
  intro.
  now destruct x, s; auto; unfold is_nan; rewrite FPcompare_Bcompare; unfold Bcompare; destruct (e ?= e)%Z; simpl; rewrite ?Pcompare_refl.
Qed.

Lemma is_zero_spec : forall x, is_zero (B2Prim x) = match x with B754_zero _ => true | _ => false end.
  intro.
  unfold is_zero.
  replace zero with (B2Prim (B754_zero false)) by reflexivity.
  rewrite FPcompare_Bcompare.
  destruct x, s; auto.
Qed.

Lemma is_infinity_spec : forall x, is_infinity (B2Prim x) = match x with B754_infinity _ => true | _ => false end.
  intro.
  unfold is_infinity.
  replace infinity with (B2Prim (B754_infinity false)) by reflexivity.
  replace neg_infinity with (B2Prim (B754_infinity true)) by reflexivity.
  rewrite !FPcompare_Bcompare.
  destruct x, s; auto.
Qed.

Lemma get_sign_spec : forall x, Binary.is_nan prec emax x = false -> get_sign (B2Prim x) = Bsign prec emax x.
  intros.
  unfold get_sign, is_zero.
  replace zero with (B2Prim (B754_zero false)) by reflexivity.
  rewrite FPcompare_Bcompare.
  destruct x, s; auto; simpl; rewrite FPcompare_Bcompare; reflexivity.
Qed.

Lemma is_finite_spec : forall x, is_finite (B2Prim x) = Binary.is_finite prec emax x.
  intro.
  unfold is_finite.
  rewrite is_nan_spec.
  rewrite is_infinity_spec.
  destruct x; reflexivity.
Qed.
