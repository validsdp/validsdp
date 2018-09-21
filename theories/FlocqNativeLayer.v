Require Import ZArith Flocq.IEEE754.Binary Flocq.Core.Zaux Float FlocqEmulatedLayer.

Lemma can_inj : forall {A} {B} {f : A -> B} {g : B -> A}, (forall x, g (f x) = x) -> (forall x y, f x = f y -> x = y).
  intros A B f g Hcan x y Heq. rewrite <- Hcan. symmetry. rewrite <- Hcan. rewrite Heq. reflexivity.
Qed.

(** Conversion to Flocq full_float *)

Definition EF2FF '(b, pl) x :=
  match x with
  | E754_finite s m e => F754_finite s m e
  | E754_infinity s => F754_infinity s
  | E754_zero s => F754_zero s
  | E754_nan => F754_nan b pl
  end.

Lemma FF2EF_EF2FF : forall nan x, FF2EF (EF2FF nan x) = x.
  intros. destruct x, nan; auto.
Qed.

Definition FFpayload x :=
  match x with
  | F754_nan b pl => (b, pl)
  | _ => (false, 1%positive)
  end.

Lemma EF2FF_FF2EF : forall x, EF2FF (FFpayload x) (FF2EF x) = x.
  intro. destruct x; auto.
Qed.

Lemma EF2FF_FF2EF_notnan : forall nan x, is_nan_FF x = false -> EF2FF nan (FF2EF x) = x.
  intros.
  destruct x, nan; auto.
  discriminate.
Qed.

Lemma EF2FF_inj : forall nan x y, EF2FF nan x = EF2FF nan y -> x = y.
  intro. exact (can_inj (FF2EF_EF2FF nan)).
Qed.

Lemma FF2EF_inj : forall x y, FF2EF x = FF2EF y -> FFpayload x = FFpayload y -> x = y.
  intros x y Heq Hpl.
  rewrite <- EF2FF_FF2EF. symmetry. rewrite <- EF2FF_FF2EF.
  rewrite Heq, Hpl. reflexivity.
Qed.

(** Conversions from/to Flocq binary_float *)

Program Definition Prim2B (nan : { pl : bool * positive | nan_pl prec (snd pl) = true }) x :=
  FF2B prec emax (EF2FF nan (Prim2EF x)) _.
Next Obligation.
  remember (Prim2EF x). destruct e; auto.
  rewrite <- valid_binary_equiv.
  rewrite FF2EF_EF2FF.
  rewrite Heqe.
  apply Prim2EF_valid.
  reflexivity.
Qed.

Definition B2Prim (x : binary_float prec emax) := (EF2Prim (B2EF x)).

Lemma B2Prim_Prim2B : forall nan x, B2Prim (Prim2B nan x) = x.
  intros. unfold Prim2B, B2Prim. unfold B2EF. rewrite B2FF_FF2B. rewrite FF2EF_EF2FF.
  apply EF2Prim_Prim2EF.
Qed.

Lemma FF2B_proof_irr (x y : Binary.full_float) (Heq : x = y) (Hx : Binary.valid_binary prec emax x = true) (Hy : Binary.valid_binary prec emax y = true) : FF2B prec emax x Hx = FF2B prec emax y Hy.
  unfold FF2B.
  revert Heq Hx Hy.
  case x, y; auto; try discriminate; try (intro H; inversion H; intros; reflexivity);
  intro H; inversion H; intros; rewrite (eqbool_irrelevance _ Hx Hy); reflexivity.
Qed.

Lemma valid_binary_B2EF : forall (x : binary_float prec emax), valid_binary (B2EF x) = true.
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
  intros. unfold Prim2B, B2Prim. unfold B2EF.
  assert (Hy : Binary.valid_binary prec emax (B2FF x) = true).
  {
    apply valid_binary_B2FF.
  }
  assert (Heq : EF2FF (proj1_sig (Bpayload x)) (Prim2EF (EF2Prim (B2EF x))) = B2FF x).
  {
    rewrite Prim2EF_EF2Prim. unfold B2EF. rewrite Bpayload_FFpayload. rewrite EF2FF_FF2EF. reflexivity.
    apply valid_binary_B2EF.
  }
  rewrite (FF2B_proof_irr _ _ Heq _ Hy).
  apply FF2B_B2FF.
Qed.

Lemma Prim2B_B2Prim_notnan : forall nan x, Binary.is_nan prec emax x = false -> Prim2B nan (B2Prim x) = x.
  intros.
  unfold Prim2B, B2Prim.
  unfold B2EF.
  assert (Hy : Binary.valid_binary prec emax (B2FF x) = true).
  {
    apply valid_binary_B2FF.
  }
  assert (Heq : EF2FF (proj1_sig nan) (Prim2EF (EF2Prim (B2EF x))) = B2FF x).
  {
    rewrite Prim2EF_EF2Prim.
    unfold B2EF.
    rewrite EF2FF_FF2EF_notnan.
    reflexivity.
    rewrite <- (FF2B_B2FF prec emax x Hy) in H.
    rewrite is_nan_FF2B in H.
    assumption.
    apply valid_binary_B2EF.
  }
  rewrite (FF2B_proof_irr _ _ Heq _ Hy).
  apply FF2B_B2FF.
Qed.

Lemma Prim2B_inj : forall nan x y, Prim2B nan x = Prim2B nan y -> x = y.
  intro. exact (can_inj (B2Prim_Prim2B nan)).
Qed.

Lemma B2Prim_inj : forall x y, B2Prim x = B2Prim y -> FFpayload (B2FF x) = FFpayload (B2FF y) -> x = y.
  unfold B2Prim. intros x y Heq Hpl. apply EF2Prim_inj in Heq; try apply valid_binary_B2EF.
  case x, y; try discriminate; unfold B2EF in Heq; simpl in Heq; inversion Heq; try reflexivity.
  * simpl in Hpl. inversion Hpl. revert e. rewrite H1. intro. now rewrite (eqbool_irrelevance _ _ e0).
  * revert e0 Hpl. rewrite H1, H2. intros e0 Hpl. now rewrite (eqbool_irrelevance _ _ e2).
Qed.

Lemma B2EF_Prim2B : forall pl x, B2EF (Prim2B pl x) = Prim2EF x.
  intros. unfold Prim2B. unfold B2EF. rewrite B2FF_FF2B. rewrite FF2EF_EF2FF. reflexivity.
Qed.

Lemma Prim2EF_B2Prim : forall x, Prim2EF (B2Prim x) = B2EF x.
Proof.
intro x; unfold B2Prim.
now rewrite Prim2EF_EF2Prim; [|apply valid_binary_B2EF].
Qed.

(** Basic properties of the Binary64 format *)

Lemma prec_gt_0 : FLX.Prec_gt_0 prec.
  unfold FLX.Prec_gt_0. now compute.
Qed.

Lemma Hmax : (prec < emax)%Z.
  now compute.
Qed.

(** Equivalence between prim_float and Flocq binary_float operations *)

Ltac prove_FP2B EFop_Bop FPop_EFop op_nan :=
  intros; unfold B2Prim; rewrite <- EFop_Bop; apply Prim2EF_inj; rewrite FPop_EFop;
  rewrite !Prim2EF_EF2Prim by (try (rewrite (EFop_Bop _ _ op_nan));
                               try (rewrite (EFop_Bop _ _ prec_gt_0 Hmax op_nan));
                               apply valid_binary_B2EF);
  reflexivity.

Theorem FPopp_Bopp : forall opp_nan x, (-(B2Prim x))%float = B2Prim (Bopp prec emax opp_nan x).
  prove_FP2B @EFopp_Bopp FPopp_EFopp opp_nan.
Qed.

Theorem FPabs_Babs : forall abs_nan x, abs (B2Prim x) = B2Prim (Babs prec emax abs_nan x).
  prove_FP2B @EFabs_Babs FPabs_EFabs abs_nan.
Qed.

Theorem FPcompare_Bcompare : forall x y,
  ((B2Prim x) ?= (B2Prim y))%float = flatten_cmp_opt (Bcompare prec emax x y).
  intros. rewrite FPcompare_EFcompare. rewrite <- EFcompare_Bcompare. unfold B2Prim.
  rewrite !Prim2EF_EF2Prim by apply valid_binary_B2EF. reflexivity.
Qed.

Theorem FPmult_Bmult : forall mult_nan x y, ((B2Prim x)*(B2Prim y))%float = B2Prim (Bmult prec emax eq_refl eq_refl mult_nan mode_NE x y).
  prove_FP2B @EFmult_Bmult FPmult_EFmult mult_nan.
Qed.

Theorem FPplus_Bplus : forall plus_nan x y, ((B2Prim x)+(B2Prim y))%float = B2Prim (Bplus prec emax eq_refl eq_refl plus_nan mode_NE x y).
  prove_FP2B @EFplus_Bplus FPplus_EFplus plus_nan.
Qed.

Theorem FPminus_Bminus : forall minus_nan x y, ((B2Prim x)-(B2Prim y))%float = B2Prim (Bminus prec emax eq_refl eq_refl minus_nan mode_NE x y).
  prove_FP2B @EFminus_Bminus FPminus_EFminus minus_nan.
Qed.

Theorem FPdiv_Bdiv : forall div_nan x y, ((B2Prim x)/(B2Prim y))%float = B2Prim (Bdiv prec emax eq_refl eq_refl div_nan mode_NE x y).
  prove_FP2B @EFdiv_Bdiv FPdiv_EFdiv div_nan.
Qed.

Theorem FPsqrt_Bsqrt : forall sqrt_nan x, sqrt (B2Prim x) = B2Prim (Bsqrt prec emax eq_refl eq_refl sqrt_nan mode_NE x).
  prove_FP2B @EFsqrt_Bsqrt FPsqrt_EFsqrt sqrt_nan.
Qed.

Require Import Flocq_complements.

Theorem FPnormfr_mantissa_Bnormfr_mantissa :
  forall x,
  normfr_mantissa (B2Prim x) = Int63Op.of_Z (Z.of_N (Bnormfr_mantissa prec emax x)).
Proof.
intro x; unfold B2Prim.
rewrite <-EFnormfr_mantissa_Bnormfr_mantissa.
rewrite <-(Prim2EF_EF2Prim (B2EF x)) at 2; [|apply valid_binary_B2EF].
rewrite <-normfr_mantissa_spec.
now rewrite Int63Axioms.of_to_Z.
Qed.

Theorem FPldexp_Bldexp :
  forall x e,
  ldexp (B2Prim x) e = B2Prim (Bldexp prec emax prec_gt_0 Hmax mode_NE x e).
Proof.
intros x e; unfold B2Prim.
rewrite <-EFldexp_Bldexp.
rewrite <-(Prim2EF_EF2Prim (B2EF x)) at 2; [|apply valid_binary_B2EF].
rewrite <-ldexp_spec.
now rewrite EF2Prim_Prim2EF.
Qed.

Lemma Hemax : (3 <= emax)%Z.
Proof. now compute. Qed.

Theorem FPfrexp_Bfrexp :
  forall x,
  fst (frexp (B2Prim x)) = B2Prim (fst (Bfrexp prec emax prec_gt_0 Hemax x)) /\
  snd (frexp (B2Prim x)) = snd (Bfrexp prec emax prec_gt_0 Hemax x).
Proof.
intro x; unfold B2Prim.
rewrite <-(proj1 (EFfrexp_Bfrexp prec_gt_0 Hemax _)).
rewrite <-(proj2 (EFfrexp_Bfrexp prec_gt_0 Hemax _)).
rewrite <-(Prim2EF_EF2Prim (B2EF x)) at 2 4; [|apply valid_binary_B2EF].
generalize (frexp_spec (EF2Prim (B2EF x))).
case_eq (frexp (EF2Prim (B2EF x))); intros f z Hfz Hfrexp.
now rewrite <-Hfrexp; simpl; rewrite EF2Prim_Prim2EF.
Qed.

Theorem FPone_Bone : one = B2Prim (Bone prec emax prec_gt_0 Hmax).
Proof. now unfold B2Prim; rewrite <-EFone_Bone; compute. Qed.

Theorem FPulp_Bulp :
  forall x,
  ulp (B2Prim x) = B2Prim (Bulp prec emax prec_gt_0 Hmax Hemax x).
Proof.
intros x; unfold B2Prim, ulp.
rewrite <-EFulp_Bulp; unfold EFulp.
generalize (frexp_spec (EF2Prim (B2EF x))).
case_eq (frexp (EF2Prim (B2EF x))); intros f z Hfz.
rewrite Prim2EF_EF2Prim; [|apply valid_binary_B2EF].
intro Hfrexp; rewrite <-Hfrexp; unfold snd.
change (EFone prec emax) with (Prim2EF one).
now rewrite <-ldexp_spec, EF2Prim_Prim2EF.
Qed.

Theorem FPnext_up_Bsucc :
  forall succ_nan x,
  next_up (B2Prim x)
  = B2Prim (Bsucc prec emax prec_gt_0 Hmax Hemax succ_nan x).
Proof.
intros succ_nan x; unfold B2Prim.
rewrite <-EFsucc_Bsucc.
rewrite <-(Prim2EF_EF2Prim (B2EF x)) at 2; [|apply valid_binary_B2EF].
rewrite <-FPnext_up_EFsucc.
now rewrite EF2Prim_Prim2EF.
Qed.

Theorem FPnext_down_Bpred :
  forall pred_nan x,
  next_down (B2Prim x)
  = B2Prim (Bpred prec emax prec_gt_0 Hmax Hemax pred_nan x).
Proof.
intros pred_nan x; unfold B2Prim.
rewrite <-EFpred_Bpred.
rewrite <-(Prim2EF_EF2Prim (B2EF x)) at 2; [|apply valid_binary_B2EF].
rewrite <-FPnext_down_EFpred.
now rewrite EF2Prim_Prim2EF.
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
