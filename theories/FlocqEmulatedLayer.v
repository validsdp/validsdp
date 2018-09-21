Require Import ZArith Flocq.Core.Core Flocq.IEEE754.Binary EmulatedFloat.

Arguments B754_finite {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_zero {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B2FF {prec} {emax}.

Section EF2B.

Context {prec emax : Z}.
Context (prec_gt_0_ : Prec_gt_0 prec).
Hypothesis Hmax : (prec < emax)%Z.
(** The following hypothesis is required for Bfrexp *)
Hypothesis Hemax : (3 <= emax)%Z.

Definition FF2EF (x : full_float) :=
  match x with
  | F754_finite s m e => E754_finite s m e
  | F754_infinity s => E754_infinity s
  | F754_zero s => E754_zero s
  | F754_nan b pl => E754_nan
  end.

Lemma fexp_equiv : forall e, fexp prec emax e = FLT.FLT_exp (3 - emax - prec) prec e.
  intros. unfold fexp, FLT.FLT_exp. unfold emin. reflexivity.
Qed.

Lemma valid_binary_equiv :
  forall x, is_nan_FF x = false -> EmulatedFloat.valid_binary prec emax (FF2EF x) = Binary.valid_binary prec emax x.
  intros. destruct x; auto. discriminate.
Qed.

Definition Floc2loc (x : Bracket.location) :=
  match x with
  | Bracket.loc_Exact => EmulatedFloat.loc_Exact
  | Bracket.loc_Inexact l => EmulatedFloat.loc_Inexact l
  end.

Definition Fshr2shr (mrs : Binary.shr_record) :=
  let '(Binary.Build_shr_record m r s) := mrs in
  EmulatedFloat.Build_shr_record m r s.

Lemma shr_1_equiv : forall mrs, EmulatedFloat.shr_1 (Fshr2shr mrs) = Fshr2shr (Binary.shr_1 mrs).
  intro. destruct mrs. unfold shr_1, Binary.shr_1.
  destruct shr_m; auto; destruct p; auto.
Qed.

Lemma loc_of_shr_record_equiv : forall mrs, EmulatedFloat.loc_of_shr_record (Fshr2shr mrs) = Floc2loc (Binary.loc_of_shr_record mrs).
  intro. destruct mrs. destruct shr_r, shr_s; auto.
Qed.

Lemma shr_record_of_loc_equiv : forall m l, EmulatedFloat.shr_record_of_loc m (Floc2loc l) = Fshr2shr (Binary.shr_record_of_loc m l).
  intros. destruct l; auto. destruct c; auto.
Qed.

Lemma shr_iter_equiv : forall p mrs, iter_pos shr_1 p (Fshr2shr mrs) = Fshr2shr (Zaux.iter_pos Binary.shr_1 p mrs).
  intros. revert mrs. induction p; intro; simpl.
  rewrite shr_1_equiv. rewrite IHp. rewrite IHp. reflexivity.
  rewrite IHp. rewrite IHp. reflexivity.
  apply shr_1_equiv.
Qed.

Lemma shr_equiv : forall mrs e n, EmulatedFloat.shr (Fshr2shr mrs) e n = let (mrs, e) := Binary.shr mrs e n in (Fshr2shr mrs, e).
  intros. destruct n; auto. simpl. rewrite shr_iter_equiv. reflexivity.
Qed.

Lemma shr_fexp_equiv : forall m e l, EmulatedFloat.shr_fexp prec emax m e (Floc2loc l) = let (mrs, e') := Binary.shr_fexp prec emax m e l in (Fshr2shr mrs, e').
  intros. unfold shr_fexp, Binary.shr_fexp. rewrite shr_record_of_loc_equiv. rewrite shr_equiv.
  now rewrite fexp_equiv.
Qed.

Lemma round_N_equiv : forall p l, EmulatedFloat.round_N p (Floc2loc l) = Round.round_N p l.
  intros. now destruct l.
Qed.

Lemma round_nearest_even_equiv : forall sx mx lx, round_nearest_even mx (Floc2loc lx) = choice_mode mode_NE sx mx lx.
  intros. unfold round_nearest_even, choice_mode. rewrite round_N_equiv. reflexivity.
Qed.

Lemma binary_round_aux_equiv : forall sx mx ex lx, EmulatedFloat.binary_round_aux prec emax sx mx ex (Floc2loc lx) = FF2EF (Binary.binary_round_aux prec emax mode_NE sx mx ex lx).
  intros. unfold binary_round_aux, Binary.binary_round_aux. rewrite shr_fexp_equiv. set (Binary.shr_fexp prec emax mx ex lx). destruct p.
  rewrite loc_of_shr_record_equiv. rewrite <- round_nearest_even_equiv. unfold Binary.binary_overflow, binary_overflow; simpl. change loc_Exact with (Floc2loc Bracket.loc_Exact). rewrite shr_fexp_equiv. destruct s; simpl.
  set (Binary.shr_fexp prec emax _ _ _). destruct p. destruct s; simpl.
  destruct shr_m0; simpl; auto. unfold FF2EF. set (z0 <=? emax - prec)%Z.
  destruct b; auto.
Qed.

Lemma binary_round_equiv : forall sx mx ex, EmulatedFloat.binary_round prec emax sx mx ex = FF2EF (Binary.binary_round prec emax mode_NE sx mx ex).
  intros. unfold binary_round, Binary.binary_round.
  change loc_Exact with (Floc2loc Bracket.loc_Exact).
  unfold shl_align_fexp, Binary.shl_align_fexp. rewrite fexp_equiv.
  change digits2_pos with Digits.digits2_pos.
  change shl_align with Binary.shl_align.
  set (Binary.shl_align mx ex (FLT.FLT_exp (3 - emax - prec) prec (Z.pos (Digits.digits2_pos mx) + ex))). destruct p. apply binary_round_aux_equiv.
Qed.

Definition B2EF (x : binary_float prec emax) := FF2EF (B2FF x).

Lemma binary_normalize_equiv : forall m e szero, EmulatedFloat.binary_normalize prec emax m e szero = B2EF (Binary.binary_normalize prec emax prec_gt_0_ Hmax mode_NE m e szero).
  intros. unfold binary_normalize, Binary.binary_normalize. destruct m; auto; unfold B2EF; rewrite B2FF_FF2B; apply binary_round_equiv.
Qed.

Lemma B2EF_build_nan : forall nan, E754_nan = B2EF (build_nan prec emax nan).
  intros. unfold build_nan. destruct nan. destruct x; try (discriminate). reflexivity.
Qed.

Theorem EFopp_Bopp : forall opp_nan (x : binary_float prec emax), EFopp (B2EF x) = B2EF (Bopp prec emax opp_nan x).
  intros. destruct x; auto.
Qed.

Theorem EFabs_Babs : forall abs_nan (x : binary_float prec emax), EFabs (B2EF x) = B2EF (Babs prec emax abs_nan x).
  intros. destruct x; auto.
Qed.

Theorem EFcompare_Bcompare : forall x y, EFcompare (B2EF x) (B2EF y) = Bcompare prec emax x y.
  intros. destruct x, y; auto.
Qed.

Theorem EFmult_Bmult : forall mult_nan x y, EFmult prec emax (B2EF x) (B2EF y) = B2EF (Bmult prec emax prec_gt_0_ Hmax mult_nan mode_NE x y).
  intros. destruct x, y; auto; simpl; try (apply B2EF_build_nan). unfold B2EF.
  rewrite B2FF_FF2B. change loc_Exact with (Floc2loc Bracket.loc_Exact). apply binary_round_aux_equiv.
Qed.

Theorem EFplus_Bplus : forall plus_nan x y, EFplus prec emax (B2EF x) (B2EF y) = B2EF (Bplus prec emax prec_gt_0_ Hmax plus_nan mode_NE x y).
  intros.
  destruct x, y; auto; simpl; try (apply B2EF_build_nan); try (destruct (Bool.eqb _ _)); auto.
  apply binary_normalize_equiv.
Qed.

Theorem EFminus_Bminus : forall minus_nan x y, EFminus prec emax (B2EF x) (B2EF y) = B2EF (Bminus prec emax prec_gt_0_ Hmax minus_nan mode_NE x y).
  intros.
  destruct x, y; auto; simpl; try (apply B2EF_build_nan); try (destruct (Bool.eqb _ _)); auto.
  apply binary_normalize_equiv.
Qed.

Lemma new_location_even_equiv : forall nb_steps k l, EmulatedFloat.new_location_even nb_steps k (Floc2loc l) = Floc2loc (Bracket.new_location_even nb_steps k l).
  intros. unfold new_location_even, Bracket.new_location_even. set (Zeq_bool k 0).
  destruct b. destruct l; auto. set (2 * k ?= nb_steps)%Z. destruct c; auto. destruct l; auto.
Qed.

Lemma new_location_odd_equiv : forall nb_steps k l, EmulatedFloat.new_location_odd nb_steps k (Floc2loc l) = Floc2loc (Bracket.new_location_odd nb_steps k l).
  intros. unfold new_location_odd, Bracket.new_location_odd. set (Zeq_bool k 0).
  destruct b. destruct l; auto. set (2 * k + 1 ?= nb_steps)%Z.
  destruct c; auto. destruct l; auto.
Qed.

Lemma new_location_equiv : forall nb_steps k l, EmulatedFloat.new_location nb_steps k (Floc2loc l) = Floc2loc (Bracket.new_location nb_steps k l).
  intros. unfold new_location, Bracket.new_location.
  set (Z.even nb_steps); destruct b. apply new_location_even_equiv.
  apply new_location_odd_equiv.
Qed.

Lemma div_core_binary_equiv : forall m1 e1 m2 e2, EFdiv_core_binary prec emax m1 e1 m2 e2 = let '(q, e, l) := Fdiv_core_binary prec emax m1 e1 m2 e2 in (q, e, Floc2loc l).
  intros. unfold EFdiv_core_binary, Fdiv_core_binary.
  rewrite Zaux.Zfast_div_eucl_correct. rewrite <- fexp_equiv.
  change loc_Exact with (Floc2loc Bracket.loc_Exact).
  set (Z.div_eucl _ _). destruct p. rewrite new_location_equiv. reflexivity.
Qed.

Theorem EFdiv_Bdiv : forall Hmax div_nan x y, EFdiv prec emax (B2EF x) (B2EF y) = B2EF (Bdiv prec emax prec_gt_0_ Hmax div_nan mode_NE x y).
  intros. destruct x, y; auto; simpl; try (apply B2EF_build_nan).
  unfold B2EF; rewrite B2FF_FF2B. rewrite div_core_binary_equiv.
  set (Fdiv_core_binary _ _ _ _ _ _). destruct p. destruct p.
  apply binary_round_aux_equiv.
Qed.

Lemma sqrt_core_binary_equiv : forall m e, EFsqrt_core_binary prec emax m e = let '(q, e, l) := Fsqrt_core_binary prec emax m e in (q, e, Floc2loc l).
  intros. unfold EFsqrt_core_binary, Fsqrt_core_binary. rewrite <- fexp_equiv.
  set (Z.sqrtrem _). destruct p. set (Zeq_bool z0 0). destruct b; auto.
Qed.

Theorem EFsqrt_Bsqrt : forall sqrt_nan x, EFsqrt prec emax (B2EF x) = B2EF (Bsqrt prec emax prec_gt_0_ Hmax sqrt_nan mode_NE x).
  intros. destruct x; destruct s ; try (apply B2EF_build_nan); auto.
  simpl. unfold B2EF.  rewrite B2FF_FF2B. rewrite sqrt_core_binary_equiv.
  set (Fsqrt_core_binary _ _ _ _). destruct p. destruct p.
  apply binary_round_aux_equiv.
Qed.

Require Import Flocq_complements.

Theorem EFnormfr_mantissa_Bnormfr_mantissa :
  forall x,
  EFnormfr_mantissa prec (B2EF x) = Bnormfr_mantissa prec emax x.
Proof. now intro x; case x. Qed.

Theorem EFldexp_Bldexp :
  forall x e,
  EFldexp prec emax (B2EF x) e
  = B2EF (Bldexp prec emax prec_gt_0_ Hmax mode_NE x e).
Proof.
intros [s|s|s pl H|sx mx ex Hmex] e; [now easy|now easy|now easy|].
simpl; unfold B2EF; rewrite B2FF_FF2B; apply binary_round_equiv.
Qed.

Theorem EFfrexp_Bfrexp :
  forall x,
  fst (EFfrexp prec emax (B2EF x))
  = B2EF (fst (Bfrexp prec emax prec_gt_0_ Hemax x)) /\
  snd (EFfrexp prec emax (B2EF x))
  = snd (Bfrexp prec emax prec_gt_0_ Hemax x).
Proof.
intros [s|s|s pl H|s m e Hme]; [now easy|now easy|now easy|].
simpl; unfold B2EF, Ffrexp_core_binary; rewrite B2FF_FF2B.
change (digits2_pos m) with (Digits.digits2_pos m).
now case (_ <=? _)%positive.
Qed.

Theorem EFone_Bone : EFone prec emax = B2EF (Bone prec emax prec_gt_0_ Hmax).
Proof. unfold B2EF, Bone; rewrite B2FF_FF2B; apply binary_round_equiv. Qed.

Theorem EFulp_Bulp :
  forall x,
  EFulp prec emax (B2EF x) = B2EF (Bulp prec emax prec_gt_0_ Hmax Hemax x).
Proof.
intro x; unfold EFulp.
now rewrite EFone_Bone, EFldexp_Bldexp, fexp_equiv, (proj2 (EFfrexp_Bfrexp x)).
Qed.

Theorem EFpred_pos_Bpred_pos :
  forall pred_pos_nan x,
  EFpred_pos prec emax (B2EF x)
  = B2EF (Bpred_pos prec emax prec_gt_0_ Hmax Hemax pred_pos_nan x).
Proof.
intros pred_pos_nan [s|s|s pl H|s m e Hme]; [now easy|now easy|now easy|].
unfold EFpred_pos, Bpred_pos.
rewrite fexp_equiv, (proj2 (EFfrexp_Bfrexp _)), EFulp_Bulp.
rewrite EFone_Bone, EFldexp_Bldexp.
set (d1 := Bldexp _ _ _ _ _ _ _).
set (d2 := Bulp _ _ _ _ _ _).
Opaque EFminus Bminus.
simpl.
Transparent EFminus Bminus.
case (_ =? _)%positive; apply EFminus_Bminus.
Qed.

Theorem EFmax_float_Bmax_float :
  EFmax_float prec emax = B2EF (Bmax_float prec emax prec_gt_0_ Hemax).
Proof. now simpl. Qed.

Theorem EFsucc_Bsucc :
  forall succ_nan x,
  EFsucc prec emax (B2EF x)
  = B2EF (Bsucc prec emax prec_gt_0_ Hmax Hemax succ_nan x).
Proof.
unfold EFsucc, B2EF at 1, B2FF, FF2EF, Bsucc.
intros succ_nan [s|s|s pl H|s m e Hme]; [| |now easy|].
- now rewrite EFone_Bone, EFldexp_Bldexp.
- now rewrite EFmax_float_Bmax_float; case s.
- rewrite (EFopp_Bopp succ_nan), (EFpred_pos_Bpred_pos succ_nan).
  rewrite (EFopp_Bopp succ_nan), EFulp_Bulp.
  set (plus_nan := fun _ => succ_nan).
  now rewrite (EFplus_Bplus plus_nan); case s.
Qed.

Theorem EFpred_Bpred :
  forall pred_nan x,
  EFpred prec emax (B2EF x)
  = B2EF (Bpred prec emax prec_gt_0_ Hmax Hemax pred_nan x).
Proof.
intros pred_nan x; unfold EFpred, Bpred; rewrite (EFopp_Bopp pred_nan).
now rewrite (EFsucc_Bsucc pred_nan), (EFopp_Bopp pred_nan).
Qed.

End EF2B.
