Require Import ZArith Flocq.Core.Core Flocq.IEEE754.Binary SpecFloat.

Arguments B754_finite {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_zero {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B2FF {prec} {emax}.

Section SF2B.

Context {prec emax : Z}.
Context (prec_gt_0_ : Prec_gt_0 prec).
Hypothesis Hmax : (prec < emax)%Z.
(** The following hypothesis is required for Bfrexp *)
Hypothesis Hemax : (3 <= emax)%Z.

Definition FF2SF (x : full_float) :=
  match x with
  | F754_finite s m e => S754_finite s m e
  | F754_infinity s => S754_infinity s
  | F754_zero s => S754_zero s
  | F754_nan b pl => S754_nan
  end.

Lemma fexp_equiv : forall e, fexp prec emax e = FLT.FLT_exp (3 - emax - prec) prec e.
  intros. unfold fexp, FLT.FLT_exp. unfold emin. reflexivity.
Qed.

Lemma valid_binary_equiv :
  forall x, is_nan_FF x = false -> SpecFloat.valid_binary prec emax (FF2SF x) = Binary.valid_binary prec emax x.
  intros. destruct x; auto. discriminate.
Qed.

Definition Floc2loc (x : Bracket.location) :=
  match x with
  | Bracket.loc_Exact => SpecFloat.loc_Exact
  | Bracket.loc_Inexact l => SpecFloat.loc_Inexact l
  end.

Definition Fshr2shr (mrs : Binary.shr_record) :=
  let '(Binary.Build_shr_record m r s) := mrs in
  SpecFloat.Build_shr_record m r s.

Lemma shr_1_equiv : forall mrs, SpecFloat.shr_1 (Fshr2shr mrs) = Fshr2shr (Binary.shr_1 mrs).
  intro. destruct mrs. unfold shr_1, Binary.shr_1.
  destruct shr_m; auto; destruct p; auto.
Qed.

Lemma loc_of_shr_record_equiv : forall mrs, SpecFloat.loc_of_shr_record (Fshr2shr mrs) = Floc2loc (Binary.loc_of_shr_record mrs).
  intro. destruct mrs. destruct shr_r, shr_s; auto.
Qed.

Lemma shr_record_of_loc_equiv : forall m l, SpecFloat.shr_record_of_loc m (Floc2loc l) = Fshr2shr (Binary.shr_record_of_loc m l).
  intros. destruct l; auto. destruct c; auto.
Qed.

Lemma shr_iter_equiv : forall p mrs, iter_pos shr_1 p (Fshr2shr mrs) = Fshr2shr (Zaux.iter_pos Binary.shr_1 p mrs).
  intros. revert mrs. induction p; intro; simpl.
  rewrite shr_1_equiv. rewrite IHp. rewrite IHp. reflexivity.
  rewrite IHp. rewrite IHp. reflexivity.
  apply shr_1_equiv.
Qed.

Lemma shr_equiv : forall mrs e n, SpecFloat.shr (Fshr2shr mrs) e n = let (mrs, e) := Binary.shr mrs e n in (Fshr2shr mrs, e).
  intros. destruct n; auto. simpl. rewrite shr_iter_equiv. reflexivity.
Qed.

Lemma shr_fexp_equiv : forall m e l, SpecFloat.shr_fexp prec emax m e (Floc2loc l) = let (mrs, e') := Binary.shr_fexp prec emax m e l in (Fshr2shr mrs, e').
  intros. unfold shr_fexp, Binary.shr_fexp. rewrite shr_record_of_loc_equiv. rewrite shr_equiv.
  now rewrite fexp_equiv.
Qed.

Lemma round_nearest_even_equiv : forall sx mx lx, round_nearest_even mx (Floc2loc lx) = choice_mode mode_NE sx mx lx.
  intros. unfold round_nearest_even, choice_mode.
  destruct lx; [now simpl|].
  now case c; simpl; [case (Z.even mx)| |].
Qed.

Lemma binary_round_aux_equiv : forall sx mx ex lx, SpecFloat.binary_round_aux prec emax sx mx ex (Floc2loc lx) = FF2SF (Binary.binary_round_aux prec emax mode_NE sx mx ex lx).
  intros. unfold binary_round_aux, Binary.binary_round_aux. rewrite shr_fexp_equiv. set (Binary.shr_fexp prec emax mx ex lx). destruct p.
  rewrite loc_of_shr_record_equiv. rewrite <- round_nearest_even_equiv. unfold Binary.binary_overflow, binary_overflow; simpl. change loc_Exact with (Floc2loc Bracket.loc_Exact). rewrite shr_fexp_equiv. destruct s; simpl.
  set (Binary.shr_fexp prec emax _ _ _). destruct p. destruct s; simpl.
  destruct shr_m0; simpl; auto. unfold FF2SF. set (z0 <=? emax - prec)%Z.
  destruct b; auto.
Qed.

Lemma binary_round_equiv : forall sx mx ex, SpecFloat.binary_round prec emax sx mx ex = FF2SF (Binary.binary_round prec emax mode_NE sx mx ex).
  intros. unfold binary_round, Binary.binary_round.
  change loc_Exact with (Floc2loc Bracket.loc_Exact).
  unfold shl_align_fexp, Binary.shl_align_fexp. rewrite fexp_equiv.
  change digits2_pos with Digits.digits2_pos.
  change shl_align with Binary.shl_align.
  set (Binary.shl_align mx ex (FLT.FLT_exp (3 - emax - prec) prec (Z.pos (Digits.digits2_pos mx) + ex))). destruct p. apply binary_round_aux_equiv.
Qed.

Definition B2SF (x : binary_float prec emax) := FF2SF (B2FF x).

Lemma binary_normalize_equiv : forall m e szero, SpecFloat.binary_normalize prec emax m e szero = B2SF (Binary.binary_normalize prec emax prec_gt_0_ Hmax mode_NE m e szero).
  intros. unfold binary_normalize, Binary.binary_normalize. destruct m; auto; unfold B2SF; rewrite B2FF_FF2B; apply binary_round_equiv.
Qed.

Lemma B2SF_build_nan : forall nan, S754_nan = B2SF (build_nan prec emax nan).
  intros. unfold build_nan. destruct nan. destruct x; try (discriminate). reflexivity.
Qed.

Theorem SFopp_Bopp : forall opp_nan (x : binary_float prec emax), SFopp (B2SF x) = B2SF (Bopp prec emax opp_nan x).
  intros. destruct x; auto.
Qed.

Theorem SFabs_Babs : forall abs_nan (x : binary_float prec emax), SFabs (B2SF x) = B2SF (Babs prec emax abs_nan x).
  intros. destruct x; auto.
Qed.

Theorem SFcompare_Bcompare : forall x y, SFcompare (B2SF x) (B2SF y) = Bcompare prec emax x y.
  intros. destruct x, y; auto.
Qed.

Theorem SFmult_Bmult : forall mult_nan x y, SFmult prec emax (B2SF x) (B2SF y) = B2SF (Bmult prec emax prec_gt_0_ Hmax mult_nan mode_NE x y).
  intros. destruct x, y; auto; simpl; try (apply B2SF_build_nan). unfold B2SF.
  rewrite B2FF_FF2B. change loc_Exact with (Floc2loc Bracket.loc_Exact). apply binary_round_aux_equiv.
Qed.

Theorem SFplus_Bplus : forall plus_nan x y, SFplus prec emax (B2SF x) (B2SF y) = B2SF (Bplus prec emax prec_gt_0_ Hmax plus_nan mode_NE x y).
  intros.
  destruct x, y; auto; simpl; try (apply B2SF_build_nan); try (destruct (Bool.eqb _ _)); auto.
  apply binary_normalize_equiv.
Qed.

Theorem SFminus_Bminus : forall minus_nan x y, SFminus prec emax (B2SF x) (B2SF y) = B2SF (Bminus prec emax prec_gt_0_ Hmax minus_nan mode_NE x y).
  intros.
  destruct x, y; auto; simpl; try (apply B2SF_build_nan); try (destruct (Bool.eqb _ _)); auto.
  apply binary_normalize_equiv.
Qed.

Lemma new_location_even_equiv : forall nb_steps k, SpecFloat.new_location_even nb_steps k = Floc2loc (Bracket.new_location_even nb_steps k Bracket.loc_Exact).
  intros. unfold new_location_even, Bracket.new_location_even. set (Zeq_bool k 0).
  now destruct b; [|case (_ ?= _)%Z].
Qed.

Lemma new_location_odd_equiv : forall nb_steps k, SpecFloat.new_location_odd nb_steps k = Floc2loc (Bracket.new_location_odd nb_steps k Bracket.loc_Exact).
  intros. unfold new_location_odd, Bracket.new_location_odd. set (Zeq_bool k 0).
  now destruct b; [|case (_ ?= _)%Z].
Qed.

Lemma new_location_equiv : forall nb_steps k, SpecFloat.new_location nb_steps k = Floc2loc (Bracket.new_location nb_steps k Bracket.loc_Exact).
  intros. unfold new_location, Bracket.new_location.
  set (Z.even nb_steps); destruct b. apply new_location_even_equiv.
  apply new_location_odd_equiv.
Qed.

Lemma div_core_binary_equiv : forall m1 e1 m2 e2, SFdiv_core_binary prec emax m1 e1 m2 e2 = let '(q, e, l) := Fdiv_core_binary prec emax m1 e1 m2 e2 in (q, e, Floc2loc l).
  intros. unfold SFdiv_core_binary, Fdiv_core_binary.
  rewrite Zaux.Zfast_div_eucl_correct. rewrite <- fexp_equiv.
  change loc_Exact with (Floc2loc Bracket.loc_Exact).
  set (Z.div_eucl _ _). destruct p. rewrite new_location_equiv. reflexivity.
Qed.

Theorem SFdiv_Bdiv : forall Hmax div_nan x y, SFdiv prec emax (B2SF x) (B2SF y) = B2SF (Bdiv prec emax prec_gt_0_ Hmax div_nan mode_NE x y).
  intros. destruct x, y; auto; simpl; try (apply B2SF_build_nan).
  unfold B2SF; rewrite B2FF_FF2B. rewrite div_core_binary_equiv.
  set (Fdiv_core_binary _ _ _ _ _ _). destruct p. destruct p.
  apply binary_round_aux_equiv.
Qed.

Lemma sqrt_core_binary_equiv : forall m e, SFsqrt_core_binary prec emax m e = let '(q, e, l) := Fsqrt_core_binary prec emax m e in (q, e, Floc2loc l).
  intros. unfold SFsqrt_core_binary, Fsqrt_core_binary. rewrite <- fexp_equiv.
  set (Z.sqrtrem _). destruct p. set (Zeq_bool z0 0). destruct b; auto.
Qed.

Theorem SFsqrt_Bsqrt : forall sqrt_nan x, SFsqrt prec emax (B2SF x) = B2SF (Bsqrt prec emax prec_gt_0_ Hmax sqrt_nan mode_NE x).
  intros. destruct x; destruct s ; try (apply B2SF_build_nan); auto.
  simpl. unfold B2SF.  rewrite B2FF_FF2B. rewrite sqrt_core_binary_equiv.
  set (Fsqrt_core_binary _ _ _ _). destruct p. destruct p.
  apply binary_round_aux_equiv.
Qed.

Theorem SFnormfr_mantissa_Bnormfr_mantissa :
  forall x,
  SFnormfr_mantissa prec (B2SF x) = Bnormfr_mantissa prec emax x.
Proof. now intro x; case x. Qed.

Theorem SFldexp_Bldexp :
  forall x e,
  SFldexp prec emax (B2SF x) e
  = B2SF (Bldexp prec emax prec_gt_0_ Hmax mode_NE x e).
Proof.
intros [s|s|s pl H|sx mx ex Hmex] e; [now easy|now easy|now easy|].
simpl; unfold B2SF; rewrite B2FF_FF2B; apply binary_round_equiv.
Qed.

Theorem SFfrexp_Bfrexp :
  forall x,
  fst (SFfrexp prec emax (B2SF x))
  = B2SF (fst (Bfrexp prec emax prec_gt_0_ Hemax x)) /\
  snd (SFfrexp prec emax (B2SF x))
  = snd (Bfrexp prec emax prec_gt_0_ Hemax x).
Proof.
intros [s|s|s pl H|s m e Hme]; [now easy|now easy|now easy|].
simpl; unfold B2SF, Ffrexp_core_binary; rewrite B2FF_FF2B.
change (digits2_pos m) with (Digits.digits2_pos m).
now case (_ <=? _)%positive.
Qed.

Theorem SFone_Bone : SFone prec emax = B2SF (Bone prec emax prec_gt_0_ Hmax).
Proof. unfold B2SF, Bone; rewrite B2FF_FF2B; apply binary_round_equiv. Qed.

Theorem SFulp_Bulp :
  forall x,
  SFulp prec emax (B2SF x) = B2SF (Bulp prec emax prec_gt_0_ Hmax Hemax x).
Proof.
intro x; unfold SFulp.
now rewrite SFone_Bone, SFldexp_Bldexp, fexp_equiv, (proj2 (SFfrexp_Bfrexp x)).
Qed.

Theorem SFpred_pos_Bpred_pos :
  forall pred_pos_nan x,
  SFpred_pos prec emax (B2SF x)
  = B2SF (Bpred_pos prec emax prec_gt_0_ Hmax Hemax pred_pos_nan x).
Proof.
intros pred_pos_nan [s|s|s pl H|s m e Hme]; [now easy|now easy|now easy|].
unfold SFpred_pos, Bpred_pos.
rewrite fexp_equiv, (proj2 (SFfrexp_Bfrexp _)), SFulp_Bulp.
rewrite SFone_Bone, SFldexp_Bldexp.
set (d1 := Bldexp _ _ _ _ _ _ _).
set (d2 := Bulp _ _ _ _ _ _).
Opaque SFminus Bminus.
simpl.
Transparent SFminus Bminus.
case (_ =? _)%positive; apply SFminus_Bminus.
Qed.

Theorem SFmax_float_Bmax_float :
  SFmax_float prec emax = B2SF (Bmax_float prec emax prec_gt_0_ Hmax).
Proof. now simpl. Qed.

Theorem SFsucc_Bsucc :
  forall succ_nan x,
  SFsucc prec emax (B2SF x)
  = B2SF (Bsucc prec emax prec_gt_0_ Hmax Hemax succ_nan x).
Proof.
unfold SFsucc, B2SF at 1, B2FF, FF2SF, Bsucc.
intros succ_nan [s|s|s pl H|s m e Hme]; [| |now easy|].
- now rewrite SFone_Bone, SFldexp_Bldexp.
- now rewrite SFmax_float_Bmax_float; case s.
- rewrite (SFopp_Bopp succ_nan), (SFpred_pos_Bpred_pos succ_nan).
  rewrite (SFopp_Bopp succ_nan), SFulp_Bulp.
  set (plus_nan := fun _ => succ_nan).
  now rewrite (SFplus_Bplus plus_nan); case s.
Qed.

Theorem SFpred_Bpred :
  forall pred_nan x,
  SFpred prec emax (B2SF x)
  = B2SF (Bpred prec emax prec_gt_0_ Hmax Hemax pred_nan x).
Proof.
intros pred_nan x; unfold SFpred, Bpred; rewrite (SFopp_Bopp pred_nan).
now rewrite (SFsucc_Bsucc pred_nan), (SFopp_Bopp pred_nan).
Qed.

End SF2B.
