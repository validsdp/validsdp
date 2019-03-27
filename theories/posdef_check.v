(* (setq coq-prog-name "~/forge/git/validsdp/coq/bin/coqtop") *)
(** * Main tactic for multivariate polynomial positivity. *)

Require Import ZArith.
From Flocq Require Import Core. Require Import Datatypes.
From Interval Require Import Interval_definitions Interval_xreal.
From Interval Require Import Interval_missing.
From Interval Require Import Interval_specific_ops. (* for Float *)
From CoqEAL.theory Require Import ssrcomplements.
From CoqEAL.refinements Require Import hrel refinements param seqmx seqmx_complements binnat binint rational binrat.
Require Import Reals Flocq.Core.Raux QArith Psatz FSetAVL.
From Bignums Require Import BigZ BigQ.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype tuple matrix ssralg bigop.
From mathcomp Require Import ssrnum rat div.
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
Import Refinements.Op.
Require Import cholesky_prog coqinterval_infnan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Part 1: Generic programs *)

Section generic_posdef_check.

Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context `{!fun_of_of F ord (mx F), !row_of ord (mx F), !store_of F ord (mx F), !dotmulB0_of F ord (mx F)}.
Context `{!heq_of (mx F), !trmx_of (mx F)}.

Context {s : nat}.
Context `{!I0_class ord s, !succ0_class ord s, !nat_of_class ord s}.

Definition posdefcheck (Q : mx F s s) : bool :=
  posdef_check (@float_infnan_spec.fieps fs) (@float_infnan_spec.fieta fs)
               (@float_infnan_spec.finite fs) Q.

End generic_posdef_check.

Section eff_posdef_check.

(** *** General definitions for seqmx and effmpoly *)

Let mx := @hseqmx.

Context {s : nat}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.

Definition posdefcheck_eff : mx F s.+1 s.+1 -> bool := posdefcheck.

End eff_posdef_check.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_posdef_check.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.

Definition posdefcheck_ssr (s : nat) : 'M[F]_s.+1 -> bool := posdefcheck.

(** *** Proofs *)

Require Import bigop_tactics.

Lemma posdefcheck_correct s Q :
  @posdefcheck_ssr s Q ->
  posdef (cholesky.MF2R (cholesky_infnan.MFI2F Q)).
Proof.
rewrite /posdefcheck_ssr /posdefcheck.
apply posdef_check_correct.
Qed.

End theory_posdef_check.

Local Notation fs := coqinterval_infnan.coqinterval_round_up_infnan (only parsing).

(** *** The main tactic. *)

Section posdef_check_eff_wrapup.

Variable fs : Float_round_up_infnan_spec.
Variable F2FI : F.type -> FIS fs.
Hypothesis F2FI_correct : forall f : F.type,
  finite (F2FI f) -> FIS2FS (F2FI f) = proj_val (F.toX f) :> R.

Definition posdefcheck_eff_wrapup (Q : seq (seq (s_float bigZ bigZ))) :=
  let s := size Q in
  let s' := s.-1 in
  let Q := map (map F2FI) Q in
  [&&
   s != 0%N,
   size Q == s,
   all (fun e => size e == s) Q &
   posdefcheck_eff
     (s := s')
     (fs := fs)
     Q].

Definition posdef_seqF (mat : seq (seq F.type)) : Prop :=
  let m := seq.size mat in
  posdef (spec_seqmx (H0 := id) m m (map (map toR) mat)).

Theorem posdefcheck_eff_wrapup_correct Q :
  @posdefcheck_eff_wrapup Q -> posdef_seqF Q.
Proof.
rewrite /posdefcheck_eff_wrapup.
set s := size Q.
set s' := s.-1.
set Q' := map (map F2FI) Q.
pose Qb := @spec_seqmx _ (FIS0 fs) _ (id) (s'.+1) (s'.+1) Q'.
case/and4P => Hs HQ'1 HQ'2 Hposdef.
have Hs' : s'.+1 = s by rewrite prednK => [//| ]; rewrite lt0n.
rewrite /posdef_seqF.
set Q'' := spec_seqmx _ _ _.
have Hpos : posdefcheck_ssr Qb.
{ move: Hposdef; apply etrans.
  apply refines_eq, refines_bool_eq.
  refines_apply1; rewrite refinesE.
  eapply Rseqmx_spec_seqmx. (* EMD: should be inferred? *)
  apply/andP; split.
  { by rewrite (eqP HQ'1) Hs'. }
  { by rewrite Hs'. } }
have HQb : posdef (cholesky.MF2R (cholesky_infnan.MFI2F Qb)).
{ by apply posdefcheck_correct with (Q0 := Qb). }
have Hfin := posdef_check_f1 Hpos.
have := HQb.
have HszQ : s'.+1 = size Q by rewrite Hs'.
suff->: Q'' = castmx (HszQ, HszQ) (cholesky.MF2R (cholesky_infnan.MFI2F Qb)).
{ rewrite /posdef.
  intros Hforall v Hv i j.
  move/(_ (castmx (esym HszQ, erefl 1%N) v)) in Hforall.
  have Hv' : castmx (esym HszQ, erefl 1%N) v <> 0%R.
  { move/matrixP in Hv.
    move/matrixP => Kv'.
    apply Hv => k l.
    move/(_ (cast_ord (esym HszQ) k) l) in Kv'.
    rewrite castmxE /= !(cast_ord_id, cast_ord_comp) in Kv'.
    by rewrite Kv' !mxE. }
  move/(_ Hv' i j): Hforall.
  congr Rlt; rewrite !mxE.
  set h := (fun j : 'I_(size Q) => cast_ord (esym HszQ) j).
  have hBij : {on [pred _ | true], bijective h}.
  { exists (fun i : 'I_(s'.+1) => cast_ord HszQ i).
    { by move=> k _; rewrite cast_ord_comp cast_ord_id. }
    { by move=> k _; rewrite /h cast_ord_comp cast_ord_id. } }
  rewrite (reindex h hBij).
  apply eq_bigr => k Hk.
  rewrite /h !(castmxE, cast_ord_comp, cast_ord_id, mxE).
  congr Rmult.
  rewrite (reindex h hBij).
  apply eq_bigr => l Hl.
  by rewrite /h !(castmxE, cast_ord_comp, cast_ord_id, mxE). }
apply/matrixP => i j; rewrite !(mxE, castmxE) /= /map_seqmx /Q'.
have HQ': size Q' = size Q by rewrite size_map.
have Hrow : forall i : 'I_(size Q), (size (nth [::] Q i) = size Q)%N.
{ move=> k.
  move/(all_nthP [::])/(_ k): HQ'2.
  rewrite -(eqP HQ'1) HQ'.
  move/(_ (@ltn_ord _ k))/eqP; apply etrans.
  by rewrite /Q' (nth_map [::]) // size_map. }
rewrite (nth_map ([::] : seq R)); last by rewrite size_map.
rewrite (nth_map R0);
  last by rewrite (nth_map ([::] : seq F.type)) // size_map Hrow.
rewrite (nth_map ([::] : seq F.type)) //.
rewrite (nth_map F.zero); last by rewrite Hrow.
rewrite (nth_map ([::] : seq (FIS fs))); last by rewrite size_map.
rewrite (nth_map (F2FI F.zero));
  last by rewrite (nth_map ([::] : seq F.type)) // size_map Hrow.
rewrite (nth_map ([::] : seq F.type)) //.
rewrite (nth_map F.zero); last by rewrite Hrow.
have HFin' : forall (i j : 'I_(size Q)),
  finite (F2FI (nth F.zero (nth [::] Q i) j)).
{ move=> k l.
  clear - Hfin HszQ HQ' Hrow.
  move/(_ (cast_ord (esym HszQ) k) (cast_ord (esym HszQ) l)): Hfin.
  rewrite /Qb /= mxE /map_seqmx /= (nth_map [::]) ?HQ'//.
  rewrite /Q' /= (nth_map [::]) ?HQ'//.
  rewrite (nth_map (F2FI F.zero)) ?size_map ?Hrow ?HQ'//.
  by rewrite (nth_map F.zero) ?Hrow ?HQ'. }
have H1 := HFin' i j.
have H2 := F2FI_correct H1.
by rewrite -H2.
Qed.

End posdef_check_eff_wrapup.

Lemma F2FI_correct' (f : F.type) :
  @finite coqinterval_infnan.coqinterval_round_up_infnan (F2FI f) ->
  FI2FS (F2FI f) = toR f :> R.
Proof. by apply F2FI_correct. Qed.

Ltac posdef_check :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (posdefcheck_eff_wrapup_correct F2FI_correct');
      vm_cast_no_check (erefl true))
  end.

(* This code generate an anomaly :
Require matrices.
Eval vm_compute in posdef_check matrices.m4. *)

From Bignums Require Import BigZ BigN.
Require Import Int63.
Require Import Float.
Require Import Bool.
Require Import primitive_floats_infnan.

Definition BigZ2int63 (n : BigZ.t_) : option (bool * Int63.int) :=
  match n with
  | BigZ.Pos (BigN.N0 n) => Some (false, n)
  | BigZ.Neg (BigN.N0 n) => Some (true, n)
  | _ => None
  end.

Lemma BigZ2int63_correct n :
  match BigZ2int63 n with
  | None => True
  | Some (false, n') => to_Z n' = BigZ.to_Z n
  | Some (true, n') => Z.opp (to_Z n') = BigZ.to_Z n
  end.
Proof.
  unfold BigZ2int63.
  destruct n, t ; auto.
Qed.

Lemma Bir_mantissa_sign_correct n :
  match BigZ2int63 n with
  | None => True
  | Some (sn, n') =>
    if (n' == 0)%int63 then Bir.mantissa_sign n = Interval_specific_sig.Mzero
    else Bir.mantissa_sign n = Interval_specific_sig.Mnumber sn (BigN.N0 n')
  end.
Proof.
  unfold BigZ2int63.
  destruct n, t; auto;
    case_eq (t == 0)%int63;
    intro Ht.
  - apply eqb_correct in Ht.
    now rewrite Ht.
  - apply eqb_false_correct in Ht.
    unfold Bir.mantissa_sign.
    rewrite ifF.
    + reflexivity.
    + apply not_true_is_false.
      intro H.
      apply Ht.
      cbv in H.
      revert H.
      case_eq (t ?= 0)%int63 ; try discriminate.
      rewrite compare_spec.
      rewrite Z.compare_eq_iff.
      intros H _.
      now apply to_Z_inj.
  - apply eqb_correct in Ht.
    now rewrite Ht.
  - apply eqb_false_correct in Ht.
    unfold Bir.mantissa_sign.
    rewrite ifF.
    + reflexivity.
    + apply not_true_is_false.
      intro H.
      apply Ht.
      cbv in H.
      revert H.
      case_eq (0 ?= t)%int63; try discriminate.
      * rewrite compare_spec.
        rewrite Z.compare_eq_iff.
        intros H _.
        now apply to_Z_inj.
      * rewrite compare_spec.
        rewrite Z.compare_gt_iff.
        intro Hl.
        exfalso.
        revert Hl.
        apply Zle_not_lt.
        change (Int63.to_Z 0) with Z0.
        apply to_Z_bounded.
Qed.

Definition canonical_mantissaPrim (m : int) (se : bool) (e : int) :=
  (~~se || (e <= 1074)%int63)  (* emin <= e *)
  && (m < 9007199254740992 (*2^53*))%int63
  && (se && (1074 (*-emin*) <= e)%int63
      || (4503599627370496 (*2^52*) <= m)%int63).

Lemma canonical_mantissaPrim_correct m se e :
  match [| m |]%int63 with
  | Z0 => True
  | Z.pos mp =>
    let ez := if se then (- [| e |]%int63)%Z else [| e |]%int63 in
    canonical_mantissaPrim m se e -> Binary.canonical_mantissa prec emax mp ez
  | Z.neg _ => False
  end.
Proof.
case_eq (to_Z m) => [ |mp|mp] Hm; [exact I| | ].
{ rewrite /canonical_mantissaPrim => /andP [] /andP [He Hubm] /orP Hlbm.
  set ez := if se then _ else _.
  have Hlbez : (emin <= ez)%Z.
  { rewrite /ez; move: He; case se => /=.
    { rewrite /emin /emax /prec /= => He.
      rewrite -Pos2Z.opp_pos -Z.opp_le_mono.
      by move: He; rewrite /is_true leb_spec. }
    move=> _; apply (Z.le_trans _ 0) => //; apply to_Z_bounded. }
  have Hubmp : IZR (Z.pos mp) < bpow radix2 prec.
  { move: Hubm; rewrite /is_true ltb_spec Hm /prec /= => Hmp.
    by apply IZR_lt. }
  have Hubmp' : (mag radix2 (IZR (Z.pos mp)) <= prec)%Z.
  { by apply mag_le_bpow => //; rewrite Rabs_pos_eq => //; apply IZR_le. }
  have Hlbmp : ez = emin \/ (bpow radix2 (prec - 1) <= IZR (Z.pos mp)).
  { move: Hlbm => [] Hlbm; [left|right].
    { apply Z.le_antisymm => //; rewrite /ez; move: Hlbm; case se => //= He'.
      rewrite /emin /emax /prec /= -Pos2Z.opp_pos -Z.opp_le_mono.
      by move: He'; rewrite /is_true leb_spec. }
    move: Hlbm; rewrite /is_true leb_spec Hm => Hlbm.
    by rewrite /prec /=; apply IZR_le. }
  rewrite /Binary.canonical_mantissa /fexp /FLT_exp -/emin; apply Zeq_bool_true.
  rewrite Digits.Zpos_digits2_pos Zdigits_mag //.
  case Hlbmp.
  { move=> ->; rewrite Z.max_r //; lia. }
  move=> Hlbmp'.
  have -> : mag radix2 (IZR (Z.pos mp)) = prec :> BinNums.Z.
  { by apply mag_unique; rewrite Rabs_pos_eq; [ |apply IZR_le]. }
  rewrite Z.max_l; lia. }
move: (to_Z_bounded m); lia.
Qed.

Definition boundedPrim (m : int) (se : bool) (e : int) :=
  (se || (e <= 1024 - 53)%int63) && (canonical_mantissaPrim m se e).

Lemma boundedPrim_correct m se e :
  match [| m |]%int63 with
  | Z0 => True
  | Z.pos mp =>
    let ez := if se then (- [| e |]%int63)%Z else [| e |]%int63 in
    boundedPrim m se e -> Binary.bounded prec emax mp ez
  | Z.neg _ => False
  end.
Proof.
move: (canonical_mantissaPrim_correct m se e).
case_eq (to_Z m) => [//|mp Hmp /=|//].
set ez := if se then _ else _.
rewrite /boundedPrim /Binary.bounded => cmc /andP [] /orP He cm.
rewrite (cmc cm) /= /ez.
rewrite /is_true Z.leb_le; move: He; case se => He.
{ move: (to_Z_bounded e); lia. }
by case He => //; rewrite /is_true leb_spec.
Qed.

Definition BigZFloat2Prim (f : s_float BigZ.t_ BigZ.t_) :=
  match f with
  | Fnan => nan
  | Float m e =>
    match (BigZ2int63 m, BigZ2int63 e) with
    | (Some (sm', m'), Some (se', e')) =>
      if (m' == 0)%int63 then zero else
        if boundedPrim m' se' e' then
          let f := of_int63 m' in
          let f := if sm' then (-f)%float else f in
          let e'' := if se' then (shift - e')%int63 else (shift + e')%int63 in
          ldshiftexp f e''
        else nan
    | _ => nan
    end
  end.

Require Import Flocq.IEEE754.Binary Flocq.Core.Digits.
Require Import FlocqSpecLayer FlocqNativeLayer.

(* TODO: move *)
Lemma FF2R_SF2FF_B2SF prec emax nan (f : binary_float prec emax) :
  FF2R radix2 (SF2FF nan (B2SF f)) = B2R prec emax f.
Proof. now revert nan f; intros (nan_s, nan_pl) [s|s|s pl Hpl|s m e Hme]. Qed.

(* TODO: move *)
Lemma is_finite_FF_SF2FF_B2SF prec emax nan (f : binary_float prec emax) :
  is_finite_FF (SF2FF nan (B2SF f)) = is_finite prec emax f.
Proof. now revert nan f; intros (nan_s, nan_pl) [s|s|s pl Hpl|s m e Hme]. Qed.

Lemma B2R_Prim2B_B2Prim nan x :
  B2R prec emax (Prim2B nan (B2Prim x)) = B2R prec emax x.
Proof.
case_eq (is_nan prec emax x); [ |now intro H; rewrite Prim2B_B2Prim_notnan].
revert x; intros [s|s|s pl Hpl|s m e Hme]; try discriminate; intros _.
unfold Prim2B, B2Prim, Prim2SF, SF2FF; simpl.
now rewrite B2R_FF2B; case (sval nan).
Qed.

Lemma of_int63_exact m :
  (Zdigits radix2 [| m |]%int63 <= prec)%Z ->
  B2R prec emax (Prim2B primitive_floats_infnan.nan_pl (of_int63 m))
  = IZR [| m |]%int63.
Proof.
  intros Hm.
assert (Hprec0 : (0 < prec)%Z); [now simpl| ].
assert (Hprec : (prec < emax)%Z); [now simpl| ].
rewrite -(FF2R_SF2FF_B2SF (sval primitive_floats_infnan.nan_pl)) B2SF_Prim2B.
rewrite of_int63_spec binary_normalize_equiv FF2R_SF2FF_B2SF.
pose (bm := binary_normalize prec emax (zpos_gt_0 53) Hprec mode_NE (to_Z m)
                             0 false).
assert (Hb := binary_normalize_correct _ _ _ Hprec mode_NE (to_Z m) 0 false).
pose (r := F2R ({| Fnum := to_Z m; Fexp := 0 |} : Defs.float radix2)).
assert (Hr : Generic_fmt.round radix2 (fexp prec emax) ZnearestE r = r).
{ case (Z.eq_dec [| m |]%int63 0); intro Hmz.
  { now unfold r, F2R; rewrite Hmz; simpl; rewrite Rmult_0_l round_0. }
  apply round_generic; [now apply valid_rnd_N| ].
  apply generic_format_F2R; intros _; unfold F2R; simpl; rewrite Rmult_1_r.
  unfold cexp, fexp, FLT_exp; apply Z.max_lub; [ |unfold emin, emax; lia].
  rewrite -Zdigits_mag; lia. }
revert Hb; rewrite Hr ifT.
{ now intros (Hr', _); rewrite Hr'; unfold r, F2R; simpl; rewrite Rmult_1_r. }
apply Rlt_bool_true; unfold r, F2R; simpl; rewrite Rmult_1_r.
change (IZR (Z.pow_pos 2 _)) with (bpow radix2 1024).
case (Z.eq_dec [| m |]%int63 0); intro Hmz.
{ rewrite Hmz Rabs_R0; apply bpow_gt_0. }
apply (Rlt_le_trans _ _ _ (bpow_mag_gt radix2 _)), bpow_le.
rewrite -Zdigits_mag; unfold prec in Hm; lia.
Qed.

Lemma BigZFloat2Prim_correct (f : F.type) :
  is_true (FloatValues.is_finite (BigZFloat2Prim f)) ->
  FI2FS (BigZFloat2Prim f) = proj_val (F.toX f) :> R.
Proof.
case f; [now cbn|intros m e; clear f].
unfold BigZFloat2Prim, F.toX, FtoX, F.toF.
assert (Hm := Bir_mantissa_sign_correct m).
assert (He := BigZ2int63_correct e).
revert Hm He.
destruct (BigZ2int63 m) as [(sm, m')|p]; [ |discriminate];
  destruct (BigZ2int63 e) as [(se, e')|p']; [ |discriminate].
case eqbP; intro Hm'.
{ intros Hm _ _; rewrite Hm; simpl.
  now unfold Prim2B; rewrite B2R_FF2B; cbv. }
intros Hm He; rewrite Hm; unfold Bir.EtoZ.
set (m'' := if sm then _ else _).
set (e'' := if se then (_ - _)%int63 else _).
move: (boundedPrim_correct m' se e').
case_eq (to_Z m');
  [now auto |intros m'p Hm'p|
   now replace (FloatValues.is_finite nan) with false by now cbv].
case (boundedPrim _ _ _);
  [ |now replace (FloatValues.is_finite nan) with false by now cbv].
assert (He' : [e]%bigZ = if se then (- to_Z e')%Z else to_Z e').
{ now revert He; case se. }
rewrite He'; clear He' He e.
set (e := if se then _ else _).
simpl; intro Hb; specialize (Hb (refl_equal _)).
rewrite <-(B2Prim_Prim2B primitive_floats_infnan.nan_pl (ldshiftexp _ _)) at 1.
rewrite is_finite_spec; simpl.
unfold Prim2B; rewrite B2R_FF2B is_finite_FF2B.
rewrite ldshiftexp_spec.
rewrite <-(B2SF_Prim2B primitive_floats_infnan.nan_pl m'').
assert (Hprec : (prec < emax)%Z); [now simpl| ].
rewrite SFldexp_Bldexp.
set (f := _ primitive_floats_infnan.nan_pl m'').
set (e''' := Z.sub (to_Z e'') _).
assert (H := Bldexp_correct _ _ _ Hprec Binary.mode_NE f e''').
revert H.
case Rlt_bool_spec; intro Hlt; [ |now case (Bldexp _ _ _ _ _ _ _)].
set (bf := Bldexp _ _ _ _ _ _ _).
intros (Ht, (Hfe''', Hs)).
rewrite FF2R_SF2FF_B2SF Ht.
rewrite is_finite_FF_SF2FF_B2SF Hfe'''; intro Hf.
unfold FtoR.
set (m''' := if sm then _ else _).
assert (Hm''' : B2R prec emax f = IZR m''').
{ unfold f, m'', m''', Bir.MtoP, BigN.to_Z.
  unfold CyclicAxioms.ZnZ.to_Z, Cyclic63.Int63Cyclic.ops, Cyclic63.int_ops.
  assert (Hdig_m'p : Z.le (Zdigits radix2 (Z.pos m'p)) prec).
  { revert Hb; unfold bounded, canonical_mantissa.
    move/andP => [Heq _]; apply Zeq_bool_eq in Heq; revert Heq.
    unfold FLT_exp; rewrite Zpos_digits2_pos; lia. }
  case sm.
  { rewrite <-(B2Prim_Prim2B primitive_floats_infnan.nan_pl (of_int63 m')).
    rewrite (FPopp_Bopp (fun _ => ex_nan)).
    now rewrite B2R_Prim2B_B2Prim B2R_Bopp of_int63_exact Hm'p. }
  now rewrite of_int63_exact Hm'p. }
rewrite Hm'''; unfold m''', e''', Bir.MtoP, BigN.to_Z.
unfold CyclicAxioms.ZnZ.to_Z, Cyclic63.Int63Cyclic.ops, Cyclic63.int_ops.
rewrite Hm'p.  
clear m''' Hm'''; set (m''' := if sm then _ else _).
assert (He''shift : Z.sub (to_Z e'') (to_Z shift) = e).
{ assert (He' : (to_Z e' <= -emin)%Z).
  { revert Hb; unfold e; case se.
    { rewrite -{2}(Z.opp_involutive (to_Z e')) -Z.opp_le_mono.
      unfold bounded, canonical_mantissa.
      move=> /andP [] /Zeq_bool_eq; unfold FLT_exp, emin, emax, prec; lia. }
    rewrite /SpecFloat.bounded => /andP [] _ /Zle_bool_imp_le.
    unfold emin, emax, prec; lia. }
  unfold e'', e; case se.
  { rewrite sub_spec Zmod_small; [ring|split].
    { rewrite shift_value; revert He'; unfold emin, emax, prec; lia. }
    apply (Z.le_lt_trans _ (to_Z shift)); [ |now simpl].
    assert (H := to_Z_bounded e'); lia. }
  rewrite add_spec Zmod_small; [ring|split].
  { assert (H := conj (to_Z_bounded shift) (to_Z_bounded e')); lia. }
  apply (Z.le_lt_trans _ (4 * emax)); [ |now simpl].
  rewrite shift_value; revert He'; unfold emin, emax, prec; lia. }
rewrite He''shift.
rewrite round_generic.
{ now case e; [rewrite Rmult_1_r|intro p; rewrite mult_IZR|simpl]. }
apply generic_format_F2R; fold m''' e; intros Nzm'''.
unfold cexp, FLT_exp; rewrite (mag_F2R_Zdigits _ _ _ Nzm''').
revert Hb; unfold SpecFloat.bounded, SpecFloat.canonical_mantissa.
move=> /andP [] /Zeq_bool_eq; rewrite -/emin /FLT_exp Zpos_digits2_pos => Hb _.
now unfold m'''; case sm; rewrite Hb.
Qed.

Ltac primitive_posdef_check :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (@posdefcheck_eff_wrapup_correct primitive_float_round_up_infnan _ BigZFloat2Prim_correct);
      vm_cast_no_check (erefl true))
  end.

(*Goal posdef_seqF matrices.m12.
Time posdef_check.
Undo.
Time primitive_posdef_check.
Qed.*)
