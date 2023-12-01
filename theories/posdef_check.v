(* (setq coq-prog-name "~/forge/git/validsdp/coq/bin/coqtop") *)
(** * Main tactic for multivariate polynomial positivity. *)

Require Import ZArith.
From Flocq Require Import Core. Require Import Datatypes.
From Interval Require Import Float.Basic Real.Xreal.
From Interval Require Import Missing.Stdlib.
From Interval Require Import Float.Specific_ops. (* for Float *)
From CoqEAL.theory Require Import ssrcomplements.
From CoqEAL.refinements Require Import hrel refinements param seqmx seqmx_complements binnat binint rational binrat.
Require Import Reals Flocq.Core.Raux QArith Psatz FSetAVL.
From Bignums Require Import BigZ BigQ.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype tuple matrix ssralg bigop.
From mathcomp Require Import ssrnum ssrint rat div.
Require Import mathcomp.analysis.Rstruct.
Require Import iteri_ord libValidSDP.float_infnan_spec libValidSDP.real_matrix.
Import Refinements.Op.
Require Import cholesky_prog libValidSDP.coqinterval_infnan.

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

Context {fs : Float_round_up_infnan_spec} (eta_neq_0 : eta fs <> 0).
Let F := FIS fs.

Definition posdefcheck_ssr (s : nat) : 'M[F]_s.+1 -> bool := posdefcheck.

(** *** Proofs *)

Lemma posdefcheck_correct s Q :
  @posdefcheck_ssr s Q ->
  posdef (cholesky.MF2R (cholesky_infnan.MFI2F Q)).
Proof.
rewrite /posdefcheck_ssr /posdefcheck.
apply posdef_check_correct, eta_neq_0.
Qed.

End theory_posdef_check.

Local Notation fs := coqinterval_infnan.coqinterval_round_up_infnan (only parsing).

(** *** The main tactic. *)

Section posdef_check_eff_wrapup.

Variable fs : Float_round_up_infnan_spec.
Hypothesis eta_neq_0 : eta fs <> 0.
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
{ by (try (apply posdefcheck_correct with (Q0 := Qb))
      || apply posdefcheck_correct with (Q := Qb)). }
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

Lemma eta_float_round_up_infnan_neq_0 :
  eta coqinterval_infnan.coqinterval_round_up_infnan <> 0.
Proof. compute; lra. Qed.

(* We use the typical Coq design pattern "abstract + vm_cast_no_check"
   to avoid performing the conversion check twice. *)
Ltac posdef_check :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (@posdefcheck_eff_wrapup_correct _ eta_float_round_up_infnan_neq_0 _ F2FI_correct');
      vm_cast_no_check (erefl true))
  end.

Ltac posdef_check_native :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (@posdefcheck_eff_wrapup_correct _ eta_float_round_up_infnan_neq_0 _ F2FI_correct');
      native_cast_no_check (erefl true))
  end.

Goal posdef_seqF
  [:: [:: Float (4844268357668941) (-51); Float (-6010289013563096) (-55); Float (-8527459789388090) (-59); Float (-4778266098206664) (-50); Float (5667663619731675) (-55);
          Float (4683274154211911) (-51)];
      [:: Float (-6010289013563096) (-55); Float (7396430339592472) (-51); Float (-7289940589024767) (-57); Float (-6805625889340557) (-58); Float (-6772467775663301) (-51);
          Float (5856798786847734) (-55)];
      [:: Float (-8527459789388090) (-59); Float (-7289940589024767) (-57); Float (4853298392673210) (-52); Float (-6022680283661423) (-56); Float (-6234500978567578) (-55);
          Float (7135901130999799) (-56)];
      [:: Float (-4778266098206664) (-50); Float (-6805625889340557) (-58); Float (-6022680283661423) (-56); Float (4783306079007354) (-49); Float (5238162149477632) (-57);
          Float (-4748548273910727) (-50)];
      [:: Float (5667663619731675) (-55); Float (-6772467775663301) (-51); Float (-6234500978567578) (-55); Float (5238162149477632) (-57); Float (6311840486445046) (-51);
          Float (-6079338910151020) (-55)];
      [:: Float (4683274154211911) (-51); Float (5856798786847734) (-55); Float (7135901130999799) (-56); Float (-4748548273910727) (-50); Float (-6079338910151020) (-55);
          Float (4765808075135984) (-51)]]%bigZ.
Time posdef_check.
Qed.

From Bignums Require Import BigZ BigN.
Require Import Uint63.
Require Import Floats.
Require Import Bool.
Require Import libValidSDP.primitive_floats_infnan.

Definition BigZ2int63 (n : BigZ.t_) : option (bool * Uint63.int) :=
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
    if Uint63.eqb n' 0%int63 then Bir.mantissa_sign n = Specific_sig.Mzero
    else Bir.mantissa_sign n = Specific_sig.Mnumber sn (BigN.N0 n')
  end.
Proof.
  unfold BigZ2int63.
  destruct n, t; auto;
    case_eq (Uint63.eqb t 0%int63);
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
      vm_compute in H.
      revert H.
      case_eq (t ?= 0)%uint63 ; try discriminate.
      rewrite Uint63.compare_spec.
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
      vm_compute in H.
      revert H.
      case_eq (0 ?= t)%uint63; try discriminate.
      * rewrite Uint63.compare_spec.
        rewrite Z.compare_eq_iff.
        intros H _.
        now apply to_Z_inj.
      * rewrite Uint63.compare_spec.
        rewrite Z.compare_gt_iff.
        intro Hl.
        exfalso.
        revert Hl.
        apply Zle_not_lt.
        change (Uint63.to_Z 0) with Z0.
        apply to_Z_bounded.
Qed.

Definition canonical_mantissaPrim (m : int) (se : bool) (e : int) :=
  (~~se || Uint63.leb e 1074)%int63  (* emin <= e *)
  && (Uint63.ltb m 9007199254740992 (*2^53*))%int63
  && (se && (Uint63.leb 1074 (*-emin*) e)%int63
      || (Uint63.leb 4503599627370496 (*2^52*) m)%int63).

Lemma canonical_mantissaPrim_correct m se e :
  match Uint63.to_Z m with
  | Z0 => True
  | Z.pos mp =>
    let ez := if se then Z.opp (Uint63.to_Z e) else Uint63.to_Z e in
    canonical_mantissaPrim m se e -> canonical_mantissa prec emax mp ez
  | Z.neg _ => False
  end.
Proof.
case_eq (to_Z m) => [ |mp|mp] Hm; [exact I| | ].
{ rewrite /canonical_mantissaPrim => /andP [] /andP [He Hubm] /orP Hlbm.
  set ez := if se then _ else _.
  have Hlbez : (Z.le emin ez).
  { rewrite /ez; move: He; case se => /=.
    { rewrite /emin /emax /prec /= => He.
      rewrite -Pos2Z.opp_pos -Z.opp_le_mono.
      by move: He; rewrite /is_true Uint63.leb_spec. }
    move=> _; apply (Z.le_trans _ 0) => //; apply to_Z_bounded. }
  have Hubmp : IZR (Z.pos mp) < bpow radix2 prec.
  { move: Hubm; rewrite /is_true Uint63.ltb_spec Hm /prec /= => Hmp.
    by apply IZR_lt. }
  have Hubmp' : (Z.le (mag radix2 (IZR (Z.pos mp))) prec).
  { by apply mag_le_bpow => //; rewrite Rabs_pos_eq => //; apply IZR_le. }
  have Hlbmp : ez = emin \/ (bpow radix2 (prec - 1) <= IZR (Z.pos mp)).
  { move: Hlbm => [] Hlbm; [left|right].
    { apply Z.le_antisymm => //; rewrite /ez; move: Hlbm; case se => //= He'.
      rewrite /emin /emax /prec /= -Pos2Z.opp_pos -Z.opp_le_mono.
      by move: He'; rewrite /is_true Uint63.leb_spec. }
    move: Hlbm; rewrite /is_true Uint63.leb_spec Hm => Hlbm.
    by rewrite /prec /=; apply IZR_le. }
  rewrite /canonical_mantissa /fexp /FLT_exp -/emin; apply Zeq_bool_true.
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
  (se || (Uint63.leb e (1024 - 53))%int63) && (canonical_mantissaPrim m se e).

Lemma boundedPrim_correct m se e :
  match Uint63.to_Z m with
  | Z0 => True
  | Z.pos mp =>
    let ez := if se then Z.opp (Uint63.to_Z e) else Uint63.to_Z e in
    boundedPrim m se e -> bounded prec emax mp ez
  | Z.neg _ => False
  end.
Proof.
move: (canonical_mantissaPrim_correct m se e).
case_eq (to_Z m) => [//|mp Hmp /=|//].
set ez := if se then _ else _.
rewrite /boundedPrim /bounded => cmc /andP [] /orP He cm.
rewrite (cmc cm) /= /ez.
rewrite /is_true Z.leb_le; move: He; case se => He.
{ move: (to_Z_bounded e); lia. }
by case He => //; rewrite /is_true Uint63.leb_spec.
Qed.

Definition BigZFloat2Prim (f : s_float BigZ.t_ BigZ.t_) :=
  match f with
  | Fnan => nan
  | Float m e =>
    match (BigZ2int63 m, BigZ2int63 e) with
    | (Some (sm', m'), Some (se', e')) =>
      if (Uint63.eqb m' 0)%int63 then zero else
        if boundedPrim m' se' e' then
          let f := of_uint63 m' in
          let f := if sm' then (-f)%float else f in
          let e'' := if se' then (Uint63.of_Z shift - e')%uint63 else (Uint63.of_Z shift + e')%uint63 in
          ldshiftexp f e''
        else nan
    | _ => nan
    end
  end.

Require Import Flocq.IEEE754.BinarySingleNaN Flocq.Core.Digits.
Require Import Flocq.IEEE754.PrimFloat.
Module Z := FloatOps.Z. (* workaround *)

(* TODO: move *)
Lemma FF2R_SF2FF_B2SF prec emax (f : binary_float prec emax) :
  SF2R radix2 (B2SF f) = B2R f.
Proof. now revert f; intros [s|s| |s m e Hme]. Qed.

(* TODO: move *)
Lemma is_finite_FF_SF2FF_B2SF prec emax (f : binary_float prec emax) :
  is_finite_SF (B2SF f) = is_finite f.
Proof. now revert f; intros [s|s| |s m e Hme]. Qed.

Lemma B2R_Prim2B_B2Prim x : B2R (Prim2B (B2Prim x)) = B2R x.
Proof.
case_eq (is_nan x); [ |now intro H; rewrite Prim2B_B2Prim].
revert x; intros [s|s| |s m e Hme]; try discriminate; intros _.
now unfold Prim2B, B2Prim, Prim2SF; simpl.
Qed.

Lemma of_int63_exact m :
  Z.le (Zdigits radix2 (Uint63.to_Z m)) prec ->
  B2R (Prim2B (of_uint63 m))
  = IZR (Uint63.to_Z m).
Proof.
intros Hm.
assert (Hprec0 : Z.lt 0 prec); [now simpl| ].
assert (Hprec : Z.lt prec emax); [now simpl| ].
rewrite -(FF2R_SF2FF_B2SF) B2SF_Prim2B.
rewrite of_uint63_spec binary_normalize_equiv FF2R_SF2FF_B2SF.
pose (bm := binary_normalize _ _ Hprec0 Hprec mode_NE (to_Z m)
                             0 false).
assert (Hb := binary_normalize_correct _ _ PrimFloat.Hprec Hmax mode_NE (to_Z m) 0 false).
pose (r := F2R ({| Fnum := to_Z m; Fexp := 0 |} : Defs.float radix2)).
assert (Hr : Generic_fmt.round radix2 (fexp prec emax) ZnearestE r = r).
{ case (Z.eq_dec (Uint63.to_Z m) 0); intro Hmz.
  { now unfold r, F2R; rewrite Hmz; simpl; rewrite Rmult_0_l round_0. }
  apply round_generic; [now apply valid_rnd_N| ].
  apply generic_format_F2R; intros _; unfold F2R; simpl; rewrite Rmult_1_r.
  unfold cexp, fexp, FLT_exp; apply Z.max_lub; [ |unfold emin, emax; lia].
  rewrite -Zdigits_mag; lia. }
revert Hb; simpl; rewrite Hr ifT.
{ now intros (Hr', _); rewrite Hr'; unfold r, F2R; simpl; rewrite Rmult_1_r. }
apply Rlt_bool_true; unfold r, F2R; simpl; rewrite Rmult_1_r.
change (IZR (Z.pow_pos 2 _)) with (bpow radix2 1024).
case (Z.eq_dec (Uint63.to_Z m) 0); intro Hmz.
{ rewrite Hmz Rabs_R0; apply bpow_gt_0. }
apply (Rlt_le_trans _ _ _ (bpow_mag_gt radix2 _)), bpow_le.
rewrite -Zdigits_mag; unfold prec in Hm; lia.
Qed.

Lemma BigZFloat2Prim_correct (f : F.type) :
  is_true (PrimFloat.is_finite (BigZFloat2Prim f)) ->
  FI2FS (BigZFloat2Prim f) = proj_val (F.toX f) :> R.
Proof.
case f; [now cbn|intros m e; clear f].
unfold BigZFloat2Prim, F.toX, FtoX, F.toF.
assert (Hm := Bir_mantissa_sign_correct m).
assert (He := BigZ2int63_correct e).
revert Hm He.
destruct (BigZ2int63 m) as [(sm, m')|]; [ |discriminate];
  destruct (BigZ2int63 e) as [(se, e')|]; [ |discriminate].
case eqbP; intro Hm'.
{ now intros Hm _ _; rewrite Hm; simpl. }
intros Hm He; rewrite Hm; unfold Bir.EtoZ.
set (m'' := if sm then _ else _).
set (e'' := if se then (_ - _)%uint63 else _).
move: (boundedPrim_correct m' se e').
case_eq (to_Z m');
  [now auto |intros m'p Hm'p|
   now replace (PrimFloat.is_finite nan) with false by now cbv].
case (boundedPrim _ _ _);
  [ |now replace (PrimFloat.is_finite nan) with false by now cbv].
assert (He' : BigZ.to_Z e = if se then Z.opp (to_Z e') else to_Z e').
{ now revert He; case se. }
rewrite He'; clear He' He e.
set (e := if se then _ else _).
simpl; intro Hb; specialize (Hb (refl_equal _)).
rewrite <-(B2Prim_Prim2B (ldshiftexp _ _)) at 1.
rewrite is_finite_equiv; simpl.
unfold Prim2B; rewrite B2R_SF2B is_finite_SF2B.
rewrite Prim2SF_B2Prim B2SF_SF2B.
rewrite ldshiftexp_spec.
rewrite <-(B2SF_Prim2B m'').
assert (Hprec : Z.lt prec emax); [now simpl| ].
rewrite B2SF_Prim2B.
rewrite -ldexp_spec.
rewrite -B2SF_Prim2B ldexp_equiv.
rewrite is_finite_SF_B2SF.
rewrite SF2R_B2SF.
set (f := Prim2B m'').
set (e''' := Z.sub (to_Z e'') _).
assert (H := Bldexp_correct _ _ PrimFloat.Hprec Hmax BinarySingleNaN.mode_NE f e''').
revert H.
case Rlt_bool_spec; intro Hlt; [ |now case Bldexp].
set (bf := Bldexp _ _ _).
intros (Ht, (Hfe''', Hs)).
rewrite Ht Hfe'''.
intro Hf.
unfold FtoR.
set (m''' := if sm then _ else _).
assert (Hm''' : B2R f = IZR m''').
{ unfold f, m'', m''', Bir.MtoP, BigN.to_Z.
  unfold CyclicAxioms.ZnZ.to_Z, Cyclic63.Uint63Cyclic.ops, Cyclic63.int_ops.
  assert (Hdig_m'p : Z.le (Zdigits radix2 (Z.pos m'p)) prec).
  { revert Hb; unfold bounded, canonical_mantissa.
    move/andP => [Heq _]; apply Zeq_bool_eq in Heq; revert Heq.
    unfold fexp; rewrite Zpos_digits2_pos; lia. }
  case sm.
  { rewrite <-(B2Prim_Prim2B (of_uint63 m')).
    rewrite opp_equiv.
    now rewrite B2R_Bopp B2R_Prim2B_B2Prim of_int63_exact /= Hm'p. }
  now rewrite of_int63_exact /= Hm'p. }
rewrite Hm'''; unfold m''', e''', Bir.MtoP, BigN.to_Z.
unfold CyclicAxioms.ZnZ.to_Z, Cyclic63.Uint63Cyclic.ops, Cyclic63.int_ops.
rewrite /= Hm'p.
clear m''' Hm'''; set (m''' := if sm then _ else _).
assert (He''shift : Z.sub (to_Z e'') shift = e).
{ assert (He' : Z.le (to_Z e') (Z.opp emin)).
  { revert Hb; unfold e; case se.
    { rewrite -{2}(Z.opp_involutive (to_Z e')) -Z.opp_le_mono.
      unfold bounded, canonical_mantissa.
      move=> /andP [] /Zeq_bool_eq; unfold fexp, emin, emax, prec; lia. }
    rewrite /SpecFloat.bounded => /andP [] _ /Zle_bool_imp_le.
    unfold emin, emax, prec; lia. }
  unfold e'', e; case se.
  { rewrite Uint63.sub_spec Zmod_small; [ |split].
    { rewrite of_Z_spec Zmod_small; [ring|now compute]. }
    { rewrite of_Z_spec Zmod_small; [ |now compute].
      revert He'; unfold emin, emax, prec, shift; lia. }
    apply (Z.le_lt_trans _ shift); [ |now simpl].
    rewrite of_Z_spec Zmod_small; [ |now compute].
    assert (H := to_Z_bounded e'); lia. }
  rewrite Uint63.add_spec Zmod_small; [ |split].
  { rewrite of_Z_spec Zmod_small; [ring|now compute]. }
  { rewrite of_Z_spec Zmod_small; [ |now compute].
    rewrite /shift; assert (H := to_Z_bounded e'); lia. }
  apply (Z.le_lt_trans _ (4 * emax)); [ |now simpl].
  rewrite of_Z_spec Zmod_small; [ |now compute].
  rewrite /shift; revert He'; unfold emin, emax, prec; lia. }
rewrite He''shift.
rewrite round_generic.
{ now case e; [rewrite Rmult_1_r|intro p; rewrite mult_IZR|simpl]. }
apply generic_format_F2R; fold m''' e; intros Nzm'''.
unfold cexp, FLT_exp; rewrite (mag_F2R_Zdigits _ _ _ Nzm''').
revert Hb; unfold SpecFloat.bounded, SpecFloat.canonical_mantissa.
move=> /andP [] /Zeq_bool_eq; rewrite -/emin /FLT_exp Zpos_digits2_pos => Hb _.
unfold m'', m'''.
unfold SpecFloat.fexp.
now case sm; unfold fexp in Hb; rewrite Hb.
Qed.

Lemma eta_primitive_float_round_up_infnan_neq_0 :
  eta primitive_float_round_up_infnan <> 0.
Proof. compute; lra. Qed.

Ltac primitive_posdef_check :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (@posdefcheck_eff_wrapup_correct _ eta_primitive_float_round_up_infnan_neq_0 _ BigZFloat2Prim_correct);
      vm_cast_no_check (erefl true))
  end.

Ltac primitive_posdef_check_native :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply (@posdefcheck_eff_wrapup_correct _ eta_primitive_float_round_up_infnan_neq_0 _ BigZFloat2Prim_correct);
      native_cast_no_check (erefl true))
  end.

Goal posdef_seqF
  [:: [:: Float (4844268357668941) (-51); Float (-6010289013563096) (-55); Float (-8527459789388090) (-59); Float (-4778266098206664) (-50); Float (5667663619731675) (-55);
          Float (4683274154211911) (-51)];
      [:: Float (-6010289013563096) (-55); Float (7396430339592472) (-51); Float (-7289940589024767) (-57); Float (-6805625889340557) (-58); Float (-6772467775663301) (-51);
          Float (5856798786847734) (-55)];
      [:: Float (-8527459789388090) (-59); Float (-7289940589024767) (-57); Float (4853298392673210) (-52); Float (-6022680283661423) (-56); Float (-6234500978567578) (-55);
          Float (7135901130999799) (-56)];
      [:: Float (-4778266098206664) (-50); Float (-6805625889340557) (-58); Float (-6022680283661423) (-56); Float (4783306079007354) (-49); Float (5238162149477632) (-57);
          Float (-4748548273910727) (-50)];
      [:: Float (5667663619731675) (-55); Float (-6772467775663301) (-51); Float (-6234500978567578) (-55); Float (5238162149477632) (-57); Float (6311840486445046) (-51);
          Float (-6079338910151020) (-55)];
      [:: Float (4683274154211911) (-51); Float (5856798786847734) (-55); Float (7135901130999799) (-56); Float (-4748548273910727) (-50); Float (-6079338910151020) (-55);
          Float (4765808075135984) (-51)]]%bigZ.
Time primitive_posdef_check.
Qed.
