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
From mathcomp Require Import ssrnum ssrint rat div.
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
Require Import Bool ZArith.
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

Definition BigZFloat2Prim (f : s_float BigZ.t_ BigZ.t_) :=
  match f with
  | Fnan => nan
  | Float m e =>
    match (BigZ2int63 m, BigZ2int63 e) with
    | (Some (sm, m), Some (se, e)) =>
      (* TODO: don't go through Z, do that in int63 *)
      match to_Z m with
      | Z0 => zero
      | Z.neg _ => nan  (* should never happen *)
      | Z.pos mp =>
        if (m == 0)%int63 then zero else
          if bounded prec emax mp (to_Z e) then
            let f := of_int63 m in
            let f := if sm then (-f)%float else f in
            let shexp := if se then (shift - e)%int63 else (shift + e)%int63 in
            ldshiftexp f shexp
          else nan
      end
    | _ => nan
    end
  end.

Require Import Flocq.IEEE754.Binary Flocq.Core.Digits.
Require Import Flocq_complements.
Require Import FlocqEmulatedLayer FlocqNativeLayer.

(* TODO: move *)
Lemma FF2R_EF2FF_B2EF prec emax nan (f : binary_float prec emax) :
  FF2R radix2 (EF2FF nan (B2EF f)) = B2R prec emax f.
Proof. now revert nan f; intros (nan_s, nan_pl) [s|s|s pl Hpl|s m e Hme]. Qed.

(* TODO: move *)
Lemma is_finite_FF_EF2FF_B2EF prec emax nan (f : binary_float prec emax) :
  is_finite_FF (EF2FF nan (B2EF f)) = is_finite prec emax f.
Proof. now revert nan f; intros (nan_s, nan_pl) [s|s|s pl Hpl|s m e Hme]. Qed.

Lemma BigZFloat2Prim_correct (f : F.type) :
  is_true (FloatValues.is_finite (BigZFloat2Prim f)) ->
  FI2FS (BigZFloat2Prim f) = proj_val (F.toX f) :> R.
Proof.
case f; [now cbn|intros m e; clear f].
unfold BigZFloat2Prim, F.toX, FtoX, F.toF.
assert (Hm := Bir_mantissa_sign_correct m).
assert (He := BigZ2int63_correct e).
revert Hm He.
destruct (BigZ2int63 m); destruct (BigZ2int63 e);
  [ |now destruct p|discriminate|discriminate].
destruct p as (sm, m').
destruct p0 as (se, e').
case eqbP; intro Hm'.
{ rewrite Hm' to_Z_0.
  intros Hm _ _; rewrite Hm; simpl.
  now unfold Prim2B; rewrite B2R_FF2B; cbv. }
intros Hm He; rewrite Hm; unfold Bir.EtoZ.
set (m'' := if sm then _ else _).
set (e'' := if se then (_ - _)%int63 else _).
case_eq (to_Z m');
  [now auto |intros m'p Hm'p|
   now replace (FloatValues.is_finite nan) with false by now cbv].
case_eq (EmulatedFloat.bounded prec emax m'p (to_Z e')); intro Hb;
  [ |now replace (FloatValues.is_finite nan) with false by now cbv].
rewrite <-(B2Prim_Prim2B primitive_floats_infnan.nan_pl (ldshiftexp _ _)) at 1.
rewrite is_finite_spec; simpl.
unfold Prim2B; rewrite B2R_FF2B is_finite_FF2B.
rewrite ldshiftexp_spec.
rewrite <-(B2EF_Prim2B primitive_floats_infnan.nan_pl m'').
assert (Hprec : Z.lt prec emax); [now simpl| ].
rewrite EFldexp_Bldexp.
set (f := _ primitive_floats_infnan.nan_pl m'').
set (e''' := Z.sub (to_Z e'') _).
assert (H := Bldexp_correct _ _ _ Hprec Binary.mode_NE f e''').
revert H.
case Rlt_bool_spec; intro Hlt; [ |now case (Bldexp _ _ _ _ _ _ _)].
set (bf := Bldexp _ _ _ _ _ _ _).
intros (Ht, (Hfe''', Hs)).
rewrite FF2R_EF2FF_B2EF Ht.
rewrite is_finite_FF_EF2FF_B2EF Hfe'''; intro Hf.
rewrite round_generic.
{ unfold FtoR.
  set (m''' := if sm then _ else _).
  assert (Hm''' : B2R prec emax f = IZR m''').
  { revert Hf.
    unfold f, m'', m'''.
    pose (bm' := binary_normalize prec emax (zpos_gt_0 53) Hprec mode_NE
                                  (to_Z m') 0 false).
    cut (is_finite prec emax bm' ->
         B2R prec emax bm' = IZR (Z.pos (Bir.MtoP (BigN.N0 m')))).
    { intro H.
      unfold Prim2B; rewrite B2R_FF2B is_finite_FF2B.
      now case sm; [rewrite FPopp_EFopp| ];
        rewrite of_int63_spec binary_normalize_equiv;
        [rewrite (EFopp_Bopp (fun _ => ex_nan))| ];
        rewrite FF2R_EF2FF_B2EF is_finite_FF_EF2FF_B2EF;
        [rewrite B2R_Bopp is_finite_Bopp| ]; intro H'; rewrite H. }
    assert (H := binary_normalize_correct _ _ _ Hprec mode_NE (to_Z m') 0
                                          false); revert H.
    case Rlt_bool_spec; fold bm'; intro Hlt'; [ |now case bm'].
    intros (Hrbm', (_, Hsbm')) _; rewrite Hrbm'.
    rewrite round_generic.
    { unfold F2R; simpl; rewrite Rmult_1_r; f_equal.
      unfold Bir.MtoP, BigN.to_Z.
      unfold CyclicAxioms.ZnZ.to_Z, Cyclic63.Int63Cyclic.ops, Cyclic63.int_ops.
      now rewrite Hm'p. }
    apply generic_format_F2R; intros _; unfold F2R; simpl; rewrite Rmult_1_r.
    unfold cexp, FLT_exp; apply Z.max_lub; [ |lia]; rewrite Hm'p.
    revert Hb; unfold EmulatedFloat.bounded, EmulatedFloat.canonical_mantissa.
    move/andP => [Heq _]; apply Zeq_bool_eq in Heq; revert Heq.
    rewrite Zpos_digits2_pos Zdigits_mag; [unfold fexp; lia|discriminate]. }
  rewrite Hm'''.
  unfold e''', e''.
  revert He.
  case se; [rewrite sub_spec|rewrite add_spec].
  { admit. }
  admit. }
admit.
Admitted.

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
