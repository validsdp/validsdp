(* (setq coq-prog-name "~/forge/git/validsdp/coq/bin/coqtop") *)
(** * Main tactic for multivariate polynomial positivity. *)

Require Import ZArith.
From Flocq Require Import Core. Require Import Datatypes.
From Interval Require Import Interval_definitions Interval_xreal.
From Interval Require Import Interval_missing.
From Interval Require Import Interval_specific_ops. (* for Float *)
From CoqEAL.theory Require Import ssrcomplements.
From CoqEAL.refinements Require Import hrel refinements param seqmx seqmx_complements binnat binint rational binrat.
Require Import Reals Flocq.Core.Raux QArith CBigZ CBigQ Psatz FSetAVL.
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

Definition BigZ2int63 (n : BigZ.t_) : option (bool * Int63Native.int) :=
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
        apply leb_spec.
        apply leb_0.
Qed.

Definition BigZFloat2Prim (f : s_float BigZ.t_ BigZ.t_) :=
  match f with
  | Fnan => nan
  | Float m e =>
    match (BigZ2int63 m, BigZ2int63 e) with
    | (Some (sm, m), Some (se, e)) =>
      let f := of_int63 m in
      let f := if sm then (-f)%float else f in
      let shexp := if se then (shift - e)%int63 else (shift + e)%int63 in
      ldshiftexp f shexp
    | _ => nan
    end
  end.

Lemma BigZFloat2Prim_correct (f : F.type) :
  is_true (is_finite (BigZFloat2Prim f)) -> FI2FS (BigZFloat2Prim f) = proj_val (F.toX f) :> R.
Proof.
  case f.
  - now cbn.
  - intros m e.
    assert (Hm := BigZ2int63_correct m).
    assert (He := BigZ2int63_correct e).
    unfold BigZFloat2Prim.
    unfold F.toX, FtoX, F.toF.
    assert (Hbms := Bir_mantissa_sign_correct m).
    revert Hbms Hm He.
    destruct (BigZ2int63 m); destruct (BigZ2int63 e) ;
      [ | now destruct p | discriminate | discriminate ].
    destruct p as (sm, m').
    destruct p0 as (se, e').
    case_eq (m' == 0)%int63.
    + intros Hm' Hbms _ _ _.
      rewrite Hbms.
      apply eqb_correct in Hm'.
      rewrite Hm'.
      simpl.
      rewrite <- (EF2Prim_Prim2EF (of_int63 0)%float).
      rewrite of_int63_spec.
      replace [|0|]%int63 with Z0 by reflexivity.
      simpl.
      unfold FlocqNativeLayer.Prim2B.
      destruct sm.
      * rewrite (FlocqNativeLayer.FF2B_proof_irr _ (Binary.F754_zero true) _ (FlocqNativeLayer.Prim2B_obligation_1 _ _) (eq_refl true)).
        -- reflexivity.
        -- rewrite ldshiftexp_spec.
           reflexivity.
      * rewrite (FlocqNativeLayer.FF2B_proof_irr _ (Binary.F754_zero false) _ (FlocqNativeLayer.Prim2B_obligation_1 _ _) (eq_refl true)).
        -- reflexivity.
        -- rewrite ldshiftexp_spec.
           reflexivity.
    + intros Hm' Hbms.
      rewrite Hbms.
      apply eqb_false_correct in Hm'.
      intros _.
      clear Hbms m.
      intro He.
      assert (H : (if se then (shift - e')%int63 else (shift + e')%int63) = of_Z (Z.add [|shift|]%int63 [e]%bigZ)).
      {
        destruct se.
        - rewrite <- to_Z_eq.
          rewrite of_Z_spec.
          rewrite sub_spec.
          rewrite <- Z.add_opp_r.
          now rewrite He.
        - rewrite <- to_Z_eq.
          rewrite of_Z_spec.
          rewrite add_spec.
          now rewrite He.
      }
      rewrite H.
      clear H He.
      destruct sm; intro Hm.
      * rewrite <- (EF2Prim_Prim2EF (- of_int63 m')%float).
        rewrite FPopp_EFopp.
        rewrite of_int63_spec.
        rewrite <- (EF2Prim_Prim2EF (ldshiftexp _ _)).
        rewrite ldshiftexp_spec.
        rewrite Prim2EF_EF2Prim.
        -- admit.
        -- admit.
      * admit.
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
