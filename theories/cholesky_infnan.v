(** * Application: corollary of [cholesky] considering overflows. *)

Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.algebra.matrix mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum fcmdotprod real_matrix cholesky float_infnan_spec.

Section Cholesky_infnan.

Variable fs : Float_infnan_spec.

(** ** Definition of Cholesky decomposition with arithmetic operations with overflow from [float_infnan_spec]. *)
Section Cholesky_def_infnan.

Variable n : nat.

Variable A : 'M[FIS fs]_n.+1.

(** [Rt] is meant to be the (floating point computed) Cholesky factor of [A]. *)
Variable Rt : 'M[FIS fs]_n.+1.

Fixpoint stilde_infnan (k : nat) (c : FIS fs) {struct k} :=
  match k with
    | 0%N => fun _ _ => c
    | k'.+1 => fun (a b : FIS fs ^ (k'.+1)) =>
                 @stilde_infnan k' (fiminus c (fimult (a ord0) (b ord0)))
                                [ffun i => a (lift ord0 i)]
                                [ffun i => b (lift ord0 i)]
  end.

Lemma stilde_infnan_eq k
      (c1 : FIS fs) (a1 b1 : FIS fs ^ k) (c2 : FIS fs) (a2 b2 : FIS fs ^ k) :
  (c1 = c2) ->
  (forall i, a1 i = a2 i) -> (forall i, b1 i = b2 i) ->
  stilde_infnan c1 a1 b1 = stilde_infnan c2 a2 b2.
Proof.
elim: k c1 a1 b1 c2 a2 b2 => [//|k IHk] c1 a1 b1 c2 a2 b2 Hc Ha Hb.
by apply IHk; [by rewrite Hc Ha Hb| |]; move=> i; rewrite !ffunE.
Qed.

Definition ytilded_infnan k (c : FIS fs) (a b : FIS fs ^ k) (bk : FIS fs) :=
  fidiv (stilde_infnan c a b) bk.

Definition ytildes_infnan k (c : FIS fs) (a : FIS fs ^ k) :=
  fisqrt (stilde_infnan c a a).

(** Version of [cholesky_spec] not ignoring overflows. *)
Definition cholesky_spec_infnan : Prop :=
  (forall (j i : 'I_n.+1),
     (i < j)%N ->
     Rt i j = ytilded_infnan (A i j)
                             [ffun k : 'I_i => Rt (inord k) i]
                             [ffun k : 'I_i => Rt (inord k) j]
                             (Rt i i))
  /\ (forall (j : 'I_n.+1),
        Rt j j = ytildes_infnan (A j j)
                                [ffun k : 'I_j => Rt (inord k) j]).

(** [cholesky_success] means [cholesky_spec] and floating point Cholesky
    decomposition runs to completion. *)
Definition cholesky_success_infnan : Prop :=
  cholesky_spec_infnan /\ forall i, (0 < FIS2FS (Rt i i))%Re.

Lemma stilde_infnan_fc k c a b : finite (@stilde_infnan k c a b) -> finite c.
Proof.
elim: k c a b => [//|k IHk] c a b.
rewrite /stilde_infnan /= -/stilde_infnan => H.
apply (@fiminus_spec_fl _ c (fimult (a ord0) (b ord0))), (IHk _ _ _ H).
Qed.

Lemma ytilded_infnan_fc k c a b d : finite (@ytilded_infnan k c a b d) ->
  finite d -> finite c.
Proof. move=> H Fd; apply (stilde_infnan_fc (fidiv_spec_fl H Fd)). Qed.

Lemma ytildes_infnan_fc k c a : finite (@ytildes_infnan k c a) -> finite c.
Proof. move=> H; apply (stilde_infnan_fc (fisqrt_spec_f1 H)). Qed.

Lemma stilde_infnan_fa k c a b : finite (@stilde_infnan k c a b) ->
  forall i, finite (a i).
Proof.
elim: k c a b => [//|k IHk] c a b; [by move=> H; case|].
rewrite /stilde_infnan /= -/stilde_infnan => H i.
case (unliftP ord0 i) => [j|] ->.
{ by move: (IHk _ _ _ H j); rewrite ffunE. }
apply (fimult_spec_fl (fiminus_spec_fr (stilde_infnan_fc H))).
Qed.

Lemma ytildes_infnan_fa k c a : finite (@ytildes_infnan k c a) ->
  forall i, finite (a i).
Proof. move=> H; apply (stilde_infnan_fa (fisqrt_spec_f1 H)). Qed.

Lemma cholesky_success_infnan_f1 : cholesky_success_infnan ->
  forall (i j : 'I_n.+1), (i <= j)%N -> finite (A i j).
Proof.
move=> [H0 H1] i j Hij.
have HRtj := FIS2FS_spec (Rgt_not_eq _ _ (Rlt_gt _ _ (H1 j))).
rewrite (proj2 H0) in HRtj; case (ltnP i j) => Hij'.
{ move: (ytildes_infnan_fa HRtj (Ordinal Hij')); rewrite ffunE inord_val.
  rewrite (proj1 H0) // /ytilded_infnan => H.
  apply (ytilded_infnan_fc H), FIS2FS_spec, Rgt_not_eq, Rlt_gt, H1. }
have -> : i = j; [by apply ord_inj, anti_leq; rewrite Hij|].
apply (ytildes_infnan_fc HRtj).
Qed.

Lemma stilde_infnan_eq_stilde k c a b : finite (@stilde_infnan k c a b) ->
  (FIS2FS (stilde_infnan c a b)
   = stilde (FIS2FS c) [ffun k => FIS2FS (a k)] [ffun k => FIS2FS (b k)] :> R).
Proof.
elim: k c a b => [//|k IHk] c a b.
rewrite /stilde_infnan /= -/stilde_infnan => H.
have HH := stilde_infnan_fc H.
rewrite (IHk _ _ _ H) /stilde /fcmdotprod_l2r /=.
apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE //.
rewrite (fiminus_spec HH) /fminus /fplus /=.
by rewrite (fimult_spec (fiminus_spec_fr HH)).
Qed.

Lemma ytilded_infnan_eq_ytilded k c a b bk :
  finite (@ytilded_infnan k c a b bk) -> (FIS2FS bk <> 0 :> R) ->
  (FIS2FS (ytilded_infnan c a b bk)
   = ytilded (FIS2FS c) [ffun k => FIS2FS (a k)] [ffun k => FIS2FS (b k)]
             (FIS2FS bk) :> R).
Proof.
move=> H Hbk. have Fbk := FIS2FS_spec Hbk.
rewrite fidiv_spec // /fdiv stilde_infnan_eq_stilde //.
by apply (fidiv_spec_fl H), FIS2FS_spec.
Qed.

Lemma ytildes_infnan_eq_ytildes k c a : finite (@ytildes_infnan k c a) ->
  (FIS2FS (ytildes_infnan c a)
   = ytildes (FIS2FS c) [ffun k => FIS2FS (a k)] :> R).
Proof.
move=> H.
rewrite fisqrt_spec // /fsqrt stilde_infnan_eq_stilde //.
apply (fisqrt_spec_f1 H).
Qed.

Definition MFI2F := map_mx (@FIS2FS fs).

Lemma cholesky_spec_infnan_cholesky_spec :
  (forall j, FIS2FS (Rt j j) <> 0 :> R) ->
  cholesky_spec_infnan -> cholesky_spec (MFI2F A) (MFI2F Rt).
Proof.
move=> Hjj H; destruct H as (H, H'); split.
{ move=> j i Hij.
  rewrite mxE H // ytilded_infnan_eq_ytilded //.
  { by apply /ytilded_eq => [|i'|i'|]; try rewrite !ffunE; rewrite !mxE. }
  move: (Hjj j); rewrite H' => H2.
  move: (ytildes_infnan_fa (FIS2FS_spec H2) (Ordinal Hij)).
  rewrite -H // ffunE => H3.
  have H4 : i = inord (Ordinal Hij); [by rewrite inord_val|by rewrite H4]. }
move=> j.
rewrite mxE H' ytildes_infnan_eq_ytildes; [|by rewrite -H'; apply FIS2FS_spec].
by apply /ytildes_eq => [|i]; [|rewrite !ffunE]; rewrite mxE.
Qed.

(** If [cholesky_success_infnan], then no overflow occured during the
    computation of the cholesky decomposition which then gives the same result
    as previously defined ignoring overflows ([cholesky_spec]). *)
Lemma cholesky_success_infnan_cholesky_success :
  cholesky_success_infnan -> cholesky_success (MFI2F A) (MFI2F Rt).
Proof.
move=> H; destruct H as (H0, H1); split.
{ apply /cholesky_spec_infnan_cholesky_spec => // i.
  by apply Rgt_not_eq, Rlt_gt. }
by move=> i; rewrite mxE.
Qed.

End Cholesky_def_infnan.

(** If [A] contains no infinity or NaN, then [MFI2F A] = [A] and
    [posdef (MF2R (MFI2F A))] means that [A] is positive definite. *)
Lemma corollary_2_4_with_c_upper_bound_infnan :
  forall n, 4 * INR n.+2 * eps fs < 1 ->
  forall A : 'M[FIS fs]_n.+1, MF2R (MFI2F A^T) = MF2R (MFI2F A) ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FIS fs]_n.+1,
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, (MFI2F At) i i <= (MFI2F A) i i - c)) ->
  forall Rt : 'M[FIS fs]_n.+1, cholesky_success_infnan At Rt ->
  posdef (MF2R (MFI2F A)).
Proof.
move=> n H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At HAt Rt HARt.
have SymFIA : MF2R (MFI2F A)^T = MF2R (MFI2F A) by rewrite map_trmx SymA.
move: (cholesky_success_infnan_cholesky_success HARt).
apply (corollary_2_4_with_c_upper_bound H4n SymFIA Pdiag Hmaxdiag Hc).
by split; [move=> i j Hij; rewrite !mxE (proj1 HAt)|by apply HAt].
Qed.

(* TODO: MF2R should be a coercion *)
Lemma corollary_2_7_with_c_r_upper_bounds_infnan :
  forall n, 4 * INR n.+2 * eps fs < 1 ->
  forall A : 'M[FIS fs]_n.+1, MF2R (MFI2F A^T) = MF2R (MFI2F A) ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall Rad : 'M[FIS fs]_n.+1, 0 <=m: MF2R (MFI2F Rad) ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma fs (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta fs * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall r : R, (forall (i j : 'I_n.+1), ((MFI2F Rad) i j <= r)%Re) ->
  forall At : 'M[FIS fs]_n.+1,
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, ((MFI2F At) i i <= (MFI2F A) i i
                                           - c - INR n.+1 * r)%Re)) ->
  forall Rt : 'M[FIS fs]_n.+1, cholesky_success_infnan At Rt ->
  forall Xt : 'M_n.+1,
  Mabs (Xt - MF2R (MFI2F A)) <=m: MF2R (MFI2F Rad) -> posdef Xt.
Proof.
move=> n H4n A SymA Pdiag Rad PRad maxdiag Hmaxdiag c Hc r Hr At HAt
         Rt HARt.
have SymFIA : MF2R (MFI2F A)^T = MF2R (MFI2F A) by rewrite map_trmx SymA.
move: (cholesky_success_infnan_cholesky_success HARt).
apply (corollary_2_7_with_c_r_upper_bounds H4n SymFIA Pdiag PRad Hmaxdiag
                                           Hc Hr).
by split; [move=> i j Hij; rewrite !mxE (proj1 HAt)|by apply HAt].
Qed.

End Cholesky_infnan.

Require Import binary64_infnan.

Definition corollary_2_4_with_c_upper_bound64_infnan :=
  @corollary_2_4_with_c_upper_bound_infnan binary64_infnan.

Definition corollary_2_7_with_c_r_upper_bounds64_infnan :=
  @corollary_2_7_with_c_r_upper_bounds_infnan binary64_infnan.
