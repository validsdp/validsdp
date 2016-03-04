(** * Application: corollary of [cholesky] considering overflows. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg matrix bigop.

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

Variable A : 'M[FI fs]_n.+1.

(** [Rt] is meant to be the (floating point computed) Cholesky factor of [A]. *)
Variable Rt : 'M[FI fs]_n.+1.

Fixpoint stilde_infnan (k : nat) (c : FI fs) {struct k} :=
  match k with
    | 0%N => fun _ _ => c
    | k'.+1 => fun (a b : FI fs ^ (k'.+1)) =>
                 @stilde_infnan k' (fiminus c (fimult (a ord0) (b ord0)))
                                [ffun i => a (lift ord0 i)]
                                [ffun i => b (lift ord0 i)]
  end.

Definition ytilded_infnan k (c : FI fs) (a b : FI fs ^ k) (bk : FI fs) :=
  fidiv (stilde_infnan c a b) bk.

Definition ytildes_infnan k (c : FI fs) (a : FI fs ^ k) :=
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
  cholesky_spec_infnan /\ forall i, (0 < FI2F (Rt i i))%Re.

Lemma stilde_infnan_fc k c a b : finite (@stilde_infnan k c a b) -> finite c.
Proof.
elim: k c a b => [//|k IHk] c a b.
rewrite /stilde_infnan /= -/stilde_infnan => H.
apply (@fiminus_spec_fl _ c (fimult (a ord0) (b ord0))), (IHk _ _ _ H).
Qed.

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

Lemma stilde_infnan_eq_stilde k c a b : finite (@stilde_infnan k c a b) ->
  (FI2F (stilde_infnan c a b)
   = stilde (FI2F c) [ffun k => FI2F (a k)] [ffun k => FI2F (b k)] :> R).
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
  finite (@ytilded_infnan k c a b bk) -> (FI2F bk <> 0 :> R) ->
  (FI2F (ytilded_infnan c a b bk)
   = ytilded (FI2F c) [ffun k => FI2F (a k)] [ffun k => FI2F (b k)]
             (FI2F bk) :> R).
Proof.
move=> H Hbk. have Fbk := FI2F_spec Hbk.
rewrite fidiv_spec // /fdiv stilde_infnan_eq_stilde //.
by apply (fidiv_spec_fl H), FI2F_spec.
Qed.

Lemma ytildes_infnan_eq_ytildes k c a : finite (@ytildes_infnan k c a) ->
  (FI2F (ytildes_infnan c a)
   = ytildes (FI2F c) [ffun k => FI2F (a k)] :> R).
Proof.
move=> H.
rewrite fisqrt_spec // /fsqrt stilde_infnan_eq_stilde //.
apply (fisqrt_spec_f1 H).
Qed.

Definition MFI2F := map_mx (@FI2F fs).

Lemma cholesky_spec_infnan_cholesky_spec :
  (forall j, FI2F (Rt j j) <> 0 :> R) ->
  cholesky_spec_infnan -> cholesky_spec (MFI2F A) (MFI2F Rt).
Proof.
move=> Hjj H; destruct H as (H, H'); split.
{ move=> j i Hij.
  rewrite mxE H // ytilded_infnan_eq_ytilded //.
  { by apply /ytilded_eq => [|i'|i'|]; try rewrite !ffunE; rewrite !mxE. }
  move: (Hjj j); rewrite H' => H2.
  move: (ytildes_infnan_fa (FI2F_spec H2) (Ordinal Hij)).
  rewrite -H // ffunE => H3.
  have H4 : i = inord (Ordinal Hij); [by rewrite inord_val|by rewrite H4]. }
move=> j.
rewrite mxE H' ytildes_infnan_eq_ytildes; [|by rewrite -H'; apply FI2F_spec].
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
  forall n, 4 * INR n.+2 * eps (fis fs) < 1 ->
  forall A : 'M[FI fs]_n.+1, A^T = A ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma (fis fs) (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall At : 'M[FI fs]_n.+1, At^T = At ->
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, (MFI2F At) i i <= (MFI2F A) i i - c)) ->
  forall Rt : 'M[FI fs]_n.+1, cholesky_success_infnan At Rt ->
  posdef (MF2R (MFI2F A)).
Proof.
move=> n H4n A SymA Pdiag maxdiag Hmaxdiag c Hc At SymAt HAt Rt HARt.
have SymFIA : (MFI2F A)^T = MFI2F A by rewrite map_trmx SymA.
have SymFIAt : (MFI2F At)^T = MFI2F At by rewrite map_trmx SymAt.
move: (cholesky_success_infnan_cholesky_success HARt).
apply (corollary_2_4_with_c_upper_bound H4n SymFIA Pdiag Hmaxdiag Hc SymFIAt).
by split; [move=> i j Hij; rewrite !mxE (proj1 HAt)|by apply HAt].
Qed.

Lemma corollary_2_7_with_c_r_upper_bounds_infnan :
  forall n, 4 * INR n.+2 * eps (fis fs) < 1 ->
  forall A : 'M[FI fs]_n.+1, A^T = A ->
  (forall i : 'I_n.+1, 0 <= (MFI2F A) i i) ->
  forall Rad : 'M[F (fis fs)]_n.+1, 0 <=m: MF2R Rad ->
  forall maxdiag : R, (forall i : 'I_n.+1, (MFI2F A) i i <= maxdiag) ->
  forall c : R,
  (/2 * gamma (fis fs) (2 * n.+2) * (\tr (MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n.+1 * (2 * INR n.+2 + maxdiag)
   <= c)%Re ->
  forall r : R, (forall (i j : 'I_n.+1), (Rad i j <= r)%Re) ->
  forall At : 'M[FI fs]_n.+1, At^T = At ->
  ((forall i j : 'I_n.+1, (i < j)%N -> At i j = A i j) /\
   (forall i : 'I_n.+1, ((MFI2F At) i i <= (MFI2F A) i i
                                           - c - INR n.+1 * r)%Re)) ->
  forall Rt : 'M[FI fs]_n.+1, cholesky_success_infnan At Rt ->
  forall Xt : 'M_n.+1, Xt^T = Xt ->
  Mabs (Xt - MF2R (MFI2F A)) <=m: MF2R Rad -> posdef Xt.
Proof.
move=> n H4n A SymA Pdiag Rad PRad maxdiag Hmaxdiag c Hc r Hr At SymAt HAt
         Rt HARt.
have SymFIA : (MFI2F A)^T = MFI2F A by rewrite map_trmx SymA.
have SymFIAt : (MFI2F At)^T = MFI2F At by rewrite map_trmx SymAt.
move: (cholesky_success_infnan_cholesky_success HARt).
apply (corollary_2_7_with_c_r_upper_bounds H4n SymFIA Pdiag PRad Hmaxdiag
                                           Hc Hr SymFIAt).
by split; [move=> i j Hij; rewrite !mxE (proj1 HAt)|by apply HAt].
Qed.

End Cholesky_infnan.

Require Import binary64_infnan.

Definition corollary_2_4_with_c_upper_bound64_infnan :=
  @corollary_2_4_with_c_upper_bound_infnan binary64_infnan.

Definition corollary_2_7_with_c_r_upper_bounds64_infnan :=
  @corollary_2_7_with_c_r_upper_bounds_infnan binary64_infnan.