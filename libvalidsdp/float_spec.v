(** * Specification of floating-point operations in terms of rounding error. *)

(** This assumes rounding to nearest and features optimal bounds from:
    Claude-Pierre Jeannerod, Siegfried M. Rump:
    On relative errors of floating-point operations: Optimal bounds and applications,
    Math. Comput., 87(310):803-819, 2018. *)

(** It is implemented in [flx64] and [binary64] respectively for
    binary64 with unbounded exponents and binary64 without overflow
    and with gradual underflow. *)

Require Import Reals Rstruct Psatz Flocq.Core.Raux.
From mathcomp Require Import ssreflect ssrbool eqtype choice.

Require Export bounded.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Section FS.

Variable format : R -> bool.

Record FS_of := { FS_val :> R; _ : format FS_val }.

Canonical FS_subType := [subType for FS_val].
(** Now that FS_of has an eqtype structure, one can use val_inj
    as a proof that FS_val is injective *)

(** FS_of inherits the eqType and choiceType structures of R (see Rstruct.v) *)
Definition FS_eqMixin := [eqMixin of FS_of by <:].
Canonical FS_eqType := EqType FS_of FS_eqMixin.
Definition FS_choiceMixin := [choiceMixin of FS_of by <:].
Canonical FS_choiceType := ChoiceType FS_of FS_choiceMixin.

End FS.

Record Float_spec := {

  (** [format x] means that the real number [x] is a floating point value. *)
  format : R -> bool;

  (** The type of floating point values (coercible to R). *)
  FS := FS_of format;

  (** 0 and 1 must be floating-point numbers. *)
  format0 : format 0;
  format1 : format 1;

  (** The opposite of a floating point number is a floating point number. *)
  format_opp x : format x -> format (- x);

  (** Bound on the relative error (normalized numbers, no underflow). *)
  eps : R;

  eps_pos : 0 <= eps;
  eps_lt_1 : eps < 1;

  b_eps := bounded eps;
  b_epsd1peps := bounded (eps / (1 + eps));

  (** Bound on the absolute error (denormalized, when underflow occurs). *)
  eta : R;

  eta_pos : 0 <= eta;

  b_eta := bounded eta;

  (** Some rounding. *)
  frnd : R -> FS;

  frnd_F (x : FS) : frnd x = x;

  frnd_spec x :
    exists (d : b_epsd1peps) (e : b_eta),
      frnd x = (1 + d) * x + e :> R /\ d * e = 0;

  (** Addition. *)
  fplus (x y : FS) : FS := frnd (x + y);

  fplus_spec x y : exists d : b_epsd1peps, fplus x y = (1 + d) * (x + y) :> R;

  (** This is only true in rounding to nearest. *)
  fplus_spec_l x y : Rabs (fplus x y - (x + y)) <= Rabs x;

  fplus_spec2 (x y : FS) : y <= 0 -> fplus x y <= x;

  (** Multiplication. *)
  fmult (x y : FS) : FS := frnd (x * y);

  fmult_spec (x y : FS) := frnd_spec (x * y);

  fmult_spec2 x : 0 <= fmult x x;

  (** Square root. *)
  fsqrt (x : FS) : FS := frnd (sqrt x);

  fsqrt_spec x :
    exists d : bounded (1 - 1 / sqrt (1 + 2 * eps)),
      fsqrt x = (1 + d) * (sqrt x) :> R;
}.

(** ** All the remaining properties can be proved assuming the above ones. *)

(** *** Various lemmas on the various bounds used. *)
Section Bounds.

Variable eps : R.
Hypothesis Heps : 0 <= eps.

Lemma epsd1peps_pos : 0 <= eps / (1 + eps).
Proof. apply Rmult_le_pos; [|apply Rlt_le, Rinv_0_lt_compat]; lra. Qed.

(** can be used with [widen_bounded] to replace 1/(1+eps) with eps *)
Lemma epsd1peps_le_eps : eps / (1 + eps) <= eps.
Proof.
apply (Rmult_le_reg_r (1 + eps)); [lra|].
unfold Rdiv; rewrite Rmult_assoc Rinv_l; [|lra].
assert (0 <= eps * eps); [apply misc.sqr_ge_0|lra].
Qed.

Lemma om1ds1p2eps_pos : 0 <= 1 - 1 / sqrt (1 + 2 * eps).
Proof.
unfold Rdiv; rewrite Rmult_1_l -{1}Rinv_1.
apply Rle_0_minus, Rinv_le; [lra|].
rewrite -{1}sqrt_1; apply sqrt_le_1_alt; lra.
Qed.
  
Lemma om1ds1p2eps_le_epsd1peps : 1 - 1 / sqrt (1 + 2 * eps) <= eps / (1 + eps).
Proof.
apply (Rmult_le_reg_r (sqrt (1 + 2 * eps) * (1 + eps))).
{ apply Rmult_lt_0_compat; [apply sqrt_lt_R0|]; lra. }
field_simplify; [|lra|intro H; apply sqrt_eq_0 in H; lra].
unfold Rdiv, Rminus; (try rewrite Rinv_1 !Rmult_1_r); rewrite !Rplus_assoc.
rewrite <-(Rplus_0_r (sqrt _ * _)) at 2; apply Rplus_le_compat_l.
apply (Rplus_le_reg_r (1 + eps)); ring_simplify.
rewrite <-(sqrt_square (_ + 1)); [|lra]; apply sqrt_le_1_alt.
assert (H := misc.sqr_ge_0 eps); lra.
Qed.

Lemma s1p2epsm1_pos : 0 <= sqrt (1 + 2 * eps) - 1.
apply (Rplus_le_reg_r 1); ring_simplify.
rewrite <-sqrt_1 at 1; apply sqrt_le_1_alt; lra.
Qed.

End Bounds.

Section Derived_spec.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation b_eps := (b_eps fs).
Notation b_epsd1peps := (b_epsd1peps fs).
Notation eta := (eta fs).
Notation b_eta := (b_eta fs).

Definition F0 : F := Build_FS_of (format0 fs).

Definition F1 : F := Build_FS_of (format1 fs).

Definition eps_0 : b_eps := bounded_0 (eps_pos fs).

Definition epsd1peps_0 : b_epsd1peps := bounded_0 (epsd1peps_pos (eps_pos fs)).

Definition eta_0 : b_eta := bounded_0 (eta_pos fs).

(** Opposite. *)
Program Definition fopp (x : F) : F := @Build_FS_of _ (- (FS_val x)) _.
Next Obligation. by apply format_opp; case x. Qed.

(** Rounding. *)
Lemma frnd_spec_separate (x : R) :
  exists x' : R,
    frnd x' = frnd x /\ (exists e : b_eta, x' = x + e)
    /\ (exists d : b_epsd1peps, frnd x' = (1 + d) * x' :> R).
Proof.
destruct (frnd_spec fs x) as (d, (e, (Hde, Hde0))).
destruct (Rlt_or_le (Rabs (d * x)) (Rabs e)) as [HdxLte|HeLedx].
{ exists (frnd x); split; [|split].
  { by rewrite frnd_F. }
  { exists e; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
    { now rewrite Zd Rplus_0_r Rmult_1_l. }
    exfalso; revert HdxLte; rewrite Ze Rabs_R0; apply Rle_not_lt, Rabs_pos. }
  now exists epsd1peps_0; rewrite frnd_F Rplus_0_r Rmult_1_l. }
exists x; split; [now simpl|split].
{ now exists eta_0; rewrite Rplus_0_r. }
exists d; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
{ assert (Ze : e = 0 :> R); [|now rewrite Ze Rplus_0_r].
  apply Rcomplements.Rabs_eq_0, Rle_antisym; [|now apply Rabs_pos].
  now revert HeLedx; rewrite Zd Rmult_0_l Rabs_R0. }
now rewrite Ze Rplus_0_r.
Qed.

Lemma frnd_spec_round x :
  exists (d : b_eps) (e : b_eta), x = (1 + d) * frnd x + e :> R /\ d * e = 0.
Proof.
destruct (frnd_spec fs x) as (d, (e, (Hde, Zde))).
destruct (Rmult_integral _ _ Zde) as [Zd|Ze].
{ exists (bounded_0 (eps_pos fs)), (bounded_opp e).
  rewrite Rmult_0_l; split; [|reflexivity].
  rewrite Hde Zd !Rplus_0_r !Rmult_1_l; simpl; ring. }
assert (H := Interval_missing.Rabs_def2_le _ _ (bounded_prop d)).
assert (H' := epsd1peps_le_eps (eps_pos fs)); assert (H'' := eps_lt_1 fs).
destruct (Req_dec (frnd x) 0) as [Zfx|Nzfx].
{ assert (Zx : x = 0).
  { revert Hde; rewrite Zfx Ze Rplus_0_r; intro Hde.
    now destruct (Rmult_integral _ _ (sym_eq Hde)) as [Hx|Hx]; [lra|]. }
  now exists eps_0, eta_0; rewrite !Rplus_0_r Rmult_1_l Rmult_0_l Zfx. }
destruct (Req_dec x 0) as [Zx|Nzx].
{ now exfalso; revert Hde; rewrite {2}Zx; rewrite Ze Rmult_0_r Rplus_0_r. }
set (d' := (x - frnd x) / frnd x).
assert (Hd' : Rabs d' <= eps).
{ unfold d'; rewrite Hde Ze Rplus_0_r.
  replace (_ / _) with (- d / (1 + d)); [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ (bounded_prop d)).
  unfold Rdiv; apply Rmult_le_compat_l; [now apply eps_pos|].
  apply (Rle_trans _ (1 - eps / (1 + eps))); [right; field|]; lra. }
exists (Build_bounded Hd'), eta_0.
now rewrite Rplus_0_r Rmult_0_r; split; [unfold d'; simpl; field|].
Qed.

Lemma frnd_spec_round_max x :
  Rabs (frnd x - x) <= Rmax (eps * Rabs (frnd x)) eta.
Proof.
assert (Hde := frnd_spec_round x).
destruct Hde as (d, (e, (Hde, Hde0))).
rewrite Rabs_minus_sym; rewrite {1}Hde.
replace (_ - _) with (d * frnd x + e); [|ring].
assert (H := Rmult_integral _ _ Hde0); destruct H as [Hd|He].
{ rewrite Hd Rmult_0_l Rplus_0_l.
  apply (Rle_trans _ _ _ (bounded_prop _)), Rmax_r. }
rewrite He Rplus_0_r Rabs_mult.
assert (H := Rmax_l (eps * Rabs (frnd x)) eta); revert H.
apply Rle_trans, Rmult_le_compat_r; [apply Rabs_pos|apply bounded_prop].
Qed.

(** Addition. *)
Lemma fplus_spec_round (x y : F) :
  exists d : b_eps, x + y = (1 + d) * fplus x y :> R.
Proof.
destruct (fplus_spec x y) as (d, Hd).
assert (H := Interval_missing.Rabs_def2_le _ _ (bounded_prop d)).
assert (H' := epsd1peps_le_eps (eps_pos fs)); assert (H'' := eps_lt_1 fs).
destruct (Req_dec (fplus x y) 0) as [Zfxy|Nzfxy].
{ exists (bounded_0 (eps_pos fs)).
  rewrite Rplus_0_r Rmult_1_l Zfxy.
  now rewrite Zfxy in Hd; destruct (Rmult_integral _ _ (sym_eq Hd)); [lra|]. }
destruct (Req_dec (x + y) 0) as [Zxy|Nzxy].
{ now exfalso; revert Hd; rewrite Zxy Rmult_0_r. }
set (d' := ((x + y) - fplus x y) / fplus x y).
assert (Hd' : Rabs d' <= eps).
{ unfold d'; rewrite Hd.
  replace (_ / _) with (- d / (1 + d)); [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ (bounded_prop d)).
  unfold Rdiv; apply Rmult_le_compat_l; [now apply eps_pos|].
  apply (Rle_trans _ (1 - eps / (1 + eps))); [right; field|]; lra. }
now exists (Build_bounded Hd'); unfold d'; simpl; field.
Qed.

Lemma fplus_spec_r (x y : F) : Rabs (fplus x y - (x + y)) <= Rabs y.
Proof. unfold fplus; rewrite Rplus_comm; apply fplus_spec_l. Qed.

(** Subtraction. *)
Definition fminus (x y : F) : F := fplus x (fopp y).

(** Division (the paper conatains tighter bounds for radix2, not
    implemented here). *)
Definition fdiv (x y : F) : F := frnd (x / y).

Definition fdiv_spec (x y : F) := frnd_spec fs (x / y).

(** Square root. *)
Lemma fsqrt_spec2 (x : F) : 0 < fsqrt x -> 0 < x.
Proof.
intros Psx.
destruct (Rlt_or_le 0 x) as [Hx|Hx]; [easy|exfalso].
apply (Rlt_not_ge _ _ Psx), Rle_ge.
destruct (fsqrt_spec x) as (d, Hd); rewrite Hd.
rewrite <- (Rmult_0_r (1+d)).
apply Rmult_le_compat_l.
{ apply (Rplus_le_reg_r (-d)); ring_simplify.
  apply Raux.Rabs_le_inv  .
  rewrite Rabs_Ropp.
  destruct d as (d, dlte); apply (Rle_trans _ _ _ dlte).
  apply (Rle_trans _ _ _ (om1ds1p2eps_le_epsd1peps (eps_pos fs))).
  apply (Rle_trans _ _ _ (epsd1peps_le_eps (eps_pos fs))).
  apply Rlt_le, eps_lt_1. }
now rewrite (Raux.sqrt_neg _ Hx); right.
Qed.

(** sqrt(1 + 2 eps) - 1 <= eps *)
Lemma fsqrt_spec_round (x : F) :
  exists d : bounded (sqrt (1 + 2 * eps) - 1), sqrt x = (1 + d) * fsqrt x.
Proof.
destruct (fsqrt_spec x) as (d, Hd).
assert (H := Interval_missing.Rabs_def2_le _ _ (bounded_prop d)).
assert (H' := om1ds1p2eps_le_epsd1peps (eps_pos fs)).
assert (H'' := epsd1peps_le_eps (eps_pos fs)); assert (H''' := eps_lt_1 fs).
assert (Hpos := s1p2epsm1_pos (eps_pos fs)).
destruct (Req_dec (fsqrt x) 0) as [Zfx|Nzfx].
{ exists (bounded_0 Hpos).
  rewrite Rplus_0_r Rmult_1_l Zfx.
  now rewrite Zfx in Hd; destruct (Rmult_integral _ _ (sym_eq Hd)); [lra|]. }
destruct (Req_dec (sqrt x) 0) as [Zx|Nzx].
{ now exfalso; revert Hd; rewrite Zx Rmult_0_r. }
set (d' := (sqrt x - fsqrt x) / fsqrt x).
assert (Hd' : Rabs d' <= sqrt (1 + 2 * eps) - 1).
{ unfold d'; rewrite Hd.
  replace (_ / _) with (- d / (1 + d)); [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ (bounded_prop d)).
  apply (Rle_trans _ ((sqrt (1 + 2 * eps) - 1) * (1/sqrt (1 + 2 * eps))));
    [right; field|apply Rmult_le_compat_l]; lra. }
now exists (Build_bounded Hd'); unfold d'; simpl; field.
Qed.

End Derived_spec.
