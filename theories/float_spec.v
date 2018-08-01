(** * Specification of floating-point operations in terms of rounding error. *)

Require Import Reals.

Require Export bounded.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Record FS_of format := { FS_val :> R; FS_prop : format FS_val }.

Record Float_spec := {

  (** [format x] means that the real number [x] is a floating point value. *)
  format : R -> Prop;

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

  (** Bound on the absolute error (denormalized, when underflow occurs). *)
  eta : R;

  eta_pos : 0 < eta;

  b_eta := bounded eta;

  (** Some rounding. *)
  frnd : R -> FS;

  frnd_F (x : FS) : frnd x = x :> R;

  frnd_spec x :
    exists (d : b_eps) (e : b_eta),
      (frnd x = (1 + d) * x + e :> R /\ d * e = 0)%Re;

  (* TODO: could be infered from tighter forward bound eps / (1 + eps) *)
  frnd_spec_b x :
    exists (d : b_eps) (e : b_eta),
      (x = (1 + d) * frnd x + e :> R /\ d * e = 0)%Re;

  (** Addition. *)
  fplus (x y : FS) : FS := frnd (x + y);

  fplus_spec x y : exists d : b_eps, (fplus x y = (1 + d) * (x + y) :> R)%Re;

  (* TODO: could be infered from tighter forward bound eps / (1 + eps) *)
  fplus_spec_b (x y : FS) :
    exists d : b_eps, (x + y = (1 + d) * fplus x y :> R)%Re;

  (** This is only true in rounding to nearest. *)
  fplus_spec_l x y : (Rabs (fplus x y - (x + y)) <= Rabs x)%Re;

  fplus_spec2 (x y : FS) : (y <= 0 -> fplus x y <= x)%Re;

  (** Multiplication. *)
  fmult (x y : FS) : FS := frnd (x * y);

  fmult_spec (x y : FS) := frnd_spec (x * y);

  fmult_spec2 x : (0 <= fmult x x)%Re;

  (** Square root. *)
  fsqrt (x : FS) : FS := frnd (sqrt x);

  fsqrt_spec x : exists d : b_eps, (fsqrt x = (1 + d) * (sqrt x) :> R)%Re;

  (** sqrt(1 + 2 eps) - 1 <= eps *)
  fsqrt_spec_b (x : FS) :
    exists d : bounded (sqrt (1 + 2 * eps) - 1)%Re,
      (sqrt x = (1 + d) * fsqrt x)%Re
}.

Section Derived_spec.

Variable fs : Float_spec.

Definition F0 : FS fs := {| FS_val := 0; FS_prop := format0 fs |}.

Definition F1 : FS fs := {| FS_val := 1; FS_prop := format1 fs |}.

Definition eps_0 : b_eps fs := bounded_0 (eps_pos fs).

Definition eta_0 : b_eta fs := bounded_0 (Rlt_le 0 (eta fs) (eta_pos fs)).

(** Opposite. *)
Definition fopp (x : FS fs) : FS fs :=
  {| FS_val := -x; FS_prop := format_opp (FS_prop x) |}.

Lemma frnd_spec_separate (x : R) :
  exists x' : R,
    frnd fs x' = frnd fs x :> R /\ (exists e : b_eta fs, x' = x + e)
    /\ (exists d : b_eps fs, frnd fs x' = (1 + d) * x' :> R).
Proof.
destruct (frnd_spec fs x) as (d, (e, (Hde, Hde0))).
destruct (Rlt_or_le (Rabs (d * x)) (Rabs e)) as [HdxLte|HeLedx].
{ exists (frnd fs x); split; [|split].
  { apply frnd_F. }
  { exists e; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
    { now rewrite Zd, Rplus_0_r, Rmult_1_l. }
    exfalso; revert HdxLte; rewrite Ze, Rabs_R0; apply Rle_not_lt, Rabs_pos. }
  now exists eps_0; rewrite frnd_F, Rplus_0_r, Rmult_1_l. }
exists x; split; [now simpl|split].
{ now exists eta_0; rewrite Rplus_0_r. }
exists d; rewrite Hde; destruct (Rmult_integral _ _ Hde0) as [Zd|Ze].
{ assert (Ze : e = 0 :> R); [|now rewrite Ze, Rplus_0_r].
  apply Rcomplements.Rabs_eq_0, Rle_antisym; [|now apply Rabs_pos].
  now revert HeLedx; rewrite Zd, Rmult_0_l, Rabs_R0. }
now rewrite Ze, Rplus_0_r.
Qed.

Lemma frnd_spec_b_max x :
  Rabs (frnd fs x - x) <= Rmax (eps fs * Rabs (frnd fs x)) (eta fs).
Proof.
assert (Hde := frnd_spec_b fs x).
destruct Hde as (d, (e, (Hde, Hde0))).
rewrite Rabs_minus_sym; rewrite Hde at 1.
replace (_ - _)%Re with (d * frnd fs x + e)%Re; [|ring].
assert (H := Rmult_integral _ _ Hde0); destruct H as [Hd|He].
{ rewrite Hd, Rmult_0_l, Rplus_0_l.
  apply (Rle_trans _ _ _ (bounded_prop _)), Rmax_r. }
rewrite He, Rplus_0_r, Rabs_mult.
assert (H := Rmax_l (eps fs * Rabs (frnd fs x)) (eta fs)); revert H.
apply Rle_trans, Rmult_le_compat_r; [apply Rabs_pos|apply bounded_prop].
Qed.

Lemma fplus_spec_r (x y : FS fs) : (Rabs (fplus x y - (x + y)) <= Rabs y)%Re.
Proof. unfold fplus; rewrite Rplus_comm; apply fplus_spec_l. Qed.

(** Subtraction. *)
Definition fminus (x y : FS fs) : FS fs := fplus x (fopp y).

Lemma fsqrt_spec2 (x : FS fs) : 0 < fsqrt x -> 0 < x.
Proof.
intros Psx.
destruct (Rlt_or_le 0 x) as [Hx|Hx]; [easy|casetype False].
apply (Rlt_not_ge _ _ Psx), Rle_ge.
destruct (fsqrt_spec x) as (d, Hd); rewrite Hd.
rewrite <- (Rmult_0_r (1+d)).
apply Rmult_le_compat_l.
{ apply (Rplus_le_reg_r (-d)); ring_simplify.
  apply Raux.Rabs_le_inv  .
  rewrite Rabs_Ropp.
  destruct d as (d, dlte); apply (Rle_trans _ _ _ dlte).
  apply Rlt_le, eps_lt_1. }
now rewrite (Raux.sqrt_neg _ Hx); right.
Qed.

(** Division. *)
Definition fdiv (x y : FS fs) : FS fs := frnd fs (x / y).

Definition fdiv_spec (x y : FS fs) := frnd_spec fs (x / y).

End Derived_spec.
