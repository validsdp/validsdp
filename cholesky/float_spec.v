(** * Specification of floating-point operations in terms of rounding error. *)

Require Import Reals.

Require Export bounded.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Record Ff format := { F_val :> R; F_prop : format F_val }.

Record Float_spec := {

  (** [format x] means that the real number [x] is a floating point value. *)
  format : R -> Prop;

  (** The type of floating point values (coercible to R). *)
  F := Ff format;

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
  frnd : R -> F;

  frnd_spec x :
    exists (d : b_eps) (e : b_eta), (frnd x = (1 + d) * x + e :> R)%Re;

  (** Addition. *)
  fplus (x y : F) : F := frnd (x + y);

  fplus_spec x y : exists d : b_eps, (fplus x y = (1 + d) * (x + y) :> R)%Re;

  fplus_spec2 (x y : F) : (y <= 0 -> fplus x y <= x)%Re;

  (** Multiplication. *)
  fmult (x y : F) : F := frnd (x * y);

  fmult_spec (x y : F) := frnd_spec (x * y);

  fmult_spec2 x : (0 <= fmult x x)%Re;

  (** Square root. *)
  fsqrt (x : F) : F := frnd (sqrt x);

  fsqrt_spec x : exists d : b_eps, (fsqrt x = (1 + d) * (sqrt x) :> R)%Re
}.

Section Derived_spec.

Variable fs : Float_spec.

Definition F0 : F fs := {| F_val := 0; F_prop := format0 fs |}.

Definition F1 : F fs := {| F_val := 1; F_prop := format1 fs |}.

Definition eps_0 : b_eps fs := bounded_0 (eps_pos fs).

Definition eta_0 : b_eta fs := bounded_0 (Rlt_le 0 (eta fs) (eta_pos fs)).

(** Opposite. *)
Definition fopp (x : F fs) : F fs :=
  {| F_val := -x; F_prop := format_opp (F_prop x) |}.

(** Subtraction. *)
Definition fminus (x y : F fs) : F fs := fplus x (fopp y).

Lemma fsqrt_spec2 (x : F fs) : 0 < fsqrt x -> 0 < x.
Proof.
intros Psx.
destruct (Rlt_or_le 0 x) as [Hx|Hx]; [easy|casetype False].
apply (Rlt_not_ge _ _ Psx), Rle_ge.
destruct (fsqrt_spec x) as (d, Hd); rewrite Hd.
rewrite <- (Rmult_0_r (1+d)).
apply Rmult_le_compat_l.
{ apply (Rplus_le_reg_r (-d)); ring_simplify.
  apply Fcore_Raux.Rabs_le_inv  .
  rewrite Rabs_Ropp.
  destruct d as (d, dlte); apply (Rle_trans _ _ _ dlte).
  apply Rlt_le, eps_lt_1. }
now rewrite (Fcore_Raux.sqrt_neg _ Hx); right.
Qed.

(** Division. *)
Definition fdiv (x y : F fs) : F fs := frnd fs (x / y).

Definition fdiv_spec (x y : F fs) := frnd_spec fs (x / y).

End Derived_spec.
