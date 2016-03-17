(** * Specification of floating-point operations with overflow. *)

Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Require Export float_spec.

Record Float_infnan_spec := {
  (** Type of floating-point values (either finite, infinite or NaN). *)
  FI : Type;

  FI0 : FI;
  
  (** [finite f] means that the floating-point number [f] is finite. *)
  finite : FI -> Prop;

  finite0 : finite FI0;
  
  (** Underlying unbounded floating-point format.
      [FI] and [F fis] match when [finite] holds. *)
  fis : Float_spec;

  (** Any float less than [m] (in absolute value) will be finite
      (typically, [m] can be the smallest non representable positive float). *)
  m : R;

  m_ge_2 : 2 <= m;
  
  (** Associates the corresponding value in [F fis] for finite values
      or [F0] for infinities and NaN. *)
  FI2F : FI -> F fis;

  FI2F_spec x : (FI2F x <> 0 :> R) -> finite x;
  FI2F0 : FI2F (FI0) = F0 fis :> R;
  
  (** Some rounding. *)
  firnd : R -> FI;

  firnd_spec x : finite (firnd x) -> FI2F (firnd x) = frnd fis x :> R;
  firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x);
  
  (** Opposite. *)
  fiopp : FI -> FI;

  fiopp_spec x : finite (fiopp x) -> FI2F (fiopp x) = fopp (FI2F x) :> R;
  fiopp_spec_f1 x : finite (fiopp x) -> finite x;
  fiopp_spec_f x : finite x -> finite (fiopp x);

  (** Addition. *)
  fiplus : FI -> FI -> FI;

  fiplus_spec x y : finite (fiplus x y) ->
    FI2F (fiplus x y) = fplus (FI2F x) (FI2F y) :> R;
  fiplus_spec_fl x y : finite (fiplus x y) -> finite x;
  fiplus_spec_fr x y : finite (fiplus x y) -> finite y;
  fiplus_spec_f x y : finite x -> finite y ->
    Rabs (fplus (FI2F x) (FI2F y)) < m -> finite (fiplus x y);

  (** Multiplication. *)
  fimult : FI -> FI -> FI;

  fimult_spec x y : finite (fimult x y) ->
    FI2F (fimult x y) = fmult (FI2F x) (FI2F y) :> R;
  fimult_spec_fl x y : finite (fimult x y) -> finite x;
  fimult_spec_fr x y : finite (fimult x y) -> finite y;
  fimult_spec_f x y : finite x -> finite y ->
    Rabs (fmult (FI2F x) (FI2F y)) < m -> finite (fimult x y);

  (** Division. *)
  fidiv : FI -> FI -> FI;

  fidiv_spec x y : finite (fidiv x y) -> finite y ->
    FI2F (fidiv x y) = fdiv (FI2F x) (FI2F y) :> R;
  fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x;
  fidiv_spec_f x y : finite x -> (FI2F y <> 0 :> R) ->
    Rabs (fdiv (FI2F x) (FI2F y)) < m -> finite (fidiv x y);

  (** Square root. *)
  fisqrt : FI -> FI;

  fisqrt_spec x : finite (fisqrt x) -> FI2F (fisqrt x) = fsqrt (FI2F x) :> R;
  fisqrt_spec_f1 x : finite (fisqrt x) -> finite x;
  fisqrt_spec_f x : finite x -> FI2F x >= 0 -> finite (fisqrt x)
}.

Section Derived_spec.

Variable fs : Float_infnan_spec.

Lemma m_pos : 0 <= m fs.
Proof.
apply Rle_trans with 2; [|now apply m_ge_2].
rewrite <- (Rplus_0_l 0); apply Rplus_le_compat; apply Rle_0_1.
Qed.
       
(** Subtraction. *)
Definition fiminus (x y : FI fs) : FI fs := fiplus x (fiopp y).

Lemma fiminus_spec x y : finite (fiminus x y) ->
  FI2F (fiminus x y) = fminus (FI2F x) (FI2F y) :> R.
Proof.
unfold fiminus, fminus; intro H.
assert (Hy : finite (fiopp y)) by apply (fiplus_spec_fr H).
now unfold fplus; rewrite <- (fiopp_spec Hy); apply fiplus_spec.
Qed.

Lemma fiminus_spec_fl x y : finite (fiminus x y) -> finite x.
Proof. apply fiplus_spec_fl. Qed.

Lemma fiminus_spec_fr x y : finite (fiminus x y) -> finite y.
Proof. intro H; apply fiopp_spec_f1, (fiplus_spec_fr H). Qed.

Lemma fiminus_spec_f x y : finite x -> finite y ->
  Rabs (fminus (FI2F x) (FI2F y)) < m fs -> finite (fiminus x y).
Proof.
intros Fx Fy H; apply (fiplus_spec_f Fx (fiopp_spec_f Fy)).
now unfold fplus; rewrite fiopp_spec; [|apply fiopp_spec_f].
Qed.

End Derived_spec.
