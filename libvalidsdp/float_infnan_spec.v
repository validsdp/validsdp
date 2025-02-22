(** * Specification of floating-point operations with overflow. *)

Require Import Reals Floats Flocq.Core.Core.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Require Export float_spec.

Record Float_infnan_spec := {
  (** Type of floating-point values (either finite, infinite or NaN). *)
  FIS : Type;

  FIS0 : FIS;
  FIS1 : FIS;

  (** [finite f = true] iff the floating-point number [f] is finite. *)
  finite : FIS -> bool;

  finite0 : finite FIS0;
  finite1 : finite FIS1;

  (** Underlying unbounded floating-point format.
      [FIS] and [FS fis] match when [finite] holds. *)
  fis :> Float_spec;

  (** Any float less than [m] (in absolute value) will be finite
      (typically, [m] can be the smallest non representable positive float). *)
  m : R;

  m_ge_2 : 2 <= m;

  (** Associates the corresponding value in [F fis] for finite values
      or [F0] for infinities and NaN. *)
  FIS2FS : FIS -> FS fis;

  FIS2FS_spec x : (FIS2FS x <> 0 :> R) -> finite x;
  FIS2FS0 : FIS2FS (FIS0) = F0 fis :> R;
  FIS2FS1 : FIS2FS (FIS1) = F1 fis :> R;

  (** Some rounding. *)
  firnd : R -> FIS;

  firnd_spec x : finite (firnd x) -> FIS2FS (firnd x) = frnd fis x :> R;
  firnd_spec_f x : Rabs (frnd fis x) < m -> finite (firnd x);

  (** Opposite. *)
  fiopp : FIS -> FIS;

  fiopp_spec x : finite (fiopp x) -> FIS2FS (fiopp x) = fopp (FIS2FS x) :> R;
  fiopp_spec_f1 x : finite (fiopp x) -> finite x;
  fiopp_spec_f x : finite x -> finite (fiopp x);

  (** Addition. *)
  fiplus : FIS -> FIS -> FIS;

  fiplus_spec x y : finite (fiplus x y) ->
    FIS2FS (fiplus x y) = fplus (FIS2FS x) (FIS2FS y) :> R;
  fiplus_spec_fl x y : finite (fiplus x y) -> finite x;
  fiplus_spec_fr x y : finite (fiplus x y) -> finite y;
  fiplus_spec_f x y : finite x -> finite y ->
    Rabs (fplus (FIS2FS x) (FIS2FS y)) < m -> finite (fiplus x y);

  (** Subtraction. *)
  fiminus : FIS -> FIS -> FIS;

  fiminus_spec x y : finite (fiminus x y) ->
    FIS2FS (fiminus x y) = fminus (FIS2FS x) (FIS2FS y) :> R;
  fiminus_spec_fl x y : finite (fiminus x y) -> finite x;
  fiminus_spec_fr x y : finite (fiminus x y) -> finite y;
  fiminus_spec_f x y : finite x -> finite y ->
    Rabs (fminus (FIS2FS x) (FIS2FS y)) < m -> finite (fiminus x y);

  (** Multiplication. *)
  fimult : FIS -> FIS -> FIS;

  fimult_spec x y : finite (fimult x y) ->
    FIS2FS (fimult x y) = fmult (FIS2FS x) (FIS2FS y) :> R;
  fimult_spec_fl x y : finite (fimult x y) -> finite x;
  fimult_spec_fr x y : finite (fimult x y) -> finite y;
  fimult_spec_f x y : finite x -> finite y ->
    Rabs (fmult (FIS2FS x) (FIS2FS y)) < m -> finite (fimult x y);

  (** Division. *)
  fidiv : FIS -> FIS -> FIS;

  fidiv_spec x y : finite (fidiv x y) -> finite y ->
    FIS2FS (fidiv x y) = fdiv (FIS2FS x) (FIS2FS y) :> R;
  fidiv_spec_fl x y : finite (fidiv x y) -> finite y -> finite x;
  fidiv_spec_f x y : finite x -> (FIS2FS y <> 0 :> R) ->
    Rabs (fdiv (FIS2FS x) (FIS2FS y)) < m -> finite (fidiv x y);

  (** Square root. *)
  fisqrt : FIS -> FIS;

  fisqrt_spec x : finite (fisqrt x) -> FIS2FS (fisqrt x) = fsqrt (FIS2FS x) :> R;
  fisqrt_spec_f1 x : finite (fisqrt x) -> finite x;
  fisqrt_spec_f x : finite x -> FIS2FS x >= 0 -> finite (fisqrt x);

  (** Comparison. *)
  ficompare : FIS -> FIS -> float_comparison;

  ficompare_spec x y : finite x -> finite y ->
    ficompare x y = flatten_cmp_opt (Some (Rcompare (FIS2FS x) (FIS2FS y)));
  ficompare_spec_eq x y : ficompare x y = FEq -> FIS2FS x = FIS2FS y :> R;
  ficompare_spec_eq_f x y : ficompare x y = FEq -> (finite x <-> finite y)
}.

Section Derived_spec.

Variable fs : Float_infnan_spec.

Lemma m_pos : 0 <= m fs.
Proof.
apply Rle_trans with 2; [|now apply m_ge_2].
rewrite <- (Rplus_0_l 0); apply Rplus_le_compat; apply Rle_0_1.
Qed.

(** Equality *)
Definition fieq (x y : FIS fs) : bool :=
  match ficompare x y with
    | FEq => true
    | _ => false
  end.

Lemma fieq_spec x y : fieq x y = true -> FIS2FS x = FIS2FS y.
Proof.
intro H; apply val_inj, ficompare_spec_eq; revert H; unfold fieq.
now case (ficompare _ _).
Qed.

Lemma fieq_spec_f x y : fieq x y = true -> (finite x <-> finite y).
Proof.
unfold fieq; set (c := ficompare _ _); case_eq c; try discriminate.
now intros Hc _; apply ficompare_spec_eq_f.
Qed.

(** Comparison *)
Definition filt (x y : FIS fs) : bool :=
  match ficompare x y with
    | FLt => true
    | _ => false
  end.

Lemma filt_spec x y : finite x -> finite y -> filt x y = true ->
  FIS2FS x < FIS2FS y.
Proof.
intros Fx Fy; unfold filt; rewrite (ficompare_spec Fx Fy).
now case_eq (Rcompare (FIS2FS x) (FIS2FS y)); [|intros H _; apply Rcompare_Lt_inv|].
Qed.

(** [filt x y] can differ from [not (file y x)] because of NaNs. *)
Definition file (x y : FIS fs) : bool :=
  match ficompare x y with
    | FLt => true
    | FEq => true
    | _ => false
  end.

Lemma file_spec x y : finite x -> finite y -> file x y = true ->
  FIS2FS x <= FIS2FS y.
Proof.
intros Fx Fy; unfold file; rewrite (ficompare_spec Fx Fy).
case_eq (Rcompare (FIS2FS x) (FIS2FS y)); [| |now simpl].
{ now intros H _; right; apply Rcompare_Eq_inv. }
now intros H _; left; apply Rcompare_Lt_inv.
Qed.

Definition fimax (x y : FIS fs) :=
  match ficompare y x with
  | FLt | FEq => x
  | _ => y
  end.

Lemma fimax_spec_lel x y : finite x -> finite y -> FIS2FS x <= FIS2FS (fimax x y).
Proof.
intros Fx Fy; unfold fimax; rewrite (ficompare_spec Fy Fx).
case_eq (Rcompare (FIS2FS y) (FIS2FS x)); intro H; try apply Rle_refl.
now left; apply Rcompare_Gt_inv.
Qed.

Lemma fimax_spec_ler x y : finite x -> finite y -> FIS2FS y <= FIS2FS (fimax x y).
Proof.
intros Fx Fy; unfold fimax, file; rewrite (ficompare_spec Fy Fx).
case_eq (Rcompare (FIS2FS y) (FIS2FS x)); intro H.
{ now right; apply Rcompare_Eq_inv. }
{ now left; apply Rcompare_Lt_inv. }
apply Rle_refl.
Qed.

Lemma fimax_spec_eq x y : fimax x y = x \/ fimax x y = y.
Proof.
unfold fimax.
now case (ficompare y x); [left|left|right|right].
Qed.

Lemma fimax_spec_f x y : finite x -> finite y -> finite (fimax x y).
Proof. by case (fimax_spec_eq x y) => H; rewrite H. Qed.

End Derived_spec.

Record Float_round_up_infnan_spec := {
  (** Underlying floating-point format. *)
  fris :> Float_infnan_spec;

  (** Overapproximation of eps. *)
  fieps : FIS fris;

  fieps_spec : eps fris <= FIS2FS fieps;

  (** Overapproximation of eta. *)
  fieta : FIS fris;

  fieta_spec : eta fris <= FIS2FS fieta;

  (** Addition with upward rounding. *)
  fiplus_up : FIS fris -> FIS fris -> FIS fris;

  fiplus_up_spec x y : finite (fiplus_up x y) ->
    (FIS2FS x + FIS2FS y <= FIS2FS (fiplus_up x y))%R;
  fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x;
  fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y;

  (** Multiplication with upward rounding. *)
  fimult_up : FIS fris -> FIS fris -> FIS fris;

  fimult_up_spec x y : finite (fimult_up x y) ->
    (FIS2FS x * FIS2FS y <= FIS2FS (fimult_up x y))%R;
  fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x;
  fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y;

  (** Division with upward rounding. *)
  fidiv_up : FIS fris -> FIS fris -> FIS fris;

  fidiv_up_spec x y : finite (fidiv_up x y) -> finite y ->
    (FIS2FS x / FIS2FS y <= FIS2FS (fidiv_up x y))%R;
  fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x
}.

Section Derived_up_spec.

Variable fs : Float_round_up_infnan_spec.

(** get a float overapprox of n *)
Definition float_of_nat_up n := Init.Nat.iter n (fun x => fiplus_up x (FIS1 fs)) (FIS0 fs).

Lemma float_of_nat_up_spec k : finite (float_of_nat_up k) ->
  INR k <= FIS2FS (float_of_nat_up k).
Proof.
induction k; [by intros _; rewrite FIS2FS0; right|].
intros Fa; rewrite S_INR; simpl.
apply (Rle_trans _ (FIS2FS (float_of_nat_up k) + FIS2FS (FIS1 fs))).
{ rewrite FIS2FS1; apply Rplus_le_compat_r, IHk.
  revert Fa; apply fiplus_up_spec_fl. }
by apply fiplus_up_spec.
Qed.

Definition fiminus_down (x y : FIS fs) := (fiopp (fiplus_up y (fiopp x))).

Lemma fiminus_down_spec x y : finite (fiminus_down x y) ->
  FIS2FS (fiminus_down x y) <= FIS2FS x - FIS2FS y.
Proof.
intros Fxy.
rewrite (fiopp_spec Fxy) -Ropp_minus_distr; apply Ropp_le_contravar.
assert (Fxy' : finite (fiplus_up y (fiopp x))); [by apply fiopp_spec_f1|].
apply (Rle_trans _ (FIS2FS y + FIS2FS (fiopp x))); [|by apply fiplus_up_spec].
apply Rplus_le_compat_l.
by rewrite (fiopp_spec (fiplus_up_spec_fr Fxy')); right.
Qed.

Lemma fiminus_down_spec_fl x y : finite (fiminus_down x y) -> finite x.
Proof.
by intro H; apply fiopp_spec_f1, fiplus_up_spec_fr, fiopp_spec_f1 in H.
Qed.

Lemma fiminus_down_spec_fr x y : finite (fiminus_down x y) -> finite y.
Proof. by intro H; apply fiopp_spec_f1, fiplus_up_spec_fl in H. Qed.

End Derived_up_spec.
