(** * Specification of floating-point operations with overflow. *)

Require Import Reals Flocq.Core.Fcore.

Require Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.

Delimit Scope R_scope with Re.

Require Export float_spec.

Record Float_infnan_spec := {
  (** Type of floating-point values (either finite, infinite or NaN). *)
  FI : Type;

  FI0 : FI;
  FI1 : FI;
  
  (** [is_finite f = true] iff the floating-point number [f] is finite. *)
  is_finite : FI -> bool;

  finite (x : FI) : Prop := is_finite x = true;

  finite0 : finite FI0;
  finite1 : finite FI1;
  
  (** Underlying unbounded floating-point format.
      [FI] and [F fis] match when [finite] holds. *)
  fis :> Float_spec;

  (** Any float less than [m] (in absolute value) will be finite
      (typically, [m] can be the smallest non representable positive float). *)
  m : R;

  m_ge_2 : 2 <= m;
  
  (** Associates the corresponding value in [F fis] for finite values
      or [F0] for infinities and NaN. *)
  FI2F : FI -> F fis;

  FI2F_spec x : (FI2F x <> 0 :> R) -> finite x;
  FI2F0 : FI2F (FI0) = F0 fis :> R;
  FI2F1 : FI2F (FI1) = F1 fis :> R;
  
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
  fisqrt_spec_f x : finite x -> FI2F x >= 0 -> finite (fisqrt x);

  (** Comparison. *)
  ficompare : FI -> FI -> option comparison;

  ficompare_spec x y : finite x -> finite y ->
    ficompare x y = Some (Rcompare (FI2F x) (FI2F y));
  ficompare_spec_eq x y : ficompare x y = Some Eq -> FI2F x = FI2F y :> R;
  ficompare_spec_eq_f x y : ficompare x y = Some Eq -> (finite x <-> finite y)
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

(** Equality *)
Definition fieq (x y : FI fs) : bool :=
  match ficompare x y with
    | Some Eq => true
    | _ => false
  end.

Lemma fieq_spec x y : fieq x y = true -> FI2F x = FI2F y :> R.
Proof.
intro H; apply ficompare_spec_eq; revert H; unfold fieq.
now case (ficompare _ _); [intro c; case c|].
Qed.

Lemma fieq_spec_f x y : fieq x y = true -> (finite x <-> finite y).
Proof.
unfold fieq; set (c := ficompare _ _); case_eq c; [|now simpl].
intros c' Hc; case_eq c'; [|now simpl|now simpl]; intros Hc' _.
now apply ficompare_spec_eq_f; rewrite <-Hc', <-Hc.
Qed.

(** Comparison *)
Definition filt (x y : FI fs) : bool :=
  match ficompare x y with
    | Some Lt => true
    | _ => false
  end.

Lemma filt_spec x y : finite x -> finite y -> filt x y = true ->
  FI2F x < FI2F y.
Proof.
intros Fx Fy; unfold filt; rewrite (ficompare_spec Fx Fy).
now case_eq (Rcompare (FI2F x) (FI2F y)); [|intros H _; apply Rcompare_Lt_inv|].
Qed.

(** [filt x y] can differ from [not (file y x)] because of NaNs. *)
Definition file (x y : FI fs) : bool :=
  match ficompare x y with
    | Some Lt => true
    | Some Eq => true
    | _ => false
  end.

Lemma file_spec x y : finite x -> finite y -> file x y = true ->
  FI2F x <= FI2F y.
Proof.
intros Fx Fy; unfold file; rewrite (ficompare_spec Fx Fy).
case_eq (Rcompare (FI2F x) (FI2F y)); [| |now simpl].
{ now intros H _; right; apply Rcompare_Eq_inv. }
now intros H _; left; apply Rcompare_Lt_inv.
Qed.

Definition fimax x y := if file x y then y else x.

Lemma fimax_spec_lel x y : finite x -> finite y -> FI2F x <= FI2F (fimax x y).
Proof.
intros Fx Fy; unfold fimax, file; rewrite (ficompare_spec Fx Fy).
case_eq (Rcompare (FI2F x) (FI2F y)); intro H.
{ now right; apply Rcompare_Eq_inv. }
{ now left; apply Rcompare_Lt_inv. }
apply Rle_refl.
Qed.

Lemma fimax_spec_ler x y : finite x -> finite y -> FI2F y <= FI2F (fimax x y).
Proof.
intros Fx Fy; unfold fimax, file; rewrite (ficompare_spec Fx Fy), Rcompare_sym.
unfold CompOpp; case_eq (Rcompare (FI2F y) (FI2F x)); intro H.
{ apply Rle_refl. }
{ now left; apply Rcompare_Lt_inv. }
apply Rle_refl.
Qed.

Lemma fimax_spec_eq x y : fimax x y = x \/ fimax x y = y.
Proof. now unfold fimax; case (file x y); [right|left]. Qed.

Lemma fimax_spec_f x y : finite x -> finite y -> finite (fimax x y).
Proof. by case (fimax_spec_eq x y) => H; rewrite H. Qed.

End Derived_spec.

Record Float_round_up_infnan_spec := {
  (** Underlying floating-point format. *)
  fris :> Float_infnan_spec;

  (** Overapproximation of eps. *)
  fieps : FI fris;

  fieps_spec : eps fris <= FI2F fieps;
  
  (** Overapproximation of eta. *)
  fieta : FI fris;

  fieta_spec : eta fris <= FI2F fieta;
  
  (** Addition with upward rounding. *)
  fiplus_up : FI fris -> FI fris -> FI fris;

  fiplus_up_spec x y : finite (fiplus_up x y) ->
    (FI2F x + FI2F y <= FI2F (fiplus_up x y))%R;
  fiplus_up_spec_fl x y : finite (fiplus_up x y) -> finite x;
  fiplus_up_spec_fr x y : finite (fiplus_up x y) -> finite y;
  
  (** Multiplication with upward rounding. *)
  fimult_up : FI fris -> FI fris -> FI fris;

  fimult_up_spec x y : finite (fimult_up x y) ->
    (FI2F x * FI2F y <= FI2F (fimult_up x y))%R;
  fimult_up_spec_fl x y : finite (fimult_up x y) -> finite x;
  fimult_up_spec_fr x y : finite (fimult_up x y) -> finite y;
  
  (** Division with upward rounding. *)
  fidiv_up : FI fris -> FI fris -> FI fris;

  fidiv_up_spec x y : finite (fidiv_up x y) -> finite y ->
    (FI2F x / FI2F y <= FI2F (fidiv_up x y))%R;
  fidiv_up_spec_fl x y : finite (fidiv_up x y) -> finite y -> finite x
}.

Section Derived_up_spec.

Variable fs : Float_round_up_infnan_spec.

(** get a float overapprox of n *)
Definition float_of_nat_up n := iter n (fun x => fiplus_up x (FI1 fs)) (FI0 fs).

Lemma float_of_nat_up_spec k : finite (float_of_nat_up k) ->
  INR k <= FI2F (float_of_nat_up k).
Proof.
induction k; [by intros _; rewrite FI2F0; right|].
intros Fa; rewrite S_INR; simpl.
apply (Rle_trans _ (FI2F (float_of_nat_up k) + FI2F (FI1 fs))).
{ rewrite FI2F1; apply Rplus_le_compat_r, IHk.
  revert Fa; apply fiplus_up_spec_fl. }
by apply fiplus_up_spec.
Qed.

Definition fiminus_down (x y : FI fs) := (fiopp (fiplus_up y (fiopp x))).

Lemma fiminus_down_spec x y : finite (fiminus_down x y) ->
  FI2F (fiminus_down x y) <= FI2F x - FI2F y.
Proof.
intros Fxy; unfold fiminus_down.
rewrite (fiopp_spec Fxy), <-Ropp_minus_distr; apply Ropp_le_contravar.
assert (Fxy' : finite (fiplus_up y (fiopp x))); [by apply fiopp_spec_f1|].
apply (Rle_trans _ (FI2F y + FI2F (fiopp x))); [|by apply fiplus_up_spec].
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
