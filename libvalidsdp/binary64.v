(** * IEEE754 binary64 format satisfies hypothesis in [Float_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLT(-1074, 53) is a
    model of binary64 with gradual underflow but without NaNs nor
    overflows (which could be easily handled afterward). *)

Require Import Reals mathcomp.analysis.Rstruct Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype.

Require Import Flocq.Core.Zaux.
Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Prop.Relative.
Require Import Flocq.Prop.Plus_error.
Require Import Flocq.Prop.Div_sqrt_error.

Require Import bounded.
Require Import float_spec.
Require flx64.

Require Import float_spec.
Require flx64.

#[global] Obligation Tactic := idtac.  (* no automatic intro *)

Open Scope R_scope.

Section Binary64.

Let prec := 53%Z.
Let emax := 1024%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.

Lemma Pprec : (0 < prec)%Z.
Proof. now compute. Qed.

Instance valid_exp : Valid_exp fexp.
Proof. now apply FLT_exp_valid. Qed.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition generic_format_pred (x : R) : bool :=
  x == @F2R radix2
            {| Fnum := Ztrunc (scaled_mantissa radix2 fexp x);
               Fexp := cexp radix2 fexp x |}.

Definition format x := generic_format_pred x.

Let F := FS_of format.

Lemma format0 : format 0.
Proof. apply /eqP /generic_format_0. Qed.

Lemma format1 : format 1.
Proof. now apply /eqP; apply generic_format_FLT_1. Qed.

Lemma format_opp x : format x -> format (- x).
Proof. by move /eqP => ?; apply /eqP; apply generic_format_opp. Qed.

Definition eps := bpow radix2 (-53).

Lemma eps_pos : 0 <= eps.
Proof. apply bpow_ge_0. Qed.

Lemma eps_lt_1 : eps < 1.
Proof.
unfold eps, bpow.
apply (Rmult_lt_reg_r (IZR (Z.pow_pos radix2 53)));
  [now fold (bpow radix2 53); apply bpow_gt_0|].
rewrite Rinv_l; [rewrite Rmult_1_l|now apply Rgt_not_eq, Rlt_gt;
                                    fold (bpow radix2 53); apply bpow_gt_0].
change 1 with (IZR 1); apply IZR_lt.
unfold Z.pow_pos; simpl.
now compute.
Qed.

Let b_eps := bounded eps.
Let b_epsd1peps := bounded (eps / (1 + eps)).

Definition eta := bpow radix2 (-1075).

Lemma eta_pos : 0 <= eta.
Proof. apply bpow_ge_0. Qed.

Let b_eta := bounded eta.

(** The tie-break rule doesn't really matter. *)
Variable choice : Z -> bool.

(** All we need is rounding to nearest. *)
Program Definition frnd (x : R) : F :=
  @Build_FS_of _ (round radix2 fexp (Znearest choice) x) _.
Next Obligation.
move=> x; apply/eqP.
now apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
Qed.

Lemma frnd_F (x : F) : frnd x = x.
apply val_inj => /=.
by apply round_generic; [apply valid_rnd_N|apply /eqP; case x].
Qed.

Lemma frnd_spec (x : R) :
  exists (d : b_epsd1peps) (e : b_eta),
    round radix2 fexp (Znearest choice) x = (1 + d) * x + e :> R
    /\ d * e = 0.
Proof.
destruct (@relative_error_N_FLT'_ex radix2 emin _ Pprec choice x)
  as (d, (e, (Hd, (He, (Hde, Hr))))).
replace (u_ro _ _) with eps in Hd;
  [|now unfold u_ro, eps; change (/2) with (bpow radix2 (-1));
    rewrite <-bpow_plus].
replace (_ * _) with eta in He;
  [|now unfold eta; change (/2) with (bpow radix2 (-1));
    rewrite <-bpow_plus].
exists (Build_bounded Hd), (Build_bounded He); simpl.
now rewrite Hde Rmult_comm.
Qed.

Lemma fplus_spec (x y : F) :
  exists d : b_epsd1peps, frnd (x + y) = (1 + d) * (x + y) :> R.
Proof.
move: x => [x /= /eqP fx]; move: y => [y /= /eqP fy].
destruct (@FLT_plus_error_N_ex radix2 emin _ Pprec choice _ _ fx fy)
  as (d, (Hd, Hr)).
replace (u_ro _ _) with eps in Hd;
  [|now unfold u_ro, eps; change (/2) with (bpow radix2 (-1));
    rewrite <-bpow_plus].
exists (Build_bounded Hd); simpl.
now rewrite Rmult_comm.
Qed.

Lemma fplus_spec_l (x y : F) : Rabs (frnd (x + y) - (x + y)) <= Rabs x.
Proof.
by apply plus_error_le_l; [apply FLT_exp_valid|apply /eqP..]; [|case x|case y].
Qed.

Lemma fplus_spec2 (x y : F) : y <= 0 -> frnd (x + y) <= x.
Proof.
intros Hy.
unfold frnd; simpl.
rewrite <- (round_generic radix2 fexp (Znearest choice) x) at 2;
  [|now apply /eqP; case x].
now apply round_le; [apply FLT_exp_valid|apply valid_rnd_N|lra].
Qed.

Lemma fmult_spec2 x : 0 <= frnd (x * x).
Proof.
unfold fmult, frnd; simpl.
rewrite <- (round_0 radix2 fexp (Znearest choice)).
apply round_le; [now apply FLT_exp_valid|now apply valid_rnd_N|].
apply misc.sqr_ge_0.
Qed.

Lemma fsqrt_spec (x : F) :
  exists d : bounded (1 - 1 / sqrt (1 + 2 * eps)),
    frnd (sqrt x) = (1 + d) * (sqrt x) :> R.
Proof.
assert (Hprec1 : (1 < prec)%Z); [now simpl|].
assert (Hemin : (emin <= 2 * (1 - prec))%Z); [now simpl|].
move: x => [x /= /eqP fx].
destruct (@sqrt_error_N_FLT_ex radix2 _ Pprec choice Hprec1 _ Hemin _ fx)
  as (d, (Hd, Hr)).
replace (u_ro _ _) with eps in Hd;
  [|now unfold eps, u_ro; change (/ 2) with (bpow radix2 (-1));
    rewrite <-bpow_plus].
now exists (Build_bounded Hd); simpl; rewrite Rmult_comm.
Qed.

Definition binary64 : Float_spec :=
  @Build_Float_spec
    format
    format0
    format1
    format_opp
    eps
    eps_pos
    eps_lt_1
    eta
    eta_pos
    frnd
    frnd_F
    frnd_spec
    fplus_spec
    fplus_spec_l
    fplus_spec2
    fmult_spec2
    fsqrt_spec.

End Binary64.
