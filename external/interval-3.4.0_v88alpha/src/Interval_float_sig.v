(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import ZArith.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.

Module Type FloatOps.

Parameter radix : radix.
Parameter even_radix : bool.
Parameter even_radix_correct : match radix_val radix with Zpos (xO _) => true | _ => false end = even_radix.
Parameter type : Type.
Parameter toF : type -> float radix.
Parameter toX : type -> ExtendedR.

Parameter precision : Type.
Parameter sfactor : Type.
Parameter prec : precision -> positive.
Parameter PtoP : positive -> precision.
Parameter ZtoS : Z -> sfactor.
Parameter StoZ : sfactor -> Z.

Parameter incr_prec : precision -> positive -> precision.

Parameter zero : type.
Parameter nan : type.
Parameter fromZ : Z -> type.
Parameter fromF : float radix -> type.
Parameter real : type -> bool.
Parameter mag : type -> sfactor.

Parameter cmp : type -> type -> Xcomparison.
Parameter min : type -> type -> type.
Parameter max : type -> type -> type.
Parameter round : rounding_mode -> precision -> type -> type.
Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter scale : type -> sfactor -> type.
Parameter scale2 : type -> sfactor -> type.
Parameter add_exact : type -> type -> type.
Parameter sub_exact : type -> type -> type.
Parameter mul_exact : type -> type -> type.
Parameter add : rounding_mode -> precision -> type -> type -> type.
Parameter sub : rounding_mode -> precision -> type -> type -> type.
Parameter mul : rounding_mode -> precision -> type -> type -> type.
Parameter div : rounding_mode -> precision -> type -> type -> type.
Parameter sqrt : rounding_mode -> precision -> type -> type.
Parameter nearbyint : rounding_mode -> type -> type.

Parameter toF_correct :
  forall x, FtoX (toF x) = toX x.

Parameter zero_correct : toX zero = Xreal 0.
Parameter nan_correct : toX nan = Xnan.
Parameter fromZ_correct :
  forall n, toX (fromZ n) = Xreal (IZR n).

Parameter real_correct :
  forall f,
  real f = match toX f with Xnan => false | _ => true end.

Parameter cmp_correct :
  forall x y, cmp x y = Xcmp (toX x) (toX y).

Parameter min_correct :
  forall x y, toX (min x y) = Xmin (toX x) (toX y).

Parameter max_correct :
  forall x y, toX (max x y) = Xmax (toX x) (toX y).

Parameter neg_correct :
  forall x, toX (neg x) = Xneg (toX x).

Parameter abs_correct :
  forall x, toX (abs x) = Xabs (toX x).

Parameter scale_correct :
  forall x d, toX (scale x (ZtoS d)) = Xmul (toX x) (Xreal (bpow radix d)).

Parameter scale2_correct :
  forall x d, even_radix = true ->
  toX (scale2 x (ZtoS d)) = Xmul (toX x) (Xreal (bpow radix2 d)).

Parameter add_exact_correct :
  forall x y, toX (add_exact x y) = Xadd (toX x) (toX y).

Parameter sub_exact_correct :
  forall x y, toX (sub_exact x y) = Xsub (toX x) (toX y).

Parameter mul_exact_correct :
  forall x y, toX (mul_exact x y) = Xmul (toX x) (toX y).

Parameter add_correct :
  forall mode p x y,
  toX (add mode p x y) = Xround radix mode (prec p) (Xadd (toX x) (toX y)).

Parameter sub_correct :
  forall mode p x y,
  toX (sub mode p x y) = Xround radix mode (prec p) (Xsub (toX x) (toX y)).

Parameter mul_correct :
  forall mode p x y,
  toX (mul mode p x y) = Xround radix mode (prec p) (Xmul (toX x) (toX y)).

Parameter div_correct :
  forall mode p x y,
  toX (div mode p x y) = Xround radix mode (prec p) (Xdiv (toX x) (toX y)).

Parameter sqrt_correct :
  forall mode p x,
  toX (sqrt mode p x) = Xround radix mode (prec p) (Xsqrt (toX x)).

Parameter nearbyint_correct :
  forall mode x,
  toX (nearbyint mode x) = Xnearbyint mode (toX x).

End FloatOps.

Module FloatExt (F : FloatOps).

Definition le x y :=
  match F.cmp x y with
  | Xlt | Xeq => true
  | Xgt | Xund => false
  end.

Lemma le_correct :
  forall x y,
  le x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr <= yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold le.
rewrite F.cmp_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Raux.Rcompare_spec ; auto with real.
Qed.

Definition lt x y :=
  match F.cmp x y with
  | Xlt  => true
  | _ => false
  end.

Lemma lt_correct :
  forall x y,
  lt x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr < yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold lt.
rewrite F.cmp_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Raux.Rcompare_spec.
Qed.

End FloatExt.
