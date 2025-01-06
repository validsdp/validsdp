(** * IEEE754 binary64 format satisfies hypothesis in [Float_infnan_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_infnan_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest with overflows and NaN. *)
Require Import ZArith.
Require float_infnan_spec bsn_infnan.

Definition binary64_infnan : float_infnan_spec.Float_infnan_spec :=
   @bsn_infnan.bsn_infnan 53 1024 Logic.eq_refl Logic.eq_refl.
