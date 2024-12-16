(** * IEEE754 binary64 format satisfies hypothesis in [Float_spec] *)

(** Uses the Flocq library (http://flocq.gforge.inria.fr) to build a
    record [Float_spec] corresponding to IEEE754 binary64 format with
    a rounding to nearest. More precisely Flocq's FLT(-1074, 53) is a
    model of binary64 with gradual underflow but without NaNs nor
    overflows (which could be easily handled afterward). *)

Require binary64_infnan.

Definition binary64 : float_spec.Float_spec := float_infnan_spec.fis binary64_infnan.binary64_infnan.
