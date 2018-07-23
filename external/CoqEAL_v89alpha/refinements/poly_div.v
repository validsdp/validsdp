(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import param refinements hrel poly_op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Section generic_division.

Variable N R polyR : Type.
Context `{lt_of N, sub_of N, add_of N, one_of N, zero_of N, spec_of N nat}.
Context `{size_of polyR N, lead_coef_of R polyR, cast_of R polyR}.
Context `{shift_of polyR N, add_of polyR, mul_of polyR, sub_of polyR}.
Context `{eq_of polyR, zero_of polyR}.

Definition div_rec_poly (q : polyR) :=
  let sq := (size_op q : N) in
  let cq := (cast (lead_coef_op q : R) : polyR) in
  fix loop (k : N) (qq r : polyR) (n : nat) {struct n} :=
    if (size_op r < sq)%C
    then (k, qq, r) else
      let m := shift_op (size_op r - sq)%C
                        (cast (lead_coef_op r : R) : polyR) in
      let qq1 := (qq * cq + m)%C in
      let r1 := (r * cq - m * q)%C in
      if n is n1.+1 then loop (k + 1)%C qq1 r1 n1 else ((k + 1)%C, qq1, r1).

Global Instance div_poly : div_of polyR :=
  fun p q => (if (q == 0)%C
                 then (0%C, 0%C, p)
                 else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).1.2.

Global Instance mod_poly : mod_of polyR :=
  fun p q => (if (q == 0)%C
                 then (0%C, 0%C, p)
                 else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).2.

Global Instance scal_poly : scal_of polyR N :=
  fun p q => (if (q == 0)%C then (0%C, 0%C, p)
              else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).1.1.

End generic_division.

Definition div_rec_poly_R      : forall (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) 
         (R₁ R₂ : Type) (R_R : forall (_ : R₁) (_ : R₂), Type) 
         (polyR₁ polyR₂ : Type) (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type)
         (H₁ : lt_of N₁) (H₂ : lt_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂)
         (H0₁ : sub_of N₁) (H0₂ : sub_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂)
         (H1₁ : add_of N₁) (H1₂ : add_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂)
         (H2₁ : one_of N₁) (H2₂ : one_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H2₁ H2₂) (H5₁ : size_of polyR₁ N₁) (H5₂ : size_of polyR₂ N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
         (H6₂ : lead_coef_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                 (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
               forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2))
                R₁ R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
         (H7₂ : cast_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R
                polyR₁ polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁)
         (H8₂ : shift_of polyR₂ N₂)
         (_ : (fun (polyA₁ polyA₂ : Type)
                 (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
                 (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
               forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
                 (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁)
         (H9₂ : add_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H9₁ H9₂) (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H10₁ H10₂) (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H11₁ H11₂) (q₁ : polyR₁) (q₂ : polyR₂) (_ : polyR_R q₁ q₂) 
         (k₁ : N₁) (k₂ : N₂) (_ : N_R k₁ k₂) (qq₁ : polyR₁) (qq₂ : polyR₂)
         (_ : polyR_R qq₁ qq₂) (r₁ : polyR₁) (r₂ : polyR₂) (_ : polyR_R r₁ r₂)
         (n₁ n₂ : nat) (_ : nat_R n₁ n₂),
       @prod_R (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R)
         polyR₁ polyR₂ polyR_R
         (@div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁ k₁ qq₁
            r₁ n₁)
         (@div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂ k₂ qq₂
            r₂ n₂)
 := 
fun (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) (R₁ R₂ : Type)
  (R_R : forall (_ : R₁) (_ : R₂), Type) (polyR₁ polyR₂ : Type)
  (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type) (H₁ : lt_of N₁) 
  (H₂ : lt_of N₂)
  (H_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
            (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
          forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
          bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂) (H0₁ : sub_of N₁) 
  (H0₂ : sub_of N₂)
  (H0_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂) (H1₁ : add_of N₁) 
  (H1₂ : add_of N₂)
  (H1_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂) (H2₁ : one_of N₁) 
  (H2₂ : one_of N₂)
  (H2_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H2₁
            H2₂) (H5₁ : size_of polyR₁ N₁) (H5₂ : size_of polyR₂ N₂)
  (H5_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
  (H6₂ : lead_coef_of R₂ polyR₂)
  (H6_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
           forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2)) R₁
            R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
  (H7₂ : cast_of R₂ polyR₂)
  (H7_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R polyR₁
            polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁) 
  (H8₂ : shift_of polyR₂ N₂)
  (H8_R : (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
             (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
           forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
             (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁) (H9₂ : add_of polyR₂)
  (H9_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H9₁ H9₂) 
  (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
  (H10_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H10₁ H10₂)
  (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
  (H11_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H11₁ H11₂) 
  (q₁ : polyR₁) (q₂ : polyR₂) (q_R : polyR_R q₁ q₂) =>
let sq₁ : N₁ := @size_op polyR₁ N₁ H5₁ q₁ : N₁ in
let sq₂ : N₂ := @size_op polyR₂ N₂ H5₂ q₂ : N₂ in
let sq_R : N_R sq₁ sq₂ :=
  (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (N₁0 N₂0 : Type)
     (N_R0 : forall (_ : N₁0) (_ : N₂0), Type) (size_of₁ : size_of A₁ N₁0)
     (size_of₂ : size_of A₂ N₂0)
     (size_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                     (N₁1 N₂1 : Type) (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                     (H : forall _ : A₁0, N₁1) (H0 : forall _ : A₂0, N₂1) =>
                   forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2), N_R1 (H H1) (H0 H2)) A₁
                    A₂ A_R N₁0 N₂0 N_R0 size_of₁ size_of₂) => size_of_R) polyR₁ polyR₂
    polyR_R N₁ N₂ N_R H5₁ H5₂ H5_R q₁ q₂ q_R
  :
  N_R (@size_op polyR₁ N₁ H5₁ q₁) (@size_op polyR₂ N₂ H5₂ q₂) in
let cq₁ : polyR₁ := @cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ q₁ : R₁) : polyR₁
  in
let cq₂ : polyR₂ := @cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ q₂ : R₂) : polyR₂
  in
let cq_R : polyR_R cq₁ cq₂ :=
  (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
     (B_R : forall (_ : B₁) (_ : B₂), Type) (cast_of₁ : cast_of A₁ B₁)
     (cast_of₂ : cast_of A₂ B₂)
     (cast_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                     (B₁0 B₂0 : Type) (B_R0 : forall (_ : B₁0) (_ : B₂0), Type)
                     (H : forall _ : A₁0, B₁0) (H0 : forall _ : A₂0, B₂0) =>
                   forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2), B_R0 (H H1) (H0 H2)) A₁
                    A₂ A_R B₁ B₂ B_R cast_of₁ cast_of₂) => cast_of_R) R₁ R₂ R_R polyR₁
    polyR₂ polyR_R H7₁ H7₂ H7_R (@lead_coef_op R₁ polyR₁ H6₁ q₁ : R₁)
    (@lead_coef_op R₂ polyR₂ H6₂ q₂ : R₂)
    ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
        (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
        (lead_coef_of₁ : lead_coef_of A₁ polyA₁) (lead_coef_of₂ : lead_coef_of A₂ polyA₂)
        (lead_coef_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             (polyA₁0 polyA₂0 : Type)
                             (polyA_R0 : forall (_ : polyA₁0) (_ : polyA₂0), Type)
                             (H : forall _ : polyA₁0, A₁0) (H0 : forall _ : polyA₂0, A₂0)
                           =>
                           forall (H1 : polyA₁0) (H2 : polyA₂0) (_ : polyA_R0 H1 H2),
                           A_R0 (H H1) (H0 H2)) A₁ A₂ A_R polyA₁ polyA₂ polyA_R
                            lead_coef_of₁ lead_coef_of₂) => lead_coef_of_R) R₁ R₂ R_R
       polyR₁ polyR₂ polyR_R H6₁ H6₂ H6_R q₁ q₂ q_R
     :
     R_R (@lead_coef_op R₁ polyR₁ H6₁ q₁) (@lead_coef_op R₂ polyR₂ H6₂ q₂))
  :
  polyR_R (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ q₁ : R₁))
    (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ q₂ : R₂)) in
let fix_loop_1 :
  forall (_ : N₁) (_ : polyR₁) (_ : polyR₁) (_ : nat), prod (prod N₁ polyR₁) polyR₁ :=
  fix loop (k : N₁) (qq r : polyR₁) (n : nat) {struct n} : prod (prod N₁ polyR₁) polyR₁ :=
    match
      @lt_op N₁ H₁ (@size_op polyR₁ N₁ H5₁ r) sq₁ return (prod (prod N₁ polyR₁) polyR₁)
    with
    | true => @pair (prod N₁ polyR₁) polyR₁ (@pair N₁ polyR₁ k qq) r
    | false =>
        let m : polyR₁ :=
          @shift_op polyR₁ N₁ H8₁ (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r) sq₁)
            (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r : R₁) : polyR₁) in
        let qq1 : polyR₁ := @add_op polyR₁ H9₁ (@mul_op polyR₁ H10₁ qq cq₁) m in
        let r1 : polyR₁ :=
          @sub_op polyR₁ H11₁ (@mul_op polyR₁ H10₁ r cq₁) (@mul_op polyR₁ H10₁ m q₁) in
        match n return (prod (prod N₁ polyR₁) polyR₁) with
        | O =>
            @pair (prod N₁ polyR₁) polyR₁
              (@pair N₁ polyR₁ (@add_op N₁ H1₁ k (@one_op N₁ H2₁)) qq1) r1
        | S n1 => loop (@add_op N₁ H1₁ k (@one_op N₁ H2₁)) qq1 r1 n1
        end
    end in
let fix_loop_2 :
  forall (_ : N₂) (_ : polyR₂) (_ : polyR₂) (_ : nat), prod (prod N₂ polyR₂) polyR₂ :=
  fix loop (k : N₂) (qq r : polyR₂) (n : nat) {struct n} : prod (prod N₂ polyR₂) polyR₂ :=
    match
      @lt_op N₂ H₂ (@size_op polyR₂ N₂ H5₂ r) sq₂ return (prod (prod N₂ polyR₂) polyR₂)
    with
    | true => @pair (prod N₂ polyR₂) polyR₂ (@pair N₂ polyR₂ k qq) r
    | false =>
        let m : polyR₂ :=
          @shift_op polyR₂ N₂ H8₂ (@sub_op N₂ H0₂ (@size_op polyR₂ N₂ H5₂ r) sq₂)
            (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r : R₂) : polyR₂) in
        let qq1 : polyR₂ := @add_op polyR₂ H9₂ (@mul_op polyR₂ H10₂ qq cq₂) m in
        let r1 : polyR₂ :=
          @sub_op polyR₂ H11₂ (@mul_op polyR₂ H10₂ r cq₂) (@mul_op polyR₂ H10₂ m q₂) in
        match n return (prod (prod N₂ polyR₂) polyR₂) with
        | O =>
            @pair (prod N₂ polyR₂) polyR₂
              (@pair N₂ polyR₂ (@add_op N₂ H1₂ k (@one_op N₂ H2₂)) qq1) r1
        | S n1 => loop (@add_op N₂ H1₂ k (@one_op N₂ H2₂)) qq1 r1 n1
        end
    end in
fix
loop_R (k₁ : N₁) (k₂ : N₂) (k_R : N_R k₁ k₂) (qq₁ : polyR₁) (qq₂ : polyR₂)
       (qq_R : polyR_R qq₁ qq₂) (r₁ : polyR₁) (r₂ : polyR₂) (r_R : polyR_R r₁ r₂)
       (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  @prod_R (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R)
    polyR₁ polyR₂ polyR_R (fix_loop_1 k₁ qq₁ r₁ n₁) (fix_loop_2 k₂ qq₂ r₂ n₂) :=
  let gen_path :
    forall (N R polyR : Type) (H : lt_of N) (H0 : sub_of N) (H1 : add_of N) 
      (H2 : one_of N) (H5 : size_of polyR N) (H6 : lead_coef_of R polyR)
      (H7 : cast_of R polyR) (H8 : shift_of polyR N) (H9 : add_of polyR)
      (H10 : mul_of polyR) (H11 : sub_of polyR) (q : polyR),
    let sq : N := @size_op polyR N H5 q : N in
    let cq : polyR := @cast_op R polyR H7 (@lead_coef_op R polyR H6 q : R) : polyR in
    let
      fix loop (k : N) (qq r : polyR) (n : nat) {struct n} : prod (prod N polyR) polyR :=
        match @lt_op N H (@size_op polyR N H5 r) sq return (prod (prod N polyR) polyR) with
        | true => @pair (prod N polyR) polyR (@pair N polyR k qq) r
        | false =>
            let m : polyR :=
              @shift_op polyR N H8 (@sub_op N H0 (@size_op polyR N H5 r) sq)
                (@cast_op R polyR H7 (@lead_coef_op R polyR H6 r : R) : polyR) in
            let qq1 : polyR := @add_op polyR H9 (@mul_op polyR H10 qq cq) m in
            let r1 : polyR :=
              @sub_op polyR H11 (@mul_op polyR H10 r cq) (@mul_op polyR H10 m q) in
            match n return (prod (prod N polyR) polyR) with
            | O =>
                @pair (prod N polyR) polyR
                  (@pair N polyR (@add_op N H1 k (@one_op N H2)) qq1) r1
            | S n1 => loop (@add_op N H1 k (@one_op N H2)) qq1 r1 n1
            end
        end in
    forall (k : N) (qq r : polyR) (n : nat),
    @eq (prod (prod N polyR) polyR)
      match @lt_op N H (@size_op polyR N H5 r) sq return (prod (prod N polyR) polyR) with
      | true => @pair (prod N polyR) polyR (@pair N polyR k qq) r
      | false =>
          let m : polyR :=
            @shift_op polyR N H8 (@sub_op N H0 (@size_op polyR N H5 r) sq)
              (@cast_op R polyR H7 (@lead_coef_op R polyR H6 r : R) : polyR) in
          let qq1 : polyR := @add_op polyR H9 (@mul_op polyR H10 qq cq) m in
          let r1 : polyR :=
            @sub_op polyR H11 (@mul_op polyR H10 r cq) (@mul_op polyR H10 m q) in
          match n return (prod (prod N polyR) polyR) with
          | O =>
              @pair (prod N polyR) polyR
                (@pair N polyR (@add_op N H1 k (@one_op N H2)) qq1) r1
          | S n1 => loop (@add_op N H1 k (@one_op N H2)) qq1 r1 n1
          end
      end (loop k qq r n) :=
    fun (N R polyR : Type) (H : lt_of N) (H0 : sub_of N) (H1 : add_of N) 
      (H2 : one_of N) (H5 : size_of polyR N) (H6 : lead_coef_of R polyR)
      (H7 : cast_of R polyR) (H8 : shift_of polyR N) (H9 : add_of polyR)
      (H10 : mul_of polyR) (H11 : sub_of polyR) (q : polyR) =>
    let sq : N := @size_op polyR N H5 q : N in
    let cq : polyR := @cast_op R polyR H7 (@lead_coef_op R polyR H6 q : R) : polyR in
    let
      fix loop (k : N) (qq r : polyR) (n : nat) {struct n} : prod (prod N polyR) polyR :=
        match @lt_op N H (@size_op polyR N H5 r) sq return (prod (prod N polyR) polyR) with
        | true => @pair (prod N polyR) polyR (@pair N polyR k qq) r
        | false =>
            let m : polyR :=
              @shift_op polyR N H8 (@sub_op N H0 (@size_op polyR N H5 r) sq)
                (@cast_op R polyR H7 (@lead_coef_op R polyR H6 r : R) : polyR) in
            let qq1 : polyR := @add_op polyR H9 (@mul_op polyR H10 qq cq) m in
            let r1 : polyR :=
              @sub_op polyR H11 (@mul_op polyR H10 r cq) (@mul_op polyR H10 m q) in
            match n return (prod (prod N polyR) polyR) with
            | O =>
                @pair (prod N polyR) polyR
                  (@pair N polyR (@add_op N H1 k (@one_op N H2)) qq1) r1
            | S n1 => loop (@add_op N H1 k (@one_op N H2)) qq1 r1 n1
            end
        end in
    fun (k : N) (qq r : polyR) (n : nat) =>
    match
      n as n0
      return
        (@eq (prod (prod N polyR) polyR)
           match
             @lt_op N H (@size_op polyR N H5 r) sq return (prod (prod N polyR) polyR)
           with
           | true => @pair (prod N polyR) polyR (@pair N polyR k qq) r
           | false =>
               let m : polyR :=
                 @shift_op polyR N H8 (@sub_op N H0 (@size_op polyR N H5 r) sq)
                   (@cast_op R polyR H7 (@lead_coef_op R polyR H6 r)) in
               let qq1 : polyR := @add_op polyR H9 (@mul_op polyR H10 qq cq) m in
               let r1 : polyR :=
                 @sub_op polyR H11 (@mul_op polyR H10 r cq) (@mul_op polyR H10 m q) in
               match n0 return (prod (prod N polyR) polyR) with
               | O =>
                   @pair (prod N polyR) polyR
                     (@pair N polyR (@add_op N H1 k (@one_op N H2)) qq1) r1
               | S n1 => loop (@add_op N H1 k (@one_op N H2)) qq1 r1 n1
               end
           end (loop k qq r n0))
    with
    | O => @Logic.eq_refl (prod (prod N polyR) polyR) (loop k qq r O)
    | S n0 => @Logic.eq_refl (prod (prod N polyR) polyR) (loop k qq r (S n0))
    end in
  @eq_rect (prod (prod N₁ polyR₁) polyR₁)
    match
      @lt_op N₁ H₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁ return (prod (prod N₁ polyR₁) polyR₁)
    with
    | true => @pair (prod N₁ polyR₁) polyR₁ (@pair N₁ polyR₁ k₁ qq₁) r₁
    | false =>
        let m : polyR₁ :=
          @shift_op polyR₁ N₁ H8₁ (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁)
            (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁) : polyR₁) in
        let qq1 : polyR₁ := @add_op polyR₁ H9₁ (@mul_op polyR₁ H10₁ qq₁ cq₁) m in
        let r1 : polyR₁ :=
          @sub_op polyR₁ H11₁ (@mul_op polyR₁ H10₁ r₁ cq₁) (@mul_op polyR₁ H10₁ m q₁) in
        match n₁ return (prod (prod N₁ polyR₁) polyR₁) with
        | O =>
            @pair (prod N₁ polyR₁) polyR₁
              (@pair N₁ polyR₁ (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1) r1
        | S n1 => fix_loop_1 (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1 r1 n1
        end
    end
    (fun x : prod (prod N₁ polyR₁) polyR₁ =>
     @prod_R (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R)
       polyR₁ polyR₂ polyR_R x (fix_loop_2 k₂ qq₂ r₂ n₂))
    (@eq_rect (prod (prod N₂ polyR₂) polyR₂)
       match
         @lt_op N₂ H₂ (@size_op polyR₂ N₂ H5₂ r₂) sq₂ return (prod (prod N₂ polyR₂) polyR₂)
       with
       | true => @pair (prod N₂ polyR₂) polyR₂ (@pair N₂ polyR₂ k₂ qq₂) r₂
       | false =>
           let m : polyR₂ :=
             @shift_op polyR₂ N₂ H8₂ (@sub_op N₂ H0₂ (@size_op polyR₂ N₂ H5₂ r₂) sq₂)
               (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂) : polyR₂) in
           let qq1 : polyR₂ := @add_op polyR₂ H9₂ (@mul_op polyR₂ H10₂ qq₂ cq₂) m in
           let r1 : polyR₂ :=
             @sub_op polyR₂ H11₂ (@mul_op polyR₂ H10₂ r₂ cq₂) (@mul_op polyR₂ H10₂ m q₂) in
           match n₂ return (prod (prod N₂ polyR₂) polyR₂) with
           | O =>
               @pair (prod N₂ polyR₂) polyR₂
                 (@pair N₂ polyR₂ (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1) r1
           | S n1 => fix_loop_2 (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1 r1 n1
           end
       end
       (fun x : prod (prod N₂ polyR₂) polyR₂ =>
        @prod_R (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R)
          polyR₁ polyR₂ polyR_R
          match
            @lt_op N₁ H₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁
            return (prod (prod N₁ polyR₁) polyR₁)
          with
          | true => @pair (prod N₁ polyR₁) polyR₁ (@pair N₁ polyR₁ k₁ qq₁) r₁
          | false =>
              let m : polyR₁ :=
                @shift_op polyR₁ N₁ H8₁ (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁)
                  (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁) : polyR₁)
                in
              let qq1 : polyR₁ := @add_op polyR₁ H9₁ (@mul_op polyR₁ H10₁ qq₁ cq₁) m in
              let r1 : polyR₁ :=
                @sub_op polyR₁ H11₁ (@mul_op polyR₁ H10₁ r₁ cq₁) (@mul_op polyR₁ H10₁ m q₁)
                in
              match n₁ return (prod (prod N₁ polyR₁) polyR₁) with
              | O =>
                  @pair (prod N₁ polyR₁) polyR₁
                    (@pair N₁ polyR₁ (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1) r1
              | S n1 => fix_loop_1 (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1 r1 n1
              end
          end x)
       match
         (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
            (lt_of₁ : lt_of A₁) (lt_of₂ : lt_of A₂)
            (lt_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                          (H : forall (_ : A₁0) (_ : A₁0), bool)
                          (H0 : forall (_ : A₂0) (_ : A₂0), bool) =>
                        forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                          (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                        bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R lt_of₁ lt_of₂) => lt_of_R)
           N₁ N₂ N_R H₁ H₂ H_R (@size_op polyR₁ N₁ H5₁ r₁) (@size_op polyR₂ N₂ H5₂ r₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
               (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
               (size_of₁ : size_of A₁ N₁0) (size_of₂ : size_of A₂ N₂0)
               (size_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (N₁1 N₂1 : Type) (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                               (H : forall _ : A₁0, N₁1) (H0 : forall _ : A₂0, N₂1) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                             N_R1 (H H1) (H0 H2)) A₁ A₂ A_R N₁0 N₂0 N_R0 size_of₁ size_of₂)
             => size_of_R) polyR₁ polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂ H5_R r₁ r₂ r_R) sq₁ sq₂
           sq_R in (bool_R x₁ x₂)
         return
           (@prod_R (prod N₁ polyR₁) (prod N₂ polyR₂)
              (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
              match x₁ return (prod (prod N₁ polyR₁) polyR₁) with
              | true => @pair (prod N₁ polyR₁) polyR₁ (@pair N₁ polyR₁ k₁ qq₁) r₁
              | false =>
                  let m : polyR₁ :=
                    @shift_op polyR₁ N₁ H8₁
                      (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁)
                      (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁)
                       :
                       polyR₁) in
                  let qq1 : polyR₁ := @add_op polyR₁ H9₁ (@mul_op polyR₁ H10₁ qq₁ cq₁) m in
                  let r1 : polyR₁ :=
                    @sub_op polyR₁ H11₁ (@mul_op polyR₁ H10₁ r₁ cq₁)
                      (@mul_op polyR₁ H10₁ m q₁) in
                  match n₁ return (prod (prod N₁ polyR₁) polyR₁) with
                  | O =>
                      @pair (prod N₁ polyR₁) polyR₁
                        (@pair N₁ polyR₁ (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1) r1
                  | S n1 => fix_loop_1 (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1 r1 n1
                  end
              end
              match x₂ return (prod (prod N₂ polyR₂) polyR₂) with
              | true => @pair (prod N₂ polyR₂) polyR₂ (@pair N₂ polyR₂ k₂ qq₂) r₂
              | false =>
                  let m : polyR₂ :=
                    @shift_op polyR₂ N₂ H8₂
                      (@sub_op N₂ H0₂ (@size_op polyR₂ N₂ H5₂ r₂) sq₂)
                      (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂)
                       :
                       polyR₂) in
                  let qq1 : polyR₂ := @add_op polyR₂ H9₂ (@mul_op polyR₂ H10₂ qq₂ cq₂) m in
                  let r1 : polyR₂ :=
                    @sub_op polyR₂ H11₂ (@mul_op polyR₂ H10₂ r₂ cq₂)
                      (@mul_op polyR₂ H10₂ m q₂) in
                  match n₂ return (prod (prod N₂ polyR₂) polyR₂) with
                  | O =>
                      @pair (prod N₂ polyR₂) polyR₂
                        (@pair N₂ polyR₂ (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1) r1
                  | S n1 => fix_loop_2 (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1 r1 n1
                  end
              end)
       with
       | bool_R_true_R =>
           @prod_R_pair_R (prod N₁ polyR₁) (prod N₂ polyR₂)
             (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
             (@pair N₁ polyR₁ k₁ qq₁) (@pair N₂ polyR₂ k₂ qq₂)
             (@prod_R_pair_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R k₁ k₂ k_R qq₁ qq₂ qq_R) r₁ r₂
             r_R
       | bool_R_false_R =>
           let m₁ : polyR₁ :=
             @shift_op polyR₁ N₁ H8₁ (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁)
               (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁) : polyR₁) in
           let m₂ : polyR₂ :=
             @shift_op polyR₂ N₂ H8₂ (@sub_op N₂ H0₂ (@size_op polyR₂ N₂ H5₂ r₂) sq₂)
               (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂) : polyR₂) in
           let m_R : polyR_R m₁ m₂ :=
             (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                (shift_of₁ : shift_of polyA₁ N₁0) (shift_of₂ : shift_of polyA₂ N₂0)
                (shift_of_R : (fun (polyA₁0 polyA₂0 : Type)
                                 (polyA_R0 : forall (_ : polyA₁0) (_ : polyA₂0), Type)
                                 (N₁1 N₂1 : Type) (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                                 (H : forall (_ : N₁1) (_ : polyA₁0), polyA₁0)
                                 (H0 : forall (_ : N₂1) (_ : polyA₂0), polyA₂0) =>
                               forall (H1 : N₁1) (H2 : N₂1) (_ : N_R1 H1 H2) 
                                 (H3 : polyA₁0) (H4 : polyA₂0) 
                                 (_ : polyA_R0 H3 H4), polyA_R0 (H H1 H3) (H0 H2 H4))
                                polyA₁ polyA₂ polyA_R N₁0 N₂0 N_R0 shift_of₁ shift_of₂) =>
              shift_of_R) polyR₁ polyR₂ polyR_R N₁ N₂ N_R H8₁ H8₂ H8_R
               (@sub_op N₁ H0₁ (@size_op polyR₁ N₁ H5₁ r₁) sq₁)
               (@sub_op N₂ H0₂ (@size_op polyR₂ N₂ H5₂ r₂) sq₂)
               ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                   (sub_of₁ : sub_of A₁) (sub_of₂ : sub_of A₂)
                   (sub_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                  (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                                  (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                                A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R sub_of₁ sub_of₂) =>
                 sub_of_R) N₁ N₂ N_R H0₁ H0₂ H0_R (@size_op polyR₁ N₁ H5₁ r₁)
                  (@size_op polyR₂ N₂ H5₂ r₂)
                  ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                      (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                      (size_of₁ : size_of A₁ N₁0) (size_of₂ : size_of A₂ N₂0)
                      (size_of_R : (fun (A₁0 A₂0 : Type)
                                      (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                      (N₁1 N₂1 : Type)
                                      (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                                      (H : forall _ : A₁0, N₁1) 
                                      (H0 : forall _ : A₂0, N₂1) =>
                                    forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                                    N_R1 (H H1) (H0 H2)) A₁ A₂ A_R N₁0 N₂0 N_R0 size_of₁
                                     size_of₂) => size_of_R) polyR₁ polyR₂ polyR_R N₁ N₂
                     N_R H5₁ H5₂ H5_R r₁ r₂ r_R) sq₁ sq₂ sq_R)
               (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁) : polyR₁)
               (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂) : polyR₂)
               ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                   (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                   (cast_of₁ : cast_of A₁ B₁) (cast_of₂ : cast_of A₂ B₂)
                   (cast_of_R : (fun (A₁0 A₂0 : Type)
                                   (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                   (B₁0 B₂0 : Type)
                                   (B_R0 : forall (_ : B₁0) (_ : B₂0), Type)
                                   (H : forall _ : A₁0, B₁0) (H0 : forall _ : A₂0, B₂0) =>
                                 forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                                 B_R0 (H H1) (H0 H2)) A₁ A₂ A_R B₁ B₂ B_R cast_of₁ cast_of₂)
                 => cast_of_R) R₁ R₂ R_R polyR₁ polyR₂ polyR_R H7₁ H7₂ H7_R
                  (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁)
                  (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂)
                  ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                      (polyA₁ polyA₂ : Type)
                      (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                      (lead_coef_of₁ : lead_coef_of A₁ polyA₁)
                      (lead_coef_of₂ : lead_coef_of A₂ polyA₂)
                      (lead_coef_of_R : (fun (A₁0 A₂0 : Type)
                                           (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                           (polyA₁0 polyA₂0 : Type)
                                           (polyA_R0 : forall (_ : polyA₁0) (_ : polyA₂0),
                                                       Type) (H : forall _ : polyA₁0, A₁0)
                                           (H0 : forall _ : polyA₂0, A₂0) =>
                                         forall (H1 : polyA₁0) 
                                           (H2 : polyA₂0) (_ : polyA_R0 H1 H2),
                                         A_R0 (H H1) (H0 H2)) A₁ A₂ A_R polyA₁ polyA₂
                                          polyA_R lead_coef_of₁ lead_coef_of₂) =>
                    lead_coef_of_R) R₁ R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂ H6_R r₁ r₂ r_R
                   :
                   R_R (@lead_coef_op R₁ polyR₁ H6₁ r₁) (@lead_coef_op R₂ polyR₂ H6₂ r₂))
                :
                polyR_R (@cast_op R₁ polyR₁ H7₁ (@lead_coef_op R₁ polyR₁ H6₁ r₁ : R₁))
                  (@cast_op R₂ polyR₂ H7₂ (@lead_coef_op R₂ polyR₂ H6₂ r₂ : R₂))) in
           let qq1₁ : polyR₁ := @add_op polyR₁ H9₁ (@mul_op polyR₁ H10₁ qq₁ cq₁) m₁ in
           let qq1₂ : polyR₂ := @add_op polyR₂ H9₂ (@mul_op polyR₂ H10₂ qq₂ cq₂) m₂ in
           let qq1_R : polyR_R qq1₁ qq1₂ :=
             (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                (add_of₁ : add_of A₁) (add_of₂ : add_of A₂)
                (add_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                               (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                               (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                             A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R add_of₁ add_of₂) =>
              add_of_R) polyR₁ polyR₂ polyR_R H9₁ H9₂ H9_R (@mul_op polyR₁ H10₁ qq₁ cq₁)
               (@mul_op polyR₂ H10₂ qq₂ cq₂)
               ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                   (mul_of₁ : mul_of A₁) (mul_of₂ : mul_of A₂)
                   (mul_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                  (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                                  (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                                A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R mul_of₁ mul_of₂) =>
                 mul_of_R) polyR₁ polyR₂ polyR_R H10₁ H10₂ H10_R qq₁ qq₂ qq_R cq₁ cq₂ cq_R)
               m₁ m₂ m_R in
           let r1₁ : polyR₁ :=
             @sub_op polyR₁ H11₁ (@mul_op polyR₁ H10₁ r₁ cq₁) (@mul_op polyR₁ H10₁ m₁ q₁)
             in
           let r1₂ : polyR₂ :=
             @sub_op polyR₂ H11₂ (@mul_op polyR₂ H10₂ r₂ cq₂) (@mul_op polyR₂ H10₂ m₂ q₂)
             in
           let r1_R : polyR_R r1₁ r1₂ :=
             (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                (sub_of₁ : sub_of A₁) (sub_of₂ : sub_of A₂)
                (sub_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                               (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                               (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                             A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R sub_of₁ sub_of₂) =>
              sub_of_R) polyR₁ polyR₂ polyR_R H11₁ H11₂ H11_R (@mul_op polyR₁ H10₁ r₁ cq₁)
               (@mul_op polyR₂ H10₂ r₂ cq₂)
               ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                   (mul_of₁ : mul_of A₁) (mul_of₂ : mul_of A₂)
                   (mul_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                  (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                                  (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                                A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R mul_of₁ mul_of₂) =>
                 mul_of_R) polyR₁ polyR₂ polyR_R H10₁ H10₂ H10_R r₁ r₂ r_R cq₁ cq₂ cq_R)
               (@mul_op polyR₁ H10₁ m₁ q₁) (@mul_op polyR₂ H10₂ m₂ q₂)
               ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                   (mul_of₁ : mul_of A₁) (mul_of₂ : mul_of A₂)
                   (mul_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                  (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                                  (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4),
                                A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R mul_of₁ mul_of₂) =>
                 mul_of_R) polyR₁ polyR₂ polyR_R H10₁ H10₂ H10_R m₁ m₂ m_R q₁ q₂ q_R) in
           match
             n_R in (nat_R n₁0 n₂0)
             return
               (@prod_R (prod N₁ polyR₁) (prod N₂ polyR₂)
                  (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
                  match n₁0 return (prod (prod N₁ polyR₁) polyR₁) with
                  | O =>
                      @pair (prod N₁ polyR₁) polyR₁
                        (@pair N₁ polyR₁ (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1₁) r1₁
                  | S n1 => fix_loop_1 (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1₁ r1₁ n1
                  end
                  match n₂0 return (prod (prod N₂ polyR₂) polyR₂) with
                  | O =>
                      @pair (prod N₂ polyR₂) polyR₂
                        (@pair N₂ polyR₂ (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1₂) r1₂
                  | S n1 => fix_loop_2 (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1₂ r1₂ n1
                  end)
           with
           | nat_R_O_R =>
               @prod_R_pair_R (prod N₁ polyR₁) (prod N₂ polyR₂)
                 (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
                 (@pair N₁ polyR₁ (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁)) qq1₁)
                 (@pair N₂ polyR₂ (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂)) qq1₂)
                 (@prod_R_pair_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R
                    (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁))
                    (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂))
                    ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                        (add_of₁ : add_of A₁) (add_of₂ : add_of A₂)
                        (add_of_R : (fun (A₁0 A₂0 : Type)
                                       (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                       (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                       (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                     forall (H1 : A₁0) (H2 : A₂0) 
                                       (_ : A_R0 H1 H2) (H3 : A₁0) 
                                       (H4 : A₂0) (_ : A_R0 H3 H4),
                                     A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R add_of₁ add_of₂)
                      => add_of_R) N₁ N₂ N_R H1₁ H1₂ H1_R k₁ k₂ k_R 
                       (@one_op N₁ H2₁) (@one_op N₂ H2₂)
                       ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                           (one_of₁ : one_of A₁) (one_of₂ : one_of A₂)
                           (one_of_R : (fun (A₁0 A₂0 : Type)
                                          (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0)
                                         A₁ A₂ A_R one_of₁ one_of₂) => one_of_R) N₁ N₂ N_R
                          H2₁ H2₂ H2_R)) qq1₁ qq1₂ qq1_R) r1₁ r1₂ r1_R
           | @nat_R_S_R n1₁ n1₂ n1_R =>
               loop_R (@add_op N₁ H1₁ k₁ (@one_op N₁ H2₁))
                 (@add_op N₂ H1₂ k₂ (@one_op N₂ H2₂))
                 ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                     (add_of₁ : add_of A₁) (add_of₂ : add_of A₂)
                     (add_of_R : (fun (A₁0 A₂0 : Type)
                                    (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                    (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                                    (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
                                  forall (H1 : A₁0) (H2 : A₂0) 
                                    (_ : A_R0 H1 H2) (H3 : A₁0) 
                                    (H4 : A₂0) (_ : A_R0 H3 H4), 
                                  A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R add_of₁ add_of₂) =>
                   add_of_R) N₁ N₂ N_R H1₁ H1₂ H1_R k₁ k₂ k_R (@one_op N₁ H2₁)
                    (@one_op N₂ H2₂)
                    ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                        (one_of₁ : one_of A₁) (one_of₂ : one_of A₂)
                        (one_of_R : (fun (A₁0 A₂0 : Type)
                                       (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0)
                                      A₁ A₂ A_R one_of₁ one_of₂) => one_of_R) N₁ N₂ N_R H2₁
                       H2₂ H2_R)) qq1₁ qq1₂ qq1_R r1₁ r1₂ r1_R n1₁ n1₂ n1_R
           end
       end (fix_loop_2 k₂ qq₂ r₂ n₂)
       (gen_path N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂ k₂ qq₂ r₂ n₂))
    (fix_loop_1 k₁ qq₁ r₁ n₁)
    (gen_path N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁ k₁ qq₁ r₁ n₁).
Definition div_poly_R      : forall (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) 
         (R₁ R₂ : Type) (R_R : forall (_ : R₁) (_ : R₂), Type) 
         (polyR₁ polyR₂ : Type) (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type)
         (H₁ : lt_of N₁) (H₂ : lt_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂)
         (H0₁ : sub_of N₁) (H0₂ : sub_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂)
         (H1₁ : add_of N₁) (H1₂ : add_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂)
         (H2₁ : one_of N₁) (H2₂ : one_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H2₁ H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H3₁ H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R
                nat nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) 
         (H5₂ : size_of polyR₂ N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
         (H6₂ : lead_coef_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                 (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
               forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2))
                R₁ R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
         (H7₂ : cast_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R
                polyR₁ polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁)
         (H8₂ : shift_of polyR₂ N₂)
         (_ : (fun (polyA₁ polyA₂ : Type)
                 (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
                 (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
               forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
                 (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁)
         (H9₂ : add_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H9₁ H9₂) (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H10₁ H10₂) (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H11₁ H11₂) (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
                polyR_R H12₁ H12₂) (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁
                polyR₂ polyR_R H13₁ H13₂),
       (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
          (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
        forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
        A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
         (@div_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H3₁ H4₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ H12₁
            H13₁)
         (@div_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H3₂ H4₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ H12₂
            H13₂)
 := 
fun (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) (R₁ R₂ : Type)
  (R_R : forall (_ : R₁) (_ : R₂), Type) (polyR₁ polyR₂ : Type)
  (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type) (H₁ : lt_of N₁) 
  (H₂ : lt_of N₂)
  (H_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
            (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
          forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
          bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂) (H0₁ : sub_of N₁) 
  (H0₂ : sub_of N₂)
  (H0_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂) (H1₁ : add_of N₁) 
  (H1₂ : add_of N₂)
  (H1_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂) (H2₁ : one_of N₁) 
  (H2₂ : one_of N₂)
  (H2_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H2₁
            H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
  (H3_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H3₁
            H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
  (H4_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R nat
            nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) (H5₂ : size_of polyR₂ N₂)
  (H5_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
  (H6₂ : lead_coef_of R₂ polyR₂)
  (H6_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
           forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2)) R₁
            R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
  (H7₂ : cast_of R₂ polyR₂)
  (H7_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R polyR₁
            polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁) 
  (H8₂ : shift_of polyR₂ N₂)
  (H8_R : (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
             (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
           forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
             (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁) (H9₂ : add_of polyR₂)
  (H9_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H9₁ H9₂) 
  (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
  (H10_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H10₁ H10₂)
  (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
  (H11_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H11₁ H11₂)
  (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
  (H12_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H12₁ H12₂)
  (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
  (H13_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁ polyR₂
             polyR_R H13₁ H13₂) (p₁ : polyR₁) (p₂ : polyR₂) (p_R : polyR_R p₁ p₂)
  (q₁ : polyR₁) (q₂ : polyR₂) (q_R : polyR_R q₁ q₂) =>
(fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
   (B_R : forall (_ : B₁) (_ : B₂), Type) (p₁0 : prod A₁ B₁) (p₂0 : prod A₂ B₂)
   (p_R0 : @prod_R A₁ A₂ A_R B₁ B₂ B_R p₁0 p₂0) =>
 match
   p_R0 in (prod_R _ _ p₁1 p₂1)
   return
     (B_R match p₁1 return B₁ with
          | pair _ y => y
          end match p₂1 return B₂ with
              | pair _ y => y
              end)
 with
 | @prod_R_pair_R _ _ _ _ _ _ x₁ x₂ _ y₁ y₂ y_R => y_R
 end) N₁ N₂ N_R polyR₁ polyR₂ polyR_R
  (@fst (prod N₁ polyR₁) polyR₁
     match
       @eq_op polyR₁ H12₁ q₁ (@zero_op polyR₁ H13₁) return (prod (prod N₁ polyR₁) polyR₁)
     with
     | true =>
         @pair (prod N₁ polyR₁) polyR₁
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
     | false =>
         @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
           (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
     end)
  (@fst (prod N₂ polyR₂) polyR₂
     match
       @eq_op polyR₂ H12₂ q₂ (@zero_op polyR₂ H13₂) return (prod (prod N₂ polyR₂) polyR₂)
     with
     | true =>
         @pair (prod N₂ polyR₂) polyR₂
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
     | false =>
         @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
           (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
     end)
  ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
      (B_R : forall (_ : B₁) (_ : B₂), Type) (p₁0 : prod A₁ B₁) 
      (p₂0 : prod A₂ B₂) (p_R0 : @prod_R A₁ A₂ A_R B₁ B₂ B_R p₁0 p₂0) =>
    match
      p_R0 in (prod_R _ _ p₁1 p₂1)
      return
        (A_R match p₁1 return A₁ with
             | pair x _ => x
             end match p₂1 return A₂ with
                 | pair x _ => x
                 end)
    with
    | @prod_R_pair_R _ _ _ _ _ _ x₁ x₂ x_R y₁ y₂ _ => x_R
    end) (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁
     polyR₂ polyR_R
     match
       @eq_op polyR₁ H12₁ q₁ (@zero_op polyR₁ H13₁) return (prod (prod N₁ polyR₁) polyR₁)
     with
     | true =>
         @pair (prod N₁ polyR₁) polyR₁
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
     | false =>
         @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
           (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
     end
     match
       @eq_op polyR₂ H12₂ q₂ (@zero_op polyR₂ H13₂) return (prod (prod N₂ polyR₂) polyR₂)
     with
     | true =>
         @pair (prod N₂ polyR₂) polyR₂
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
     | false =>
         @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
           (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
     end
     match
       (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
          (eq_of₁ : eq_of A₁) (eq_of₂ : eq_of A₂)
          (eq_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                        (H : forall (_ : A₁0) (_ : A₁0), bool)
                        (H0 : forall (_ : A₂0) (_ : A₂0), bool) =>
                      forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                        (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4), 
                      bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R eq_of₁ eq_of₂) => eq_of_R)
         polyR₁ polyR₂ polyR_R H12₁ H12₂ H12_R q₁ q₂ q_R (@zero_op polyR₁ H13₁)
         (@zero_op polyR₂ H13₂)
         ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
             (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                           => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁
            polyR₂ polyR_R H13₁ H13₂ H13_R) in (bool_R x₁ x₂)
       return
         (@prod_R (prod N₁ polyR₁) (prod N₂ polyR₂)
            (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
            match x₁ return (prod (prod N₁ polyR₁) polyR₁) with
            | true =>
                @pair (prod N₁ polyR₁) polyR₁
                  (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
            | false =>
                @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
                  (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
                  (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
            end
            match x₂ return (prod (prod N₂ polyR₂) polyR₂) with
            | true =>
                @pair (prod N₂ polyR₂) polyR₂
                  (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
            | false =>
                @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
                  (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
                  (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
            end)
     with
     | bool_R_true_R =>
         @prod_R_pair_R (prod N₁ polyR₁) (prod N₂ polyR₂)
           (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁))
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂))
           (@prod_R_pair_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R (@zero_op N₁ H3₁)
              (@zero_op N₂ H3₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                  (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
                  (zero_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁ A₂
                                 A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R H3₁ H3₂
                 H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                  (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
                  (zero_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁ A₂
                                 A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁ polyR₂ polyR_R
                 H13₁ H13₂ H13_R)) p₁ p₂ p_R
     | bool_R_false_R =>
         @div_rec_poly_R N₁ N₂ N_R R₁ R₂ R_R polyR₁ polyR₂ polyR_R H₁ H₂ H_R H0₁ H0₂ H0_R
           H1₁ H1₂ H1_R H2₁ H2₂ H2_R H5₁ H5₂ H5_R H6₁ H6₂ H6_R H7₁ H7₂ H7_R H8₁ H8₂ H8_R
           H9₁ H9₂ H9_R H10₁ H10₂ H10_R H11₁ H11₂ H11_R q₁ q₂ q_R 
           (@zero_op N₁ H3₁) (@zero_op N₂ H3₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R
              H3₁ H3₂ H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁
              polyR₂ polyR_R H13₁ H13₂ H13_R) p₁ p₂ p_R
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
               (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
               (spec_of₁ : spec_of A₁ B₁) (spec_of₂ : spec_of A₂ B₂)
               (spec_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (B₁0 B₂0 : Type) (B_R0 : forall (_ : B₁0) (_ : B₂0), Type)
                               (H : forall _ : A₁0, B₁0) (H0 : forall _ : A₂0, B₂0) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                             B_R0 (H H1) (H0 H2)) A₁ A₂ A_R B₁ B₂ B_R spec_of₁ spec_of₂) =>
             spec_of_R) N₁ N₂ N_R nat nat nat_R H4₁ H4₂ H4_R
              (@size_op polyR₁ N₁ H5₁ p₁ : N₁) (@size_op polyR₂ N₂ H5₂ p₂ : N₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                  (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                  (size_of₁ : size_of A₁ N₁0) (size_of₂ : size_of A₂ N₂0)
                  (size_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (N₁1 N₂1 : Type)
                                  (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                                  (H : forall _ : A₁0, N₁1) (H0 : forall _ : A₂0, N₂1) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                                N_R1 (H H1) (H0 H2)) A₁ A₂ A_R N₁0 N₂0 N_R0 size_of₁
                                 size_of₂) => size_of_R) polyR₁ polyR₂ polyR_R N₁ N₂ N_R
                 H5₁ H5₂ H5_R p₁ p₂ p_R
               :
               N_R (@size_op polyR₁ N₁ H5₁ p₁) (@size_op polyR₂ N₂ H5₂ p₂)))
     end).
Definition mod_poly_R      : forall (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) 
         (R₁ R₂ : Type) (R_R : forall (_ : R₁) (_ : R₂), Type) 
         (polyR₁ polyR₂ : Type) (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type)
         (H₁ : lt_of N₁) (H₂ : lt_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂)
         (H0₁ : sub_of N₁) (H0₂ : sub_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂)
         (H1₁ : add_of N₁) (H1₂ : add_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂)
         (H2₁ : one_of N₁) (H2₂ : one_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H2₁ H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H3₁ H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R
                nat nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) 
         (H5₂ : size_of polyR₂ N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
         (H6₂ : lead_coef_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                 (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
               forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2))
                R₁ R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
         (H7₂ : cast_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R
                polyR₁ polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁)
         (H8₂ : shift_of polyR₂ N₂)
         (_ : (fun (polyA₁ polyA₂ : Type)
                 (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
                 (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
               forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
                 (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁)
         (H9₂ : add_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H9₁ H9₂) (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H10₁ H10₂) (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H11₁ H11₂) (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
                polyR_R H12₁ H12₂) (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁
                polyR₂ polyR_R H13₁ H13₂),
       (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
          (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
        forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
        A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
         (@mod_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H3₁ H4₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ H12₁
            H13₁)
         (@mod_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H3₂ H4₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ H12₂
            H13₂)
 := 
fun (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) (R₁ R₂ : Type)
  (R_R : forall (_ : R₁) (_ : R₂), Type) (polyR₁ polyR₂ : Type)
  (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type) (H₁ : lt_of N₁) 
  (H₂ : lt_of N₂)
  (H_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
            (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
          forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
          bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂) (H0₁ : sub_of N₁) 
  (H0₂ : sub_of N₂)
  (H0_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂) (H1₁ : add_of N₁) 
  (H1₂ : add_of N₂)
  (H1_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂) (H2₁ : one_of N₁) 
  (H2₂ : one_of N₂)
  (H2_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H2₁
            H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
  (H3_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H3₁
            H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
  (H4_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R nat
            nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) (H5₂ : size_of polyR₂ N₂)
  (H5_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
  (H6₂ : lead_coef_of R₂ polyR₂)
  (H6_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
           forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2)) R₁
            R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
  (H7₂ : cast_of R₂ polyR₂)
  (H7_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R polyR₁
            polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁) 
  (H8₂ : shift_of polyR₂ N₂)
  (H8_R : (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
             (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
           forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
             (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁) (H9₂ : add_of polyR₂)
  (H9_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H9₁ H9₂) 
  (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
  (H10_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H10₁ H10₂)
  (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
  (H11_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H11₁ H11₂)
  (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
  (H12_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H12₁ H12₂)
  (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
  (H13_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁ polyR₂
             polyR_R H13₁ H13₂) (p₁ : polyR₁) (p₂ : polyR₂) (p_R : polyR_R p₁ p₂)
  (q₁ : polyR₁) (q₂ : polyR₂) (q_R : polyR_R q₁ q₂) =>
(fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
   (B_R : forall (_ : B₁) (_ : B₂), Type) (p₁0 : prod A₁ B₁) (p₂0 : prod A₂ B₂)
   (p_R0 : @prod_R A₁ A₂ A_R B₁ B₂ B_R p₁0 p₂0) =>
 match
   p_R0 in (prod_R _ _ p₁1 p₂1)
   return
     (B_R match p₁1 return B₁ with
          | pair _ y => y
          end match p₂1 return B₂ with
              | pair _ y => y
              end)
 with
 | @prod_R_pair_R _ _ _ _ _ _ x₁ x₂ _ y₁ y₂ y_R => y_R
 end) (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁
  polyR₂ polyR_R
  match
    @eq_op polyR₁ H12₁ q₁ (@zero_op polyR₁ H13₁) return (prod (prod N₁ polyR₁) polyR₁)
  with
  | true =>
      @pair (prod N₁ polyR₁) polyR₁
        (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
  | false =>
      @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
        (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
        (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
  end
  match
    @eq_op polyR₂ H12₂ q₂ (@zero_op polyR₂ H13₂) return (prod (prod N₂ polyR₂) polyR₂)
  with
  | true =>
      @pair (prod N₂ polyR₂) polyR₂
        (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
  | false =>
      @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
        (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
        (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
  end
  match
    (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
       (eq_of₁ : eq_of A₁) (eq_of₂ : eq_of A₂)
       (eq_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                     (H : forall (_ : A₁0) (_ : A₁0), bool)
                     (H0 : forall (_ : A₂0) (_ : A₂0), bool) =>
                   forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                     (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4), bool_R (H H1 H3) (H0 H2 H4))
                    A₁ A₂ A_R eq_of₁ eq_of₂) => eq_of_R) polyR₁ polyR₂ polyR_R H12₁ H12₂
      H12_R q₁ q₂ q_R (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
      ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
          (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
          (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) =>
                        A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁ polyR₂
         polyR_R H13₁ H13₂ H13_R) in (bool_R x₁ x₂)
    return
      (@prod_R (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R)
         polyR₁ polyR₂ polyR_R
         match x₁ return (prod (prod N₁ polyR₁) polyR₁) with
         | true =>
             @pair (prod N₁ polyR₁) polyR₁
               (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
         | false =>
             @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
               (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
               (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
         end
         match x₂ return (prod (prod N₂ polyR₂) polyR₂) with
         | true =>
             @pair (prod N₂ polyR₂) polyR₂
               (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
         | false =>
             @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
               (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
               (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
         end)
  with
  | bool_R_true_R =>
      @prod_R_pair_R (prod N₁ polyR₁) (prod N₂ polyR₂)
        (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
        (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁))
        (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂))
        (@prod_R_pair_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R (@zero_op N₁ H3₁) 
           (@zero_op N₂ H3₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R
              H3₁ H3₂ H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁
              polyR₂ polyR_R H13₁ H13₂ H13_R)) p₁ p₂ p_R
  | bool_R_false_R =>
      @div_rec_poly_R N₁ N₂ N_R R₁ R₂ R_R polyR₁ polyR₂ polyR_R H₁ H₂ H_R H0₁ H0₂ H0_R H1₁
        H1₂ H1_R H2₁ H2₂ H2_R H5₁ H5₂ H5_R H6₁ H6₂ H6_R H7₁ H7₂ H7_R H8₁ H8₂ H8_R H9₁ H9₂
        H9_R H10₁ H10₂ H10_R H11₁ H11₂ H11_R q₁ q₂ q_R (@zero_op N₁ H3₁) 
        (@zero_op N₂ H3₂)
        ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
            (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
            (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) =>
                          A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R H3₁
           H3₂ H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
        ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
            (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
            (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) =>
                          A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁ polyR₂
           polyR_R H13₁ H13₂ H13_R) p₁ p₂ p_R
        (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
        (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
        ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
            (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
            (spec_of₁ : spec_of A₁ B₁) (spec_of₂ : spec_of A₂ B₂)
            (spec_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                            (B₁0 B₂0 : Type) (B_R0 : forall (_ : B₁0) (_ : B₂0), Type)
                            (H : forall _ : A₁0, B₁0) (H0 : forall _ : A₂0, B₂0) =>
                          forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                          B_R0 (H H1) (H0 H2)) A₁ A₂ A_R B₁ B₂ B_R spec_of₁ spec_of₂) =>
          spec_of_R) N₁ N₂ N_R nat nat nat_R H4₁ H4₂ H4_R (@size_op polyR₁ N₁ H5₁ p₁ : N₁)
           (@size_op polyR₂ N₂ H5₂ p₂ : N₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
               (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
               (size_of₁ : size_of A₁ N₁0) (size_of₂ : size_of A₂ N₂0)
               (size_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (N₁1 N₂1 : Type) (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                               (H : forall _ : A₁0, N₁1) (H0 : forall _ : A₂0, N₂1) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                             N_R1 (H H1) (H0 H2)) A₁ A₂ A_R N₁0 N₂0 N_R0 size_of₁ size_of₂)
             => size_of_R) polyR₁ polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂ H5_R p₁ p₂ p_R
            :
            N_R (@size_op polyR₁ N₁ H5₁ p₁) (@size_op polyR₂ N₂ H5₂ p₂)))
  end.
Definition scal_poly_R      : forall (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) 
         (R₁ R₂ : Type) (R_R : forall (_ : R₁) (_ : R₂), Type) 
         (polyR₁ polyR₂ : Type) (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type)
         (H₁ : lt_of N₁) (H₂ : lt_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂)
         (H0₁ : sub_of N₁) (H0₂ : sub_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂)
         (H1₁ : add_of N₁) (H1₂ : add_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂)
         (H2₁ : one_of N₁) (H2₂ : one_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H2₁ H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R
                H3₁ H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R
                nat nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) 
         (H5₂ : size_of polyR₂ N₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
         (H6₂ : lead_coef_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
                 (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
               forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2))
                R₁ R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
         (H7₂ : cast_of R₂ polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                 (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
                 (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R
                polyR₁ polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁)
         (H8₂ : shift_of polyR₂ N₂)
         (_ : (fun (polyA₁ polyA₂ : Type)
                 (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type) 
                 (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                 (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
                 (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
               forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
                 (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁
                polyR₂ polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁)
         (H9₂ : add_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H9₁ H9₂) (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H10₁ H10₂) (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R
                H11₁ H11₂) (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                 (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool)
               =>
               forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) 
                 (H4 : A₂) (_ : A_R H3 H4), bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
                polyR_R H12₁ H12₂) (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
         (_ : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁
                polyR₂ polyR_R H13₁ H13₂),
       (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
          (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
          (H : forall (_ : polyA₁) (_ : polyA₁), N₁0)
          (H0 : forall (_ : polyA₂) (_ : polyA₂), N₂0) =>
        forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2) 
          (H3 : polyA₁) (H4 : polyA₂) (_ : polyA_R H3 H4), N_R0 (H H1 H3) (H0 H2 H4))
         polyR₁ polyR₂ polyR_R N₁ N₂ N_R
         (@scal_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H3₁ H4₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ H12₁
            H13₁)
         (@scal_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H3₂ H4₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ H12₂
            H13₂)
 := 
fun (N₁ N₂ : Type) (N_R : forall (_ : N₁) (_ : N₂), Type) (R₁ R₂ : Type)
  (R_R : forall (_ : R₁) (_ : R₂), Type) (polyR₁ polyR₂ : Type)
  (polyR_R : forall (_ : polyR₁) (_ : polyR₂), Type) (H₁ : lt_of N₁) 
  (H₂ : lt_of N₂)
  (H_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
            (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
          forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
          bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H₁ H₂) (H0₁ : sub_of N₁) 
  (H0₂ : sub_of N₂)
  (H0_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H0₁ H0₂) (H1₁ : add_of N₁) 
  (H1₂ : add_of N₂)
  (H1_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R H1₁ H1₂) (H2₁ : one_of N₁) 
  (H2₂ : one_of N₂)
  (H2_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H2₁
            H2₂) (H3₁ : zero_of N₁) (H3₂ : zero_of N₂)
  (H3_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) N₁ N₂ N_R H3₁
            H3₂) (H4₁ : spec_of N₁ nat) (H4₂ : spec_of N₂ nat)
  (H4_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) N₁ N₂ N_R nat
            nat nat_R H4₁ H4₂) (H5₁ : size_of polyR₁ N₁) (H5₂ : size_of polyR₂ N₂)
  (H5_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall _ : A₁, N₁0) (H0 : forall _ : A₂, N₂0) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), N_R0 (H H1) (H0 H2)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H5₁ H5₂) (H6₁ : lead_coef_of R₁ polyR₁)
  (H6₂ : lead_coef_of R₂ polyR₂)
  (H6_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (H : forall _ : polyA₁, A₁) (H0 : forall _ : polyA₂, A₂) =>
           forall (H1 : polyA₁) (H2 : polyA₂) (_ : polyA_R H1 H2), A_R (H H1) (H0 H2)) R₁
            R₂ R_R polyR₁ polyR₂ polyR_R H6₁ H6₂) (H7₁ : cast_of R₁ polyR₁)
  (H7₂ : cast_of R₂ polyR₂)
  (H7_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
             (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type) 
             (H : forall _ : A₁, B₁) (H0 : forall _ : A₂, B₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2), B_R (H H1) (H0 H2)) R₁ R₂ R_R polyR₁
            polyR₂ polyR_R H7₁ H7₂) (H8₁ : shift_of polyR₁ N₁) 
  (H8₂ : shift_of polyR₂ N₂)
  (H8_R : (fun (polyA₁ polyA₂ : Type) (polyA_R : forall (_ : polyA₁) (_ : polyA₂), Type)
             (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
             (H : forall (_ : N₁0) (_ : polyA₁), polyA₁)
             (H0 : forall (_ : N₂0) (_ : polyA₂), polyA₂) =>
           forall (H1 : N₁0) (H2 : N₂0) (_ : N_R0 H1 H2) (H3 : polyA₁) 
             (H4 : polyA₂) (_ : polyA_R H3 H4), polyA_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂
            polyR_R N₁ N₂ N_R H8₁ H8₂) (H9₁ : add_of polyR₁) (H9₂ : add_of polyR₂)
  (H9_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
           forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
           A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H9₁ H9₂) 
  (H10₁ : mul_of polyR₁) (H10₂ : mul_of polyR₂)
  (H10_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H10₁ H10₂)
  (H11₁ : sub_of polyR₁) (H11₂ : sub_of polyR₂)
  (H11_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), A₁) (H0 : forall (_ : A₂) (_ : A₂), A₂) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            A_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H11₁ H11₂)
  (H12₁ : eq_of polyR₁) (H12₂ : eq_of polyR₂)
  (H12_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
              (H : forall (_ : A₁) (_ : A₁), bool) (H0 : forall (_ : A₂) (_ : A₂), bool) =>
            forall (H1 : A₁) (H2 : A₂) (_ : A_R H1 H2) (H3 : A₁) (H4 : A₂) (_ : A_R H3 H4),
            bool_R (H H1 H3) (H0 H2 H4)) polyR₁ polyR₂ polyR_R H12₁ H12₂)
  (H13₁ : zero_of polyR₁) (H13₂ : zero_of polyR₂)
  (H13_R : (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) => A_R) polyR₁ polyR₂
             polyR_R H13₁ H13₂) (p₁ : polyR₁) (p₂ : polyR₂) (p_R : polyR_R p₁ p₂)
  (q₁ : polyR₁) (q₂ : polyR₂) (q_R : polyR_R q₁ q₂) =>
(fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
   (B_R : forall (_ : B₁) (_ : B₂), Type) (p₁0 : prod A₁ B₁) (p₂0 : prod A₂ B₂)
   (p_R0 : @prod_R A₁ A₂ A_R B₁ B₂ B_R p₁0 p₂0) =>
 match
   p_R0 in (prod_R _ _ p₁1 p₂1)
   return
     (A_R match p₁1 return A₁ with
          | pair x _ => x
          end match p₂1 return A₂ with
              | pair x _ => x
              end)
 with
 | @prod_R_pair_R _ _ _ _ _ _ x₁ x₂ x_R y₁ y₂ _ => x_R
 end) N₁ N₂ N_R polyR₁ polyR₂ polyR_R
  (@fst (prod N₁ polyR₁) polyR₁
     match
       @eq_op polyR₁ H12₁ q₁ (@zero_op polyR₁ H13₁) return (prod (prod N₁ polyR₁) polyR₁)
     with
     | true =>
         @pair (prod N₁ polyR₁) polyR₁
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
     | false =>
         @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
           (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
     end)
  (@fst (prod N₂ polyR₂) polyR₂
     match
       @eq_op polyR₂ H12₂ q₂ (@zero_op polyR₂ H13₂) return (prod (prod N₂ polyR₂) polyR₂)
     with
     | true =>
         @pair (prod N₂ polyR₂) polyR₂
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
     | false =>
         @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
           (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
     end)
  ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (B₁ B₂ : Type)
      (B_R : forall (_ : B₁) (_ : B₂), Type) (p₁0 : prod A₁ B₁) 
      (p₂0 : prod A₂ B₂) (p_R0 : @prod_R A₁ A₂ A_R B₁ B₂ B_R p₁0 p₂0) =>
    match
      p_R0 in (prod_R _ _ p₁1 p₂1)
      return
        (A_R match p₁1 return A₁ with
             | pair x _ => x
             end match p₂1 return A₂ with
                 | pair x _ => x
                 end)
    with
    | @prod_R_pair_R _ _ _ _ _ _ x₁ x₂ x_R y₁ y₂ _ => x_R
    end) (prod N₁ polyR₁) (prod N₂ polyR₂) (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁
     polyR₂ polyR_R
     match
       @eq_op polyR₁ H12₁ q₁ (@zero_op polyR₁ H13₁) return (prod (prod N₁ polyR₁) polyR₁)
     with
     | true =>
         @pair (prod N₁ polyR₁) polyR₁
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
     | false =>
         @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
           (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
     end
     match
       @eq_op polyR₂ H12₂ q₂ (@zero_op polyR₂ H13₂) return (prod (prod N₂ polyR₂) polyR₂)
     with
     | true =>
         @pair (prod N₂ polyR₂) polyR₂
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
     | false =>
         @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
           (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
     end
     match
       (fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
          (eq_of₁ : eq_of A₁) (eq_of₂ : eq_of A₂)
          (eq_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                        (H : forall (_ : A₁0) (_ : A₁0), bool)
                        (H0 : forall (_ : A₂0) (_ : A₂0), bool) =>
                      forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) 
                        (H3 : A₁0) (H4 : A₂0) (_ : A_R0 H3 H4), 
                      bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R eq_of₁ eq_of₂) => eq_of_R)
         polyR₁ polyR₂ polyR_R H12₁ H12₂ H12_R q₁ q₂ q_R (@zero_op polyR₁ H13₁)
         (@zero_op polyR₂ H13₂)
         ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
             (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
             (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                           => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁
            polyR₂ polyR_R H13₁ H13₂ H13_R) in (bool_R x₁ x₂)
       return
         (@prod_R (prod N₁ polyR₁) (prod N₂ polyR₂)
            (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
            match x₁ return (prod (prod N₁ polyR₁) polyR₁) with
            | true =>
                @pair (prod N₁ polyR₁) polyR₁
                  (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁)) p₁
            | false =>
                @div_rec_poly N₁ R₁ polyR₁ H₁ H0₁ H1₁ H2₁ H5₁ H6₁ H7₁ H8₁ H9₁ H10₁ H11₁ q₁
                  (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁) p₁
                  (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
            end
            match x₂ return (prod (prod N₂ polyR₂) polyR₂) with
            | true =>
                @pair (prod N₂ polyR₂) polyR₂
                  (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂)) p₂
            | false =>
                @div_rec_poly N₂ R₂ polyR₂ H₂ H0₂ H1₂ H2₂ H5₂ H6₂ H7₂ H8₂ H9₂ H10₂ H11₂ q₂
                  (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂) p₂
                  (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
            end)
     with
     | bool_R_true_R =>
         @prod_R_pair_R (prod N₁ polyR₁) (prod N₂ polyR₂)
           (@prod_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R) polyR₁ polyR₂ polyR_R
           (@pair N₁ polyR₁ (@zero_op N₁ H3₁) (@zero_op polyR₁ H13₁))
           (@pair N₂ polyR₂ (@zero_op N₂ H3₂) (@zero_op polyR₂ H13₂))
           (@prod_R_pair_R N₁ N₂ N_R polyR₁ polyR₂ polyR_R (@zero_op N₁ H3₁)
              (@zero_op N₂ H3₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                  (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
                  (zero_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁ A₂
                                 A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R H3₁ H3₂
                 H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
                  (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
                  (zero_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁ A₂
                                 A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁ polyR₂ polyR_R
                 H13₁ H13₂ H13_R)) p₁ p₂ p_R
     | bool_R_false_R =>
         @div_rec_poly_R N₁ N₂ N_R R₁ R₂ R_R polyR₁ polyR₂ polyR_R H₁ H₂ H_R H0₁ H0₂ H0_R
           H1₁ H1₂ H1_R H2₁ H2₂ H2_R H5₁ H5₂ H5_R H6₁ H6₂ H6_R H7₁ H7₂ H7_R H8₁ H8₂ H8_R
           H9₁ H9₂ H9_R H10₁ H10₂ H10_R H11₁ H11₂ H11_R q₁ q₂ q_R 
           (@zero_op N₁ H3₁) (@zero_op N₂ H3₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) N₁ N₂ N_R
              H3₁ H3₂ H3_R) (@zero_op polyR₁ H13₁) (@zero_op polyR₂ H13₂)
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type)
               (zero_of₁ : zero_of A₁) (zero_of₂ : zero_of A₂)
               (zero_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                             => A_R0) A₁ A₂ A_R zero_of₁ zero_of₂) => zero_of_R) polyR₁
              polyR₂ polyR_R H13₁ H13₂ H13_R) p₁ p₂ p_R
           (@spec N₁ nat H4₁ (@size_op polyR₁ N₁ H5₁ p₁ : N₁))
           (@spec N₂ nat H4₂ (@size_op polyR₂ N₂ H5₂ p₂ : N₂))
           ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
               (B₁ B₂ : Type) (B_R : forall (_ : B₁) (_ : B₂), Type)
               (spec_of₁ : spec_of A₁ B₁) (spec_of₂ : spec_of A₂ B₂)
               (spec_of_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                               (B₁0 B₂0 : Type) (B_R0 : forall (_ : B₁0) (_ : B₂0), Type)
                               (H : forall _ : A₁0, B₁0) (H0 : forall _ : A₂0, B₂0) =>
                             forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                             B_R0 (H H1) (H0 H2)) A₁ A₂ A_R B₁ B₂ B_R spec_of₁ spec_of₂) =>
             spec_of_R) N₁ N₂ N_R nat nat nat_R H4₁ H4₂ H4_R
              (@size_op polyR₁ N₁ H5₁ p₁ : N₁) (@size_op polyR₂ N₂ H5₂ p₂ : N₂)
              ((fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
                  (N₁0 N₂0 : Type) (N_R0 : forall (_ : N₁0) (_ : N₂0), Type)
                  (size_of₁ : size_of A₁ N₁0) (size_of₂ : size_of A₂ N₂0)
                  (size_of_R : (fun (A₁0 A₂0 : Type)
                                  (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                                  (N₁1 N₂1 : Type)
                                  (N_R1 : forall (_ : N₁1) (_ : N₂1), Type)
                                  (H : forall _ : A₁0, N₁1) (H0 : forall _ : A₂0, N₂1) =>
                                forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2),
                                N_R1 (H H1) (H0 H2)) A₁ A₂ A_R N₁0 N₂0 N_R0 size_of₁
                                 size_of₂) => size_of_R) polyR₁ polyR₂ polyR_R N₁ N₂ N_R
                 H5₁ H5₂ H5_R p₁ p₂ p_R
               :
               N_R (@size_op polyR₁ N₁ H5₁ p₁) (@size_op polyR₂ N₂ H5₂ p₂)))
     end).

Section division_correctness.

Variable R : ringType.

Local Instance lt_nat : lt_of nat := ltn.
Local Instance sub_nat : sub_of nat := subn.
Local Instance add_nat : add_of nat := addn.
Local Instance one_nat : one_of nat := 1%N.
Local Instance zero_nat : zero_of nat := 0%N.
Local Instance spec_nat : spec_of nat nat := spec_id.

Local Instance size_of_poly : size_of {poly R} nat := sizep (R:=R).
Local Instance lead_coef_poly : lead_coef_of R {poly R} := lead_coef.
Local Instance cast_poly : cast_of R {poly R} := polyC.
Local Instance shift_poly : shift_of {poly R} nat := shiftp (R:=R).
Local Instance add_poly : add_of {poly R} := +%R.
Local Instance mul_poly : mul_of {poly R} := *%R.
Local Instance sub_poly : sub_of {poly R} := fun p q => p - q.
Local Instance eq_poly : eq_of {poly R} := eqtype.eq_op.
Local Instance zero_poly : zero_of {poly R} := 0%R.

Lemma div_rec_polyE (p q : {poly R}) n r m:
  div_rec_poly (N:=nat) (R:=R) q n r p m = redivp_rec q n r p m.
Proof.
  rewrite /div_rec_poly /redivp_rec.
  move: n r p.
  elim: m=> [|m ihm] n r p;
    by rewrite -[(_ < _)%C]/(_ < _) /shift_op /shift_poly /shiftp ?ihm mul_polyC
               [(_ + _)%C]addn1.
Qed.

Lemma div_polyE (p q : {poly R}) : div_poly (N:=nat) (R:=R) p q = rdivp p q.
Proof.
  rewrite /div_poly -[rdivp p q]/((rscalp p q, rdivp p q, rmodp p q).1.2).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Lemma mod_polyE (p q : {poly R}) : mod_poly (N:=nat) (R:=R) p q = rmodp p q.
Proof.
  rewrite /mod_poly -[rmodp p q]/((rscalp p q, rdivp p q, rmodp p q).2).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Lemma scal_polyE (p q : {poly R}) : scal_poly (N:=nat) (R:=R) p q = rscalp p q.
Proof.
  rewrite /scal_poly -[rscalp p q]/((rscalp p q, rdivp p q, rmodp p q).1.1).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Section division_param.

Local Open Scope rel_scope.

Context (N : Type) (rN : nat -> N -> Type).
Context (C : Type) (rC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).

Context `{lt_of N, sub_of N, add_of N, one_of N, zero_of N, spec_of N nat}.
Context `{size_of polyC N, lead_coef_of C polyC, cast_of C polyC}.
Context `{shift_of polyC N, add_of polyC, mul_of polyC, sub_of polyC}.
Context `{eq_of polyC, zero_of polyC}.
Context `{!refines (rN ==> rN ==> bool_R) ltn lt_op}.
Context `{!refines (rN ==> rN ==> rN) subn sub_op}.
Context `{!refines (rN ==> rN ==> rN) addn add_op}.
Context `{!refines rN 1%N 1%C, !refines rN 0%N 0%C}.
Context `{!refines (rN ==> nat_R) spec_id spec}.
Context `{!refines (RpolyC ==> rN) size_op size_op}.
Context `{!refines (RpolyC ==> rC) lead_coef_poly lead_coef_op}.
Context `{!refines (rC ==> RpolyC) cast_poly cast}.
Context `{!refines (rN ==> RpolyC ==> RpolyC) shift_poly shift_op}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) sub_poly sub_op}.
Context `{!refines (RpolyC ==> RpolyC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines RpolyC 0%R 0%C}.

Global Instance RpolyC_div_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC)
          (div_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (div_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof. param div_poly_R. Qed.

Global Instance refine_div_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC) (@rdivp R)
          (div_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -div_polyE.
  exact: refinesP.
Qed.

Global Instance RpolyC_mod_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC)
          (mod_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (mod_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof. param mod_poly_R. Qed.

Global Instance refine_mod_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC) (@rmodp R)
          (mod_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -mod_polyE.
  exact: refinesP.
Qed.

Global Instance RpolyC_scal_poly :
  refines (RpolyC ==> RpolyC ==> rN)
          (scal_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (scal_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  eapply (scal_poly_R (polyR_R:=RpolyC))=> // *;
  eapply refinesP;
  do ?eapply refines_apply; tc.
Qed.

Global Instance refine_scal_poly :
  refines (RpolyC ==> RpolyC ==> rN) (@rscalp R)
          (scal_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -scal_polyE.
  exact: refinesP.
Qed.

End division_param.
End division_correctness.