From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly polydiv.

From CoqEAL Require Import hrel param refinements poly_op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Local Open Scope ring_scope.

Section seqpoly_op.

Local Open Scope computable_scope.

Variable A N : Type.

Definition seqpoly := seq A.

Context `{zero_of A, one_of A}.
Context `{add_of A, opp_of A, mul_of A, eq_of A}.
Context `{zero_of N, one_of N, add_of N, eq_of N}.
Context `{spec_of N nat}.

Global Instance cast_seqpoly : cast_of A seqpoly := fun x => [:: x].

Global Instance seqpoly0 : zero_of seqpoly := [::].
Global Instance seqpoly1 : one_of seqpoly := [:: 1].
Global Instance opp_seqpoly : opp_of seqpoly := List.map -%C.

Fixpoint add_seqpoly_fun (p q : seqpoly) : seqpoly := match p,q with
  | [::], q => q
  | p, [::] => p
  | a :: p', b :: q' => a + b :: add_seqpoly_fun p' q'
  end.

Global Instance add_seqpoly : add_of seqpoly := add_seqpoly_fun.
Global Instance sub_seqpoly : sub_of seqpoly := fun x y => (x + - y)%C.

Lemma sub_seqpoly_0 (s : seqpoly) : s - 0 = s.
Proof. by elim: s. Qed.

Global Instance scale_seqpoly : scale_of A seqpoly := fun a => map ( *%C a).

(* 0%C :: aux p = shift 1 (aux p) *)
Global Instance mul_seqpoly : mul_of seqpoly := fun p q =>
  let fix aux p :=
      if p is a :: p then (a *: q + (0%C :: aux p))%C else 0
  in aux p.

Global Instance exp_seqpoly : exp_of seqpoly N :=
  fun p n => iter (spec n) (mul_seqpoly p) 1.

Global Instance size_seqpoly : size_of seqpoly N :=
  let fix aux p :=
      if p is a :: p then
        let sp := aux p in
        if (sp == 0)%C then if (a == 0)%C then 0%C else 1%C
        else (sp + 1)%C
      else 0%C
  in aux.

Global Instance eq_seqpoly : eq_of seqpoly :=
  fun p q => all (fun x => x == 0)%C (p - q)%C.

Global Instance shift_seqpoly : shift_of seqpoly N :=
  fun n => ncons (spec n) 0%C.

Global Instance split_seqpoly : split_of seqpoly N :=
  fun n p => (drop (spec n) p,take (spec n) p).

Global Instance lead_coef_seqpoly : lead_coef_of A seqpoly :=
  fun p => nth 0 p (spec (size_seqpoly p)).-1.

End seqpoly_op.

Parametricity cast_seqpoly.
Parametricity seqpoly0.
Parametricity seqpoly1.
Parametricity opp_seqpoly.
Definition add_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H1₁ : add_of A₁) (H1₂ : add_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         A₁ A₂ A_R H1₁ H1₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
         (add_seqpoly (A:=A₁)) (add_seqpoly (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H1₁ : add_of A₁) (H1₂ : add_of A₂) =>
[eta (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H1₁0 : add_of A₁0)
        (H1₂0 : add_of A₂0)
        (H1_R0 : (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) 
                    (H : A₁1 -> A₁1 -> A₁1) (H0 : A₂1 -> A₂1 -> A₂1) =>
                  forall (H1 : A₁1) (H2 : A₂1),
                  A_R1 H1 H2 ->
                  forall (H3 : A₁1) (H4 : A₂1), A_R1 H3 H4 -> A_R1 (H H1 H3) (H0 H2 H4))
                   A₁0 A₂0 A_R0 H1₁0 H1₂0) =>
      let fix_add_seqpoly_fun_1 :=
        fix add_seqpoly_fun (p q : seqpoly A₁0) {struct p} : seqpoly A₁0 :=
          match p with
          | [::] => q
          | a :: p' =>
              match q with
              | [::] => p
              | b :: q' => (a + b)%C :: add_seqpoly_fun p' q'
              end
          end in
      let fix_add_seqpoly_fun_2 :=
        fix add_seqpoly_fun (p q : seqpoly A₂0) {struct p} : seqpoly A₂0 :=
          match p with
          | [::] => q
          | a :: p' =>
              match q with
              | [::] => p
              | b :: q' => (a + b)%C :: add_seqpoly_fun p' q'
              end
          end in
      fix
      add_seqpoly_fun_R (p₁ : seqpoly A₁0) (p₂ : seqpoly A₂0)
                        (p_R : (fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
                                 p₁ p₂) (q₁ : seqpoly A₁0) (q₂ : seqpoly A₂0)
                        (q_R : (fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
                                 q₁ q₂) {struct p_R} :
        (fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
          (fix_add_seqpoly_fun_1 p₁ q₁) (fix_add_seqpoly_fun_2 p₂ q₂) :=
        let gen_path :
          forall (A : Type) (H1 : add_of A),
          let
            fix add_seqpoly_fun (p q : seqpoly A) {struct p} : 
            seqpoly A :=
              match p with
              | [::] => q
              | a :: p' =>
                  match q with
                  | [::] => p
                  | b :: q' => (a + b)%C :: add_seqpoly_fun p' q'
                  end
              end in
          forall p q : seqpoly A,
          match p with
          | [::] => q
          | a :: p' =>
              match q with
              | [::] => p
              | b :: q' => (a + b)%C :: add_seqpoly_fun p' q'
              end
          end = add_seqpoly_fun p q :=
          fun (A : Type) (H1 : add_of A) =>
          let add_seqpoly_fun0 :=
            fix add_seqpoly_fun (p q : seqpoly A) {struct p} : 
            seqpoly A :=
              match p with
              | [::] => q
              | a :: p' =>
                  match q with
                  | [::] => p
                  | b :: q' => (a + b)%C :: add_seqpoly_fun p' q'
                  end
              end in
          fun p q : seqpoly A =>
          match
            p as l
            return
              (match l with
               | [::] => q
               | a :: p' =>
                   match q with
                   | [::] => l
                   | b :: q' => (a + b)%C :: add_seqpoly_fun0 p' q'
                   end
               end = add_seqpoly_fun0 l q)
          with
          | [::] => erefl (add_seqpoly_fun0 [::] q)
          | a :: p0 => erefl (add_seqpoly_fun0 (a :: p0) q)
          end in
        eq_rect
          match p₁ with
          | [::] => q₁
          | a :: p' =>
              match q₁ with
              | [::] => p₁
              | b :: q' => (a + b)%C :: fix_add_seqpoly_fun_1 p' q'
              end
          end
          (((fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0)^~ 
           (fix_add_seqpoly_fun_2 p₂ q₂))
          (eq_rect
             match p₂ with
             | [::] => q₂
             | a :: p' =>
                 match q₂ with
                 | [::] => p₂
                 | b :: q' => (a + b)%C :: fix_add_seqpoly_fun_2 p' q'
                 end
             end
             [eta (fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
                    match p₁ with
                    | [::] => q₁
                    | a :: p' =>
                        match q₁ with
                        | [::] => p₁
                        | b :: q' => (a + b)%C :: fix_add_seqpoly_fun_1 p' q'
                        end
                    end]
             match
               p_R in (list_R _ p₁0 p₂0)
               return
                 ((fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
                    match p₁0 with
                    | [::] => q₁
                    | a :: p' =>
                        match q₁ with
                        | [::] => p₁
                        | b :: q' => (a + b)%C :: fix_add_seqpoly_fun_1 p' q'
                        end
                    end
                    match p₂0 with
                    | [::] => q₂
                    | a :: p' =>
                        match q₂ with
                        | [::] => p₂
                        | b :: q' => (a + b)%C :: fix_add_seqpoly_fun_2 p' q'
                        end
                    end)
             with
             | @list_R_nil_R _ _ _ => q_R
             | @list_R_cons_R _ _ _ a₁ a₂ a_R p'₁ p'₂ p'_R =>
                 match
                   q_R in (list_R _ q₁0 q₂0)
                   return
                     ((fun A₁1 A₂1 : Type => [eta list_R (A₂:=A₂1)]) A₁0 A₂0 A_R0
                        match q₁0 with
                        | [::] => p₁
                        | b :: q' => (a₁ + b)%C :: fix_add_seqpoly_fun_1 p'₁ q'
                        end
                        match q₂0 with
                        | [::] => p₂
                        | b :: q' => (a₂ + b)%C :: fix_add_seqpoly_fun_2 p'₂ q'
                        end)
                 with
                 | @list_R_nil_R _ _ _ => p_R
                 | @list_R_cons_R _ _ _ b₁ b₂ b_R q'₁ q'₂ q'_R =>
                     list_R_cons_R
                       ((fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type)
                           (add_of₁ : add_of A₁1) (add_of₂ : add_of A₂1) => id) A₁0 A₂0
                          A_R0 H1₁0 H1₂0 H1_R0 a₁ a₂ a_R b₁ b₂ b_R)
                       (add_seqpoly_fun_R p'₁ p'₂ p'_R q'₁ q'₂ q'_R)
                 end
             end (fix_add_seqpoly_fun_2 p₂ q₂) (gen_path A₂0 H1₂0 p₂ q₂))
          (fix_add_seqpoly_fun_1 p₁ q₁) (gen_path A₁0 H1₁0 p₁ q₁)) A₁ A₂ A_R H1₁ H1₂].
Definition sub_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H1₁ : add_of A₁) (H1₂ : add_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         A₁ A₂ A_R H1₁ H1₂ ->
       forall (H2₁ : opp_of A₁) (H2₂ : opp_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0) (H0 : A₂0 -> A₂0)
        => forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> A_R0 (H H1) (H0 H2)) A₁ A₂ A_R H2₁
         H2₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
         (sub_seqpoly (A:=A₁)) (sub_seqpoly (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H1₁ : add_of A₁) (H1₂ : add_of A₂)
  (H1_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
            H1₁ H1₂) (H2₁ : opp_of A₁) (H2₂ : opp_of A₂)
  (H2_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> A_R0 (H H1) (H0 H2)) A₁ A₂ A_R H2₁
            H2₂) (x₁ : seqpoly A₁) (x₂ : seqpoly A₂)
  (x_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R x₁ x₂) 
  (y₁ : seqpoly A₁) (y₂ : seqpoly A₂)
  (y_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R y₁ y₂) =>
(fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (add_of₁ : add_of A₁0)
   (add_of₂ : add_of A₂0) => id) (seqpoly A₁) (seqpoly A₂)
  ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) (add_seqpoly (A:=A₁))
  (add_seqpoly (A:=A₂)) (add_seqpoly_R H1_R) x₁ x₂ x_R (- y₁)%C 
  (- y₂)%C
  ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (opp_of₁ : opp_of A₁0)
      (opp_of₂ : opp_of A₂0) => id) (seqpoly A₁) (seqpoly A₂)
     ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
     (opp_seqpoly (A:=A₁)) (opp_seqpoly (A:=A₂)) (opp_seqpoly_R H2_R) y₁ y₂ y_R).
Parametricity scale_seqpoly.
Definition mul_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂),
       (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂ ->
       forall (H1₁ : add_of A₁) (H1₂ : add_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         A₁ A₂ A_R H1₁ H1₂ ->
       forall (H3₁ : mul_of A₁) (H3₂ : mul_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         A₁ A₂ A_R H3₁ H3₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
         (mul_seqpoly (A:=A₁)) (mul_seqpoly (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂)
  (H_R : (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂) (H1₁ : add_of A₁) 
  (H1₂ : add_of A₂)
  (H1_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
            H1₁ H1₂) (H3₁ : mul_of A₁) (H3₂ : mul_of A₂)
  (H3_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
            H3₁ H3₂) (p₁ : seqpoly A₁) (p₂ : seqpoly A₂)
  (p_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R p₁ p₂) 
  (q₁ : seqpoly A₁) (q₂ : seqpoly A₂)
  (q_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R q₁ q₂) =>
let aux₁ :=
  fix aux (p : seq A₁) : seq A₁ :=
    match p with
    | [::] => 0%C
    | a :: p0 => (a *: q₁ + (0 :: aux p0))%C
    end in
let aux₂ :=
  fix aux (p : seq A₂) : seq A₂ :=
    match p with
    | [::] => 0%C
    | a :: p0 => (a *: q₂ + (0 :: aux p0))%C
    end in
let aux_R :=
  let fix_aux_1 :=
    fix aux (p : seq A₁) : seq A₁ :=
      match p with
      | [::] => 0%C
      | a :: p0 => (a *: q₁ + (0 :: aux p0))%C
      end in
  let fix_aux_2 :=
    fix aux (p : seq A₂) : seq A₂ :=
      match p with
      | [::] => 0%C
      | a :: p0 => (a *: q₂ + (0 :: aux p0))%C
      end in
  fix aux_R (p₁0 : seq A₁) (p₂0 : seq A₂) (p_R0 : list_R A_R p₁0 p₂0) {struct p_R0} :
    list_R A_R (fix_aux_1 p₁0) (fix_aux_2 p₂0) :=
    match
      p_R0 in (list_R _ p₁1 p₂1) return (list_R A_R (fix_aux_1 p₁1) (fix_aux_2 p₂1))
    with
    | @list_R_nil_R _ _ _ =>
        (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (zero_of₁ : zero_of A₁0)
           (zero_of₂ : zero_of A₂0) => id) (seq A₁) (seq A₂) (list_R A_R) 
          (seqpoly0 A₁) (seqpoly0 A₂) (seqpoly0_R A_R)
    | @list_R_cons_R _ _ _ a₁ a₂ a_R p₁1 p₂1 p_R1 =>
        (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (add_of₁ : add_of A₁0)
           (add_of₂ : add_of A₂0) => id) (seqpoly A₁) (seqpoly A₂)
          ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
          (add_seqpoly (A:=A₁)) (add_seqpoly (A:=A₂)) (add_seqpoly_R H1_R) 
          (a₁ *: q₁)%C (a₂ *: q₂)%C
          ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
              (B_R : B₁ -> B₂ -> Type) (scale_of₁ : scale_of A₁0 B₁)
              (scale_of₂ : scale_of A₂0 B₂) => id) A₁ A₂ A_R (seqpoly A₁) 
             (seqpoly A₂) ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R)
             (scale_seqpoly (A:=A₁)) (scale_seqpoly (A:=A₂)) (scale_seqpoly_R H3_R) a₁ a₂
             a_R q₁ q₂ q_R) (0%C :: fix_aux_1 p₁1) (0%C :: fix_aux_2 p₂1)
          (list_R_cons_R
             ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) 
                 (zero_of₁ : zero_of A₁0) (zero_of₂ : zero_of A₂0) => id) A₁ A₂ A_R H₁ H₂
                H_R) (aux_R p₁1 p₂1 p_R1))
    end in
aux_R p₁ p₂ p_R.
Definition exp_seqpoly' := Eval compute in exp_seqpoly.
Definition exp_seqpoly'_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type)
         (N_R : N₁ -> N₂ -> Type) (H₁ : A₁) (H₂ : A₂),
       A_R H₁ H₂ ->
       forall (H0₁ : A₁) (H0₂ : A₂),
       A_R H0₁ H0₂ ->
       forall (H1₁ : A₁ -> A₁ -> A₁) (H1₂ : A₂ -> A₂ -> A₂),
       (forall (H : A₁) (H0 : A₂),
        A_R H H0 -> forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> A_R (H1₁ H H1) (H1₂ H0 H2)) ->
       forall (H3₁ : A₁ -> A₁ -> A₁) (H3₂ : A₂ -> A₂ -> A₂),
       (forall (H : A₁) (H0 : A₂),
        A_R H H0 -> forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> A_R (H3₁ H H1) (H3₂ H0 H2)) ->
       forall (H9₁ : N₁ -> nat) (H9₂ : N₂ -> nat),
       (forall (H : N₁) (H0 : N₂), N_R H H0 -> nat_R (H9₁ H) (H9₂ H0)) ->
       forall (p₁ : seq A₁) (p₂ : seq A₂),
       list_R A_R p₁ p₂ ->
       forall (n₁ : N₁) (n₂ : N₂),
       N_R n₁ n₂ ->
       list_R A_R (exp_seqpoly' H₁ H0₁ H1₁ H3₁ H9₁ p₁ n₁)
         (exp_seqpoly' H₂ H0₂ H1₂ H3₂ H9₂ p₂ n₂) := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type) (N_R : N₁ -> N₂ -> Type)
  (H₁ : A₁) (H₂ : A₂) (H_R : A_R H₁ H₂) (H0₁ : A₁) (H0₂ : A₂) (H0_R : A_R H0₁ H0₂)
  (H1₁ : A₁ -> A₁ -> A₁) (H1₂ : A₂ -> A₂ -> A₂)
  (H1_R : forall (H : A₁) (H0 : A₂),
          A_R H H0 -> forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> A_R (H1₁ H H1) (H1₂ H0 H2))
  (H3₁ : A₁ -> A₁ -> A₁) (H3₂ : A₂ -> A₂ -> A₂)
  (H3_R : forall (H : A₁) (H0 : A₂),
          A_R H H0 -> forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> A_R (H3₁ H H1) (H3₂ H0 H2))
  (H9₁ : N₁ -> nat) (H9₂ : N₂ -> nat)
  (H9_R : forall (H : N₁) (H0 : N₂), N_R H H0 -> nat_R (H9₁ H) (H9₂ H0)) 
  (p₁ : seq A₁) (p₂ : seq A₂) (p_R : list_R A_R p₁ p₂) (n₁ : N₁) 
  (n₂ : N₂) (n_R : N_R n₁ n₂) =>
(let fix_loop_1 :=
   fix loop (m : nat) : seq A₁ :=
     match m with
     | 0 => [:: H0₁]
     | succn i =>
         (fix aux (p : seq A₁) : seq A₁ :=
            match p with
            | [::] => [::]
            | a :: p0 =>
                (fix add_seqpoly_fun (p1 q : seq A₁) {struct p1} : 
                 seq A₁ :=
                   match p1 with
                   | [::] => q
                   | a0 :: p' =>
                       match q with
                       | [::] => p1
                       | b :: q' => H1₁ a0 b :: add_seqpoly_fun p' q'
                       end
                   end)
                  ((fix map (s : seq A₁) : seq A₁ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₁ a x :: map s'
                      end) (loop i)) (H₁ :: aux p0)
            end) p₁
     end in
 let fix_loop_2 :=
   fix loop (m : nat) : seq A₂ :=
     match m with
     | 0 => [:: H0₂]
     | succn i =>
         (fix aux (p : seq A₂) : seq A₂ :=
            match p with
            | [::] => [::]
            | a :: p0 =>
                (fix add_seqpoly_fun (p1 q : seq A₂) {struct p1} : 
                 seq A₂ :=
                   match p1 with
                   | [::] => q
                   | a0 :: p' =>
                       match q with
                       | [::] => p1
                       | b :: q' => H1₂ a0 b :: add_seqpoly_fun p' q'
                       end
                   end)
                  ((fix map (s : seq A₂) : seq A₂ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₂ a x :: map s'
                      end) (loop i)) (H₂ :: aux p0)
            end) p₂
     end in
 fix loop_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct m_R} :
   list_R A_R (fix_loop_1 m₁) (fix_loop_2 m₂) :=
   match m_R in (nat_R m₁0 m₂0) return (list_R A_R (fix_loop_1 m₁0) (fix_loop_2 m₂0)) with
   | nat_R_O_R => list_R_cons_R H0_R (list_R_nil_R A_R)
   | @nat_R_S_R i₁ i₂ i_R =>
       (let fix_aux_1 :=
          fix aux (p : seq A₁) : seq A₁ :=
            match p with
            | [::] => [::]
            | a :: p0 =>
                (fix add_seqpoly_fun (p1 q : seq A₁) {struct p1} : 
                 seq A₁ :=
                   match p1 with
                   | [::] => q
                   | a0 :: p' =>
                       match q with
                       | [::] => p1
                       | b :: q' => H1₁ a0 b :: add_seqpoly_fun p' q'
                       end
                   end)
                  ((fix map (s : seq A₁) : seq A₁ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₁ a x :: map s'
                      end) (fix_loop_1 i₁)) (H₁ :: aux p0)
            end in
        let fix_aux_2 :=
          fix aux (p : seq A₂) : seq A₂ :=
            match p with
            | [::] => [::]
            | a :: p0 =>
                (fix add_seqpoly_fun (p1 q : seq A₂) {struct p1} : 
                 seq A₂ :=
                   match p1 with
                   | [::] => q
                   | a0 :: p' =>
                       match q with
                       | [::] => p1
                       | b :: q' => H1₂ a0 b :: add_seqpoly_fun p' q'
                       end
                   end)
                  ((fix map (s : seq A₂) : seq A₂ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₂ a x :: map s'
                      end) (fix_loop_2 i₂)) (H₂ :: aux p0)
            end in
        fix aux_R (p₁0 : seq A₁) (p₂0 : seq A₂) (p_R0 : list_R A_R p₁0 p₂0) {struct p_R0} :
          list_R A_R (fix_aux_1 p₁0) (fix_aux_2 p₂0) :=
          match
            p_R0 in (list_R _ p₁1 p₂1) return (list_R A_R (fix_aux_1 p₁1) (fix_aux_2 p₂1))
          with
          | @list_R_nil_R _ _ _ => list_R_nil_R A_R
          | @list_R_cons_R _ _ _ a₁ a₂ a_R p₁1 p₂1 p_R1 =>
              (let fix_add_seqpoly_fun_1 :=
                 fix add_seqpoly_fun (p q : seq A₁) {struct p} : 
                 seq A₁ :=
                   match p with
                   | [::] => q
                   | a :: p' =>
                       match q with
                       | [::] => p
                       | b :: q' => H1₁ a b :: add_seqpoly_fun p' q'
                       end
                   end in
               let fix_add_seqpoly_fun_2 :=
                 fix add_seqpoly_fun (p q : seq A₂) {struct p} : 
                 seq A₂ :=
                   match p with
                   | [::] => q
                   | a :: p' =>
                       match q with
                       | [::] => p
                       | b :: q' => H1₂ a b :: add_seqpoly_fun p' q'
                       end
                   end in
               fix
               add_seqpoly_fun_R (p₁2 : seq A₁) (p₂2 : seq A₂) 
                                 (p_R2 : list_R A_R p₁2 p₂2) (q₁ : seq A₁) 
                                 (q₂ : seq A₂) (q_R : list_R A_R q₁ q₂) {struct p_R2} :
                 list_R A_R (fix_add_seqpoly_fun_1 p₁2 q₁) (fix_add_seqpoly_fun_2 p₂2 q₂) :=
                 let gen_path :
                   forall (A : Type) (H1 : A -> A -> A),
                   let
                     fix add_seqpoly_fun (p q : seq A) {struct p} : 
                     seq A :=
                       match p with
                       | [::] => q
                       | a :: p' =>
                           match q with
                           | [::] => p
                           | b :: q' => H1 a b :: add_seqpoly_fun p' q'
                           end
                       end in
                   forall p q : seq A,
                   match p with
                   | [::] => q
                   | a :: p' =>
                       match q with
                       | [::] => p
                       | b :: q' => H1 a b :: add_seqpoly_fun p' q'
                       end
                   end = add_seqpoly_fun p q :=
                   fun (A : Type) (H1 : A -> A -> A) =>
                   let add_seqpoly_fun0 :=
                     fix add_seqpoly_fun (p q : seq A) {struct p} : 
                     seq A :=
                       match p with
                       | [::] => q
                       | a :: p' =>
                           match q with
                           | [::] => p
                           | b :: q' => H1 a b :: add_seqpoly_fun p' q'
                           end
                       end in
                   fun p q : seq A =>
                   match
                     p as l
                     return
                       (match l with
                        | [::] => q
                        | a :: p' =>
                            match q with
                            | [::] => l
                            | b :: q' => H1 a b :: add_seqpoly_fun0 p' q'
                            end
                        end = add_seqpoly_fun0 l q)
                   with
                   | [::] => erefl (add_seqpoly_fun0 [::] q)
                   | a :: p0 => erefl (add_seqpoly_fun0 (a :: p0) q)
                   end in
                 eq_rect
                   match p₁2 with
                   | [::] => q₁
                   | a :: p' =>
                       match q₁ with
                       | [::] => p₁2
                       | b :: q' => H1₁ a b :: fix_add_seqpoly_fun_1 p' q'
                       end
                   end ((list_R A_R)^~ (fix_add_seqpoly_fun_2 p₂2 q₂))
                   (eq_rect
                      match p₂2 with
                      | [::] => q₂
                      | a :: p' =>
                          match q₂ with
                          | [::] => p₂2
                          | b :: q' => H1₂ a b :: fix_add_seqpoly_fun_2 p' q'
                          end
                      end
                      [eta list_R A_R
                             match p₁2 with
                             | [::] => q₁
                             | a :: p' =>
                                 match q₁ with
                                 | [::] => p₁2
                                 | b :: q' => H1₁ a b :: fix_add_seqpoly_fun_1 p' q'
                                 end
                             end]
                      match
                        p_R2 in (list_R _ p₁3 p₂3)
                        return
                          (list_R A_R
                             match p₁3 with
                             | [::] => q₁
                             | a :: p' =>
                                 match q₁ with
                                 | [::] => p₁2
                                 | b :: q' => H1₁ a b :: fix_add_seqpoly_fun_1 p' q'
                                 end
                             end
                             match p₂3 with
                             | [::] => q₂
                             | a :: p' =>
                                 match q₂ with
                                 | [::] => p₂2
                                 | b :: q' => H1₂ a b :: fix_add_seqpoly_fun_2 p' q'
                                 end
                             end)
                      with
                      | @list_R_nil_R _ _ _ => q_R
                      | @list_R_cons_R _ _ _ a₁0 a₂0 a_R0 p'₁ p'₂ p'_R =>
                          match
                            q_R in (list_R _ q₁0 q₂0)
                            return
                              (list_R A_R
                                 match q₁0 with
                                 | [::] => p₁2
                                 | b :: q' => H1₁ a₁0 b :: fix_add_seqpoly_fun_1 p'₁ q'
                                 end
                                 match q₂0 with
                                 | [::] => p₂2
                                 | b :: q' => H1₂ a₂0 b :: fix_add_seqpoly_fun_2 p'₂ q'
                                 end)
                          with
                          | @list_R_nil_R _ _ _ => p_R2
                          | @list_R_cons_R _ _ _ b₁ b₂ b_R q'₁ q'₂ q'_R =>
                              list_R_cons_R (H1_R a₁0 a₂0 a_R0 b₁ b₂ b_R)
                                (add_seqpoly_fun_R p'₁ p'₂ p'_R q'₁ q'₂ q'_R)
                          end
                      end (fix_add_seqpoly_fun_2 p₂2 q₂) (gen_path A₂ H1₂ p₂2 q₂))
                   (fix_add_seqpoly_fun_1 p₁2 q₁) (gen_path A₁ H1₁ p₁2 q₁))
                ((fix map (s : seq A₁) : seq A₁ :=
                    match s with
                    | [::] => [::]
                    | x :: s' => H3₁ a₁ x :: map s'
                    end) (fix_loop_1 i₁))
                ((fix map (s : seq A₂) : seq A₂ :=
                    match s with
                    | [::] => [::]
                    | x :: s' => H3₂ a₂ x :: map s'
                    end) (fix_loop_2 i₂))
                ((let fix_map_1 :=
                    fix map (s : seq A₁) : seq A₁ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₁ a₁ x :: map s'
                      end in
                  let fix_map_2 :=
                    fix map (s : seq A₂) : seq A₂ :=
                      match s with
                      | [::] => [::]
                      | x :: s' => H3₂ a₂ x :: map s'
                      end in
                  fix
                  map_R (s₁ : seq A₁) (s₂ : seq A₂) (s_R : list_R A_R s₁ s₂) {struct s_R} :
                    list_R A_R (fix_map_1 s₁) (fix_map_2 s₂) :=
                    match
                      s_R in (list_R _ s₁0 s₂0)
                      return (list_R A_R (fix_map_1 s₁0) (fix_map_2 s₂0))
                    with
                    | @list_R_nil_R _ _ _ => list_R_nil_R A_R
                    | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
                        list_R_cons_R (H3_R a₁ a₂ a_R x₁ x₂ x_R) (map_R s'₁ s'₂ s'_R)
                    end) (fix_loop_1 i₁) (fix_loop_2 i₂) (loop_R i₁ i₂ i_R))
                (H₁ :: fix_aux_1 p₁1) (H₂ :: fix_aux_2 p₂1)
                (list_R_cons_R H_R (aux_R p₁1 p₂1 p_R1))
          end) p₁ p₂ p_R
   end) (H9₁ n₁) (H9₂ n₂) (H9_R n₁ n₂ n_R).
Realizer exp_seqpoly as exp_seqpoly_R := exp_seqpoly'_R.
Parametricity size_seqpoly.
Definition eq_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂),
       (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂ ->
       forall (H1₁ : add_of A₁) (H1₂ : add_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         A₁ A₂ A_R H1₁ H1₂ ->
       forall (H2₁ : opp_of A₁) (H2₂ : opp_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0) (H0 : A₂0 -> A₂0)
        => forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> A_R0 (H H1) (H0 H2)) A₁ A₂ A_R H2₁
         H2₂ ->
       forall (H4₁ : eq_of A₁) (H4₂ : eq_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
          (H0 : A₂0 -> A₂0 -> bool) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 ->
        forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
         H4₁ H4₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
          (H0 : A₂0 -> A₂0 -> bool) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 ->
        forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4))
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
         (eq_seqpoly (A:=A₁)) (eq_seqpoly (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂)
  (H_R : (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂) (H1₁ : add_of A₁) 
  (H1₂ : add_of A₂)
  (H1_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
            H1₁ H1₂) (H2₁ : opp_of A₁) (H2₂ : opp_of A₂)
  (H2_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> A_R0 (H H1) (H0 H2)) A₁ A₂ A_R H2₁
            H2₂) (H4₁ : eq_of A₁) (H4₂ : eq_of A₂)
  (H4_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
             (H0 : A₂0 -> A₂0 -> bool) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂
            A_R H4₁ H4₂) (p₁ : seqpoly A₁) (p₂ : seqpoly A₂)
  (p_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R p₁ p₂) 
  (q₁ : seqpoly A₁) (q₂ : seqpoly A₂)
  (q_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R q₁ q₂) =>
all_R
  (fun (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂) =>
   (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (eq_of₁ : eq_of A₁0)
      (eq_of₂ : eq_of A₂0) => id) A₁ A₂ A_R H4₁ H4₂ H4_R x₁ x₂ x_R 0%C 0%C
     ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (zero_of₁ : zero_of A₁0)
         (zero_of₂ : zero_of A₂0) => id) A₁ A₂ A_R H₁ H₂ H_R))
  ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (sub_of₁ : sub_of A₁0)
      (sub_of₂ : sub_of A₂0) => id) (seqpoly A₁) (seqpoly A₂)
     ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) 
     (sub_seqpoly (A:=A₁)) (sub_seqpoly (A:=A₂)) (sub_seqpoly_R H1_R H2_R) p₁ p₂ p_R q₁ q₂
     q_R).
Parametricity shift_seqpoly.
Definition split_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type)
         (N_R : N₁ -> N₂ -> Type) (H9₁ : spec_of N₁ nat) (H9₂ : spec_of N₂ nat),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
          (B_R : B₁ -> B₂ -> Type) (H : A₁0 -> B₁) (H0 : A₂0 -> B₂) =>
        forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> B_R (H H1) (H0 H2)) N₁ N₂ N_R nat nat
         nat_R H9₁ H9₂ ->
       (fun (polyA₁ polyA₂ : Type) (polyA_R : polyA₁ -> polyA₂ -> Type) 
          (N₁0 N₂0 : Type) (N_R0 : N₁0 -> N₂0 -> Type)
          (H : N₁0 -> polyA₁ -> polyA₁ * polyA₁) (H0 : N₂0 -> polyA₂ -> polyA₂ * polyA₂) =>
        forall (H1 : N₁0) (H2 : N₂0),
        N_R0 H1 H2 ->
        forall (H3 : polyA₁) (H4 : polyA₂),
        polyA_R H3 H4 -> prod_R polyA_R polyA_R (H H1 H3) (H0 H2 H4)) 
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R) N₁ N₂ N_R
         (split_seqpoly (N:=N₁)) (split_seqpoly (N:=N₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type) (N_R : N₁ -> N₂ -> Type)
  (H9₁ : spec_of N₁ nat) (H9₂ : spec_of N₂ nat)
  (H9_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
             (B_R : B₁ -> B₂ -> Type) (H : A₁0 -> B₁) (H0 : A₂0 -> B₂) =>
           forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> B_R (H H1) (H0 H2)) N₁ N₂ N_R nat
            nat nat_R H9₁ H9₂) (n₁ : N₁) (n₂ : N₂) (n_R : N_R n₁ n₂) 
  (p₁ : seqpoly A₁) (p₂ : seqpoly A₂)
  (p_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R p₁ p₂) =>
prod_R_pair_R
  (drop_R
     ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
         (B_R : B₁ -> B₂ -> Type) (spec_of₁ : spec_of A₁0 B₁) (spec_of₂ : spec_of A₂0 B₂)
       => id) N₁ N₂ N_R nat nat nat_R H9₁ H9₂ H9_R n₁ n₂ n_R) p_R)
  (take_R
     ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
         (B_R : B₁ -> B₂ -> Type) (spec_of₁ : spec_of A₁0 B₁) (spec_of₂ : spec_of A₂0 B₂)
       => id) N₁ N₂ N_R nat nat nat_R H9₁ H9₂ H9_R n₁ n₂ n_R) p_R).
Definition lead_coef_seqpoly_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type)
         (N_R : N₁ -> N₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂),
       (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂ ->
       forall (H4₁ : eq_of A₁) (H4₂ : eq_of A₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
          (H0 : A₂0 -> A₂0 -> bool) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 ->
        forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R
         H4₁ H4₂ ->
       forall (H5₁ : zero_of N₁) (H5₂ : zero_of N₂),
       (fun A₁0 A₂0 : Type => id) N₁ N₂ N_R H5₁ H5₂ ->
       forall (H6₁ : one_of N₁) (H6₂ : one_of N₂),
       (fun A₁0 A₂0 : Type => id) N₁ N₂ N_R H6₁ H6₂ ->
       forall (H7₁ : add_of N₁) (H7₂ : add_of N₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
          (H0 : A₂0 -> A₂0 -> A₂0) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 -> forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4))
         N₁ N₂ N_R H7₁ H7₂ ->
       forall (H8₁ : eq_of N₁) (H8₂ : eq_of N₂),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
          (H0 : A₂0 -> A₂0 -> bool) =>
        forall (H1 : A₁0) (H2 : A₂0),
        A_R0 H1 H2 ->
        forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R
         H8₁ H8₂ ->
       forall (H9₁ : spec_of N₁ nat) (H9₂ : spec_of N₂ nat),
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
          (B_R : B₁ -> B₂ -> Type) (H : A₁0 -> B₁) (H0 : A₂0 -> B₂) =>
        forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> B_R (H H1) (H0 H2)) N₁ N₂ N_R nat nat
         nat_R H9₁ H9₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (polyA₁ polyA₂ : Type)
          (polyA_R : polyA₁ -> polyA₂ -> Type) (H : polyA₁ -> A₁0) 
          (H0 : polyA₂ -> A₂0) =>
        forall (H1 : polyA₁) (H2 : polyA₂), polyA_R H1 H2 -> A_R0 (H H1) (H0 H2)) A₁ A₂ A_R
         (seqpoly A₁) (seqpoly A₂)
         ((fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R)
         (lead_coef_seqpoly (N:=N₁)) (lead_coef_seqpoly (N:=N₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (N₁ N₂ : Type) (N_R : N₁ -> N₂ -> Type)
  (H₁ : zero_of A₁) (H₂ : zero_of A₂) (H_R : (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂)
  (H4₁ : eq_of A₁) (H4₂ : eq_of A₂)
  (H4_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
             (H0 : A₂0 -> A₂0 -> bool) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) A₁ A₂
            A_R H4₁ H4₂) (H5₁ : zero_of N₁) (H5₂ : zero_of N₂)
  (H5_R : (fun A₁0 A₂0 : Type => id) N₁ N₂ N_R H5₁ H5₂) (H6₁ : one_of N₁) 
  (H6₂ : one_of N₂) (H6_R : (fun A₁0 A₂0 : Type => id) N₁ N₂ N_R H6₁ H6₂) 
  (H7₁ : add_of N₁) (H7₂ : add_of N₂)
  (H7_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> A₁0)
             (H0 : A₂0 -> A₂0 -> A₂0) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> A_R0 (H H1 H3) (H0 H2 H4)) N₁ N₂ N_R
            H7₁ H7₂) (H8₁ : eq_of N₁) (H8₂ : eq_of N₂)
  (H8_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H : A₁0 -> A₁0 -> bool)
             (H0 : A₂0 -> A₂0 -> bool) =>
           forall (H1 : A₁0) (H2 : A₂0),
           A_R0 H1 H2 ->
           forall (H3 : A₁0) (H4 : A₂0), A_R0 H3 H4 -> bool_R (H H1 H3) (H0 H2 H4)) N₁ N₂
            N_R H8₁ H8₂) (H9₁ : spec_of N₁ nat) (H9₂ : spec_of N₂ nat)
  (H9_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
             (B_R : B₁ -> B₂ -> Type) (H : A₁0 -> B₁) (H0 : A₂0 -> B₂) =>
           forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> B_R (H H1) (H0 H2)) N₁ N₂ N_R nat
            nat nat_R H9₁ H9₂) (p₁ : seqpoly A₁) (p₂ : seqpoly A₂)
  (p_R : (fun A₁0 A₂0 : Type => [eta list_R (A₂:=A₂0)]) A₁ A₂ A_R p₁ p₂) =>
nth_R
  ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (zero_of₁ : zero_of A₁0)
      (zero_of₂ : zero_of A₂0) => id) A₁ A₂ A_R H₁ H₂ H_R) p_R
  ((fun (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) =>
    match
      n_R in (nat_R n₁0 n₂0)
      return
        (nat_R match n₁0 with
               | 0 => n₁
               | succn u => u
               end match n₂0 with
                   | 0 => n₂
                   | succn u => u
                   end)
    with
    | nat_R_O_R => n_R
    | @nat_R_S_R _ _ u_R => u_R
    end) (spec (size_seqpoly p₁)) (spec (size_seqpoly p₂))
     ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
         (B_R : B₁ -> B₂ -> Type) (spec_of₁ : spec_of A₁0 B₁) (spec_of₂ : spec_of A₂0 B₂)
       => id) N₁ N₂ N_R nat nat nat_R H9₁ H9₂ H9_R (size_seqpoly p₁) 
        (size_seqpoly p₂) (size_seqpoly_R H_R H4_R H5_R H6_R H7_R H8_R p_R))).

Section seqpoly_more_op.

Variable R : ringType.

Context (C : Type).
Context `{zero_of C, one_of C, add_of C, opp_of C, eq_of C}.
Context `{spec_of C R}.

Fixpoint spec_seqpoly_aux n (s : seqpoly C) : {poly R} :=
  match s with
      | [::] => 0
      | (hd :: tl) =>
        if (hd == 0)%C then spec_seqpoly_aux n.+1 tl
        else
          let c := if (n == 0%N) then if (hd == 1)%C then 1 else (spec hd)%:P
                   else let mon := if (n == 1%N) then 'X else 'X^n in
                        if (hd == 1)%C then mon else (spec hd) *: mon
          in
          if (tl == 0)%C then c
          else (spec_seqpoly_aux n.+1 tl) + c
  end.

Global Instance spec_seqpoly : spec_of (seqpoly C) {poly R}:=
  spec_seqpoly_aux 0%N.

Lemma spec_aux_shift n s :
  spec_seqpoly_aux n s = spec_seqpoly_aux 0 s * 'X^n.
Proof.
  elim: s n=> [n|a s ih n] /=; first by rewrite mul0r.
  simpC; case: ifP=> _.
    by rewrite ih [in RHS]ih exprS expr1 mulrA.
  have h : (if n == 0%N then if (a ==1)%C then 1 else (spec a)%:P else
            if (a == 1)%C then if n == 1%N then 'X : {poly R} else 'X^n else
              spec a *: (if n == 1%N then 'X else 'X^n)) =
         (if (a == 1)%C then 1 else (spec a)%:P) * 'X^n.
    case: n=> [|n] /=; simpC.
    rewrite expr0 mulr1.
    by case: ifP=> [/eqP a1|_].
    case: ifP=> [/eqP a1|_].
      rewrite mul1r.
      by case: ifP; move/eqP=> // ->; rewrite expr1.
    rewrite mul_polyC.
    by case: ifP; move/eqP=> // ->; rewrite expr1.
  case: ifP=> _; first by rewrite h.
  rewrite ih [in RHS]ih mulrDl exprS expr1 mulrA.
  exact: congr2.
Qed.

(* Cyril: fix this *)
Lemma spec_aux_eq0 s :
  (s == 0)%C -> spec_seqpoly_aux 0 s = 0.
Proof.
elim: s=> [_|a s ih aseq0] //=.
have heq0 : (a == 0)%C /\ (s == 0)%C.
  move: aseq0; rewrite /(_ == _)%C /eq_seqpoly /= => /andP [a0 s0].
  split => //; rewrite /eq_op /eq_seqpoly sub_seqpoly_0.
  by rewrite s0.
by rewrite (proj1 heq0) spec_aux_shift ih ?(proj2 heq0) // mul0r.
Qed.

End seqpoly_more_op.

Arguments spec_seqpoly / _ _ _ _ _ _ _ _ _ : assert.

(* (* translations for ringType *) *)
(* Parametricity Logic.False. *)
(* Parametricity reflect. *)
(* Parametricity Equality.mixin_of as equality_mixin_of_R. *)
(* Parametricity Logic.ex. *)
(* Parametricity Choice.mixin_of as choice_mixin_of_R. *)
(* Parametricity Choice.class_of as choice_class_of_R. *)
(* Parametricity GRing.Zmodule.mixin_of as gRing_Zmodule_mixin_of_R. *)
(* Parametricity GRing.Zmodule.class_of as gRing_Zmodule_class_of_R. *)
(* Parametricity GRing.Zmodule.type as gRing_Zmodule_type_R. *)
(* Parametricity Equality.type as equality_type_R. *)
(* Parametricity GRing.Ring.mixin_of as gRing_Ring_mixin_of_R. *)
(* Parametricity GRing.Ring.class_of as gRing_Ring_class_of_R. *)
(* Parametricity GRing.Ring.type as gRing_Ring_type_R. *)

(* (* translations for poly *) *)
(* Parametricity phant. *)
(* Parametricity polynomial. *)

Section seqpoly_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R  := 1%R.
Local Instance addR  : add_of R  := +%R.
Local Instance mulR  : mul_of R  := *%R.
Local Instance oppR  : opp_of R  := -%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.
Local Instance specR : spec_of R R := spec_id.

Local Instance zero_nat : zero_of nat := 0%N.
Local Instance one_nat  : one_of nat  := 1%N.
Local Instance add_nat  : add_of nat  := addn.
Local Instance eq_nat   : eq_of nat   := eqtype.eq_op.
Local Instance spec_nat : spec_of nat nat := spec_id.

Definition seqpoly_of_poly (p : {poly R}) : seqpoly R :=
  polyseq p.

Definition poly_of_seqpoly (sp : seqpoly R) : {poly R} :=
  \poly_(i < size sp) nth 0 sp i.

Definition Rseqpoly : {poly R} -> seqpoly R -> Type := fun_hrel poly_of_seqpoly.

Local Open Scope rel_scope.

(* zero and one *)
Local Instance Rseqpoly_0 : refines Rseqpoly 0%R 0%C.
Proof.
  by rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly poly_def big_ord0.
Qed.

Local Instance Rseqpoly_1 : refines Rseqpoly 1%R 1%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly poly_def /=.
  by rewrite zmodp.big_ord1 expr0 alg_polyC [(1%:P)]/(1%C) polyC1.
Qed.

Local Instance Rseqpoly_cons :
  refines (eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x -> _ sp <-.
  rewrite cons_poly_def poly_def big_ord_recl /= expr0 alg_polyC addrC.
  rewrite /bump poly_def big_distrl /=.
  apply: congr2=> //.
  apply: eq_bigr=> i _.
  by rewrite -[in RHS]mul_polyC -mulrA -exprSr mul_polyC.
Qed.

Local Instance Rseqpoly_cast : refines (eq ==> Rseqpoly) polyC cast_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x ->.
  rewrite /cast /cast_seqpoly /= poly_def zmodp.big_ord1 /=.
  by rewrite expr0 alg_polyC.
Qed.

Local Instance Rseqpoly_opp : refines (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <-.
  rewrite !poly_def -GRing.sumrN size_map.
  apply: eq_bigr=> i _.
  rewrite -[in RHS]mul_polyC -mulNr -polyC_opp mul_polyC.
  by rewrite (nth_map 0%C).
Qed.

Lemma coef_poly_of_seqpoly (sp : seqpoly R) (i : nat) :
  (\poly_(j < size sp) sp`_j)`_i = sp`_i.
Proof.
  rewrite coef_poly.
  have [iltp|pleqi] := ltnP i (size sp)=> //.
  by rewrite nth_default.
Qed.

Lemma coef_add_seqpoly (sp sq : seqpoly R) (i : nat) :
  (sp + sq)%C`_i = sp`_i + sq`_i.
Proof.
  elim: sp sq i=> [sq i|a p ihp [|b q] [|i]] //=.
        by rewrite [(_ + _)%C]/add_seqpoly /add_seqpoly_fun nth_nil add0r.
      by rewrite addr0.
    by rewrite addr0.
  by rewrite ihp.
Qed.

Local Instance Rseqpoly_add :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  by rewrite coef_add_poly !coef_poly_of_seqpoly coef_add_seqpoly.
Qed.

Lemma coef_opp_seqpoly (sp : seqpoly R) (i : nat) : (- sp)%C`_i = - sp`_i.
Proof.
  have [iltp|pleqi] := ltnP i (size sp).
    by rewrite (nth_map 0%C).
  by rewrite !nth_default ?oppr0 ?size_map.
Qed.

Local Instance Rseqpoly_sub :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (fun x y => x - y) sub_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  rewrite coef_add_poly coef_opp_poly !coef_poly_of_seqpoly coef_add_seqpoly.
  by rewrite coef_opp_seqpoly.
Qed.

(* scaling *)

Lemma coef_scale_seqpoly (sp : seqpoly R) (a : R) (i : nat) :
  (a *: sp)%C`_i = a * sp`_i.
Proof.
  have [iltp|pleqi] := ltnP i (size sp).
    by rewrite (nth_map 0%C).
  by rewrite !nth_default ?mulr0 ?size_map.
Qed.

Local Instance Rseqpoly_scale :
  refines (eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x -> _ sp <-.
  apply/polyP=> i.
  by rewrite coefZ !coef_poly_of_seqpoly coef_scale_seqpoly.
Qed.

(* multiplication *)
Local Instance Rseqpoly_mul :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  rewrite coef_poly_of_seqpoly.
  elim: sp i=> [i|a p ihp i].
    by rewrite [(_ * _)%C]/mul_seqpoly poly_def big_ord0 mul0r coef0 nth_nil.
  rewrite [(_ * _)%C]/mul_seqpoly coef_add_seqpoly coefM big_ord_recl.
  rewrite !coef_poly_of_seqpoly subn0.
  apply: congr2; first by rewrite coef_scale_seqpoly.
  move: ihp; case: i=> [_|i ihp]; first by rewrite big_ord0.
  rewrite [(_ :: _)`_ _]/= ihp coefM=> {ihp}.
  apply: eq_bigr=> j _.
  by rewrite !coef_poly_of_seqpoly.
Qed.

Local Instance Rseqpoly_exp :
  refines (Rseqpoly ==> Logic.eq ==> Rseqpoly) (@GRing.exp _) exp_op.
Proof.
  apply refines_abstr2=> p sp hp m n; rewrite refinesE=> -> {m}.
  rewrite /exp_op /exp_seqpoly.
  elim: n=> [|n ihn] /=;
    by rewrite ?(expr0, exprS); tc.
Qed.

Lemma poly_cons (p : seqpoly R) (a : R) :
  \poly_(i < size (a :: p)) (a :: p)`_i = a%:P + (\poly_(i < size p) p`_i) * 'X.
Proof.
  rewrite !poly_def big_ord_recl big_distrl /= expr0 alg_polyC /bump /=.
  apply: congr2=> //; apply: eq_bigr=> i _.
  by rewrite add1n exprSr scalerAl.
Qed.

Local Instance Rseqpoly_size :
  refines (Rseqpoly ==> eq) (sizep (R:=R)) (size_op (N:=nat)).
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <-.
  rewrite sizepE /size_op.
  elim: sp=> [|a p ihp].
    by rewrite poly_def big_ord0 size_poly0.
  rewrite poly_cons /= -ihp.
  case sp: (size (\poly_(i < size p) p`_i))=> [|n] /=; simpC.
    move /eqP: sp; rewrite size_poly_eq0; move/eqP=> ->.
    by rewrite mul0r addr0 size_polyC; case: (a == 0).
  rewrite addrC size_addl size_mulX ?sp ?size_polyC ?addn1; case: (a != 0)=> //;
  by apply/negP; rewrite -size_poly_eq0 sp.
Qed.

Local Instance Rseqpoly_eq :
  refines (Rseqpoly ==> Rseqpoly ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  have -> : (\poly_(i < size sp) sp`_i == \poly_(i < size sq) sq`_i)
            = (sp == sq)%C.
    apply/eqP/allP=> [/polyP heq|heq].
      move=> x /(nthP 0%C) [i] hi <-.
      rewrite coef_add_seqpoly coef_opp_seqpoly; simpC.
      by have := (heq i); rewrite !coef_poly_of_seqpoly subr_eq0=> ->.
    apply/polyP=> i; rewrite !coef_poly_of_seqpoly; apply/eqP.
    have [hlt|] := ltnP i (size (sp - sq)%C).
      rewrite -subr_eq0 -coef_opp_seqpoly -coef_add_seqpoly [_ == _]heq //.
      by rewrite mem_nth.
    have -> : size (sp - sq)%C = maxn (size sp) (size sq)=> [{heq}|hleq].
      elim: sp sq=> [sq|a p ihp [|b q]] /=.
          by rewrite max0n [(_ - _)%C]/add_seqpoly /add_seqpoly_fun size_map.
        by rewrite maxn0.
      by rewrite ihp maxnSS.
    by rewrite !nth_default // (leq_trans _ hleq) // leq_max leqnn ?orbT.
  exact: bool_Rxx.
Qed.

(* These can be done with eq instead of nat_R *)
Local Instance Rseqpoly_shift :
  refines (eq ==> Rseqpoly ==> Rseqpoly) (shiftp (R:=R)) (shift_op (N:=nat)).
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ n -> _ sp <-.
  apply/polyP=> i.
  rewrite /shiftp coefMXn !coef_poly_of_seqpoly /shift_op /shift_seqpoly.
  by rewrite nth_ncons.
Qed.

Local Instance Rseqpoly_split :
  refines (eq ==> Rseqpoly ==> prod_R Rseqpoly Rseqpoly)
          (splitp (R:=R)) (split_op (N:=nat)).
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ n -> _ sp <-.
  rewrite /split_op /split_seqpoly /splitp /=.
  apply: prod_RI; rewrite /prod_hrel /=.
  elim: sp n=> [n|a p ihp [|n]].
      by rewrite poly_def big_ord0 rdiv0p rmod0p.
    by rewrite expr0 rdivp1 rmodp1 [\poly_(_ < 0) _]poly_def big_ord0.
  rewrite !poly_cons [\poly_(i < size p) p`_i](@rdivp_eq _ 'X^n) ?monicXn //.
  have [/= -> ->] := ihp n.
  rewrite mulrDl -mulrA -exprSr addrC -addrA.
  suff htnp :
    size (rmodp (\poly_(i < size p) p`_i) 'X^n * 'X + a%:P) <
    size ('X^n.+1 : {poly R}).
    by rewrite rdivp_addl_mul_small ?rmodp_addl_mul_small ?monicXn // addrC.
  rewrite size_polyXn size_MXaddC ltnS; case: ifP=> // _.
  by rewrite (leq_trans (ltn_rmodpN0 _ _)) ?monic_neq0 ?monicXn ?size_polyXn.
Qed.

Local Instance Rseqpoly_lead_coef :
  refines (Rseqpoly ==> eq) lead_coef (lead_coef_seqpoly (N:=nat)).
Proof.
  rewrite refinesE /lead_coef_seqpoly /lead_coef=> p sp hp.
  rewrite -sizepE [sizep _]refines_eq /size_op -hp /poly_of_seqpoly.
  by rewrite coef_poly_of_seqpoly.
Qed.

Local Instance Rseqpoly_head :
  refines (Rseqpoly ==> Logic.eq) (fun p => p`_0) (fun sp => nth 0%C sp 0).
Proof.
  rewrite refinesE=> _ sp <-.
  rewrite /poly_of_seqpoly coef_poly_of_seqpoly.
  by case: sp.
Qed.

Local Instance Rseqpoly_spec_l : refines (Rseqpoly ==> Logic.eq) spec_id spec.
Proof.
  rewrite refinesE=> _ sp <-.
  rewrite /spec_id /spec /spec_seqpoly /poly_of_seqpoly.
  elim: sp=> [|a p ih] /=.
    by rewrite poly_def big_ord0.
  rewrite spec_aux_shift expr1 poly_cons ih.
  simpC.
  case: ifP=> [/eqP a0|_]; first by rewrite a0 polyC0 add0r.
  rewrite /spec /specR /spec_id addrC.
  by case: ifP=> p0;
    case: ifP=> [/eqP a1|_];
    rewrite ?a1 ?polyC1 // spec_aux_eq0 // ?mul0r ?add0r.
Qed.

Section seqpoly_param.

Context (C : Type) (rAC : R -> C -> Type).
Context (N : Type) (rN : nat -> N -> Type).
Context `{zero_of C, one_of C}.
Context `{opp_of C, add_of C, mul_of C, eq_of C}.
Context `{implem_of R C, spec_of C R}.
Context `{zero_of N, one_of N, add_of N, eq_of N}.
Context `{spec_of N nat}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (rAC ==> Logic.eq) spec_id spec}.
Context `{!refines rN 0%N 0%C, !refines rN 1%N 1%C}.
Context `{!refines (rN ==> rN ==> rN) addn +%C}.
Context `{!refines (rN ==> rN ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (rN ==> nat_R) spec_id spec}.

Definition RseqpolyC : {poly R} -> seq C -> Type :=
  (Rseqpoly \o (list_R rAC)).

Global Instance RseqpolyC_cons :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) (@cons_poly R) cons.
Proof. param_comp list_R_cons_R. Qed.

Global Instance RseqpolyC_cast :
  refines (rAC ==> RseqpolyC) polyC cast_op.
Proof. param_comp cast_seqpoly_R. Qed.

Global Instance RseqpolyC_0 : refines RseqpolyC 0%R 0%C.
Proof. param_comp seqpoly0_R. Qed.

Global Instance RseqpolyC_1 : refines RseqpolyC 1%R 1%C.
Proof. param_comp seqpoly1_R. Qed.

Global Instance RseqpolyC_opp : refines (RseqpolyC ==> RseqpolyC) -%R -%C.
Proof. param_comp opp_seqpoly_R. Qed.

Global Instance RseqpolyC_add :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) +%R +%C.
Proof. param_comp add_seqpoly_R. Qed.

Global Instance RseqpolyC_sub :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (fun x y => x - y) sub_op.
Proof. param_comp sub_seqpoly_R. Qed.

Global Instance RseqpolyC_scale :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) *:%R *:%C.
Proof. param_comp scale_seqpoly_R. Qed.

Global Instance RseqpolyC_mul :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C.
Proof. param_comp mul_seqpoly_R. Qed.

Global Instance RseqpolyC_exp :
  refines (RseqpolyC ==> rN ==> RseqpolyC) (@GRing.exp _) exp_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (exp_seqpoly_R (N_R:=rN))=> // *;
    exact: refinesP.
Qed.

Global Instance RseqpolyC_size :
  refines (RseqpolyC ==> rN) (sizep (R:=R)) size_op.
Proof. rewrite /size_op; param_comp size_seqpoly_R. Qed.

Global Instance RseqpolyC_eq :
  refines (RseqpolyC ==> RseqpolyC ==> bool_R) eqtype.eq_op eq_op.
Proof. param_comp eq_seqpoly_R. Qed.

Global Instance RseqpolyC_shift :
  refines (rN ==> RseqpolyC ==> RseqpolyC) (shiftp (R:=R)) shift_op.
Proof.
  (* param_comp shift_seqpoly_R does a mistake on the instantiation of a
  relation, why? *)
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (shift_seqpoly_R (N_R:=rN))=> // *;
    exact: refinesP.
Qed.

Global Instance RseqpolyC_mulXn p sp n rn :
  refines rN n rn -> refines RseqpolyC p sp ->
  refines RseqpolyC (p * 'X^n) (shift_op rn sp).
Proof.
  move=> hn hp; rewrite -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

Lemma mulXnC (p : {poly R}) n : p * 'X^n = 'X^n * p.
Proof.
  apply/polyP=> i.
  by rewrite coefMXn coefXnM.
Qed.

Global Instance RseqpolyC_Xnmul p sp n rn :
  refines rN n rn -> refines RseqpolyC p sp ->
  refines RseqpolyC ('X^n * p) (shift_op rn sp).
Proof. rewrite -mulXnC; exact: RseqpolyC_mulXn. Qed.

Global Instance RseqpolyC_scaleXn c rc n rn :
  refines rN n rn -> refines rAC c rc ->
  refines RseqpolyC (c *: 'X^n) (shift_op rn (cast rc)).
Proof.
  move=> hn hc; rewrite -mul_polyC -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

Global Instance RseqpolyC_mulX p sp :
  refines RseqpolyC p sp -> refines RseqpolyC (p * 'X) (shift_op (1%C : N) sp).
Proof. rewrite -['X]expr1; exact: RseqpolyC_mulXn. Qed.

Global Instance RseqpolyC_Xmul p sp :
  refines RseqpolyC p sp -> refines RseqpolyC ('X * p) (shift_op (1%C : N) sp).
Proof. rewrite -['X]expr1 -mulXnC; exact: RseqpolyC_mulX. Qed.

Global Instance RseqpolyC_scaleX c rc :
  refines rAC c rc ->
  refines RseqpolyC (c *: 'X) (shift_op (1%C : N) (cast rc)).
Proof. rewrite -['X]expr1; exact: RseqpolyC_scaleXn. Qed.

(* Uses composable_prod *)
Global Instance RseqpolyC_split :
  refines (rN ==> RseqpolyC ==> prod_R RseqpolyC RseqpolyC)
    (splitp (R:=R)) split_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (split_seqpoly_R (N_R:=rN))=> // *.
  exact: refinesP.
Qed.

Global Instance RseqpolyC_splitn n rn p sp :
  refines rN n rn -> refines RseqpolyC p sp ->
  refines (prod_R RseqpolyC RseqpolyC) (splitp n p) (split_op rn sp).
Proof. by move=> hn hp; apply: refines_apply. Qed.

Definition eq_prod_seqpoly (x y : (seqpoly C * seqpoly C)) :=
  (eq_op x.1 y.1) && (eq_op x.2 y.2).

Global Instance refines_prod_RseqpolyC_eq :
  refines (prod_R RseqpolyC RseqpolyC ==> prod_R RseqpolyC RseqpolyC ==> bool_R)
          eqtype.eq_op eq_prod_seqpoly.
Proof.
  rewrite refinesE=> x x' hx y y' hy.
  rewrite /eqtype.eq_op /eq_prod_seqpoly /=.
  have -> : (x.1 == y.1) = (x'.1 == y'.1)%C.
    apply: refines_eq.
  have -> : (x.2 == y.2) = (x'.2 == y'.2)%C.
    apply: refines_eq.
  exact: bool_Rxx.
Qed.

Global Instance RseqpolyC_lead_coef :
  refines (RseqpolyC ==> rAC) lead_coef (lead_coef_seqpoly (N:=N)).
Proof.
param_comp lead_coef_seqpoly_R.
Qed.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: nat_Rxx. Qed.

Global Instance RseqpolyC_head :
  refines (RseqpolyC ==> rAC) (fun p => p`_0) (fun sp => nth 0%C sp 0).
Proof.
  eapply refines_trans; tc.
  rewrite refinesE=> l l' rl.
  apply nth_R; exact: refinesP.
Qed.

Global Instance RseqpolyC_X : refines RseqpolyC 'X (shift_op (1%C : N) 1)%C.
Proof. rewrite -['X]mul1r; exact: RseqpolyC_mulX. Qed.

Global Instance RseqpolyC_Xn n rn :
  refines rN n rn -> refines RseqpolyC 'X^n (shift_op rn 1)%C.
Proof. move=> hn; rewrite -['X^_]mul1r; exact: RseqpolyC_mulXn. Qed.

(* Lemma gRing_Ring_type_Rxx r : gRing_Ring_type_R r r. *)
(* Proof. *)
(* Admitted. *)

(* Global Instance RseqpolyC_spec_l : *)
(*   refines (RseqpolyC ==> (@polynomial_R _ _ (gRing_Ring_type_Rxx R))) *)
(*           spec_id spec. *)
(* Proof. *)
(* Admitted. *)

Global Instance RseqpolyC_spec : refines (RseqpolyC ==> eq) spec_id spec.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE=> l l' rl.
  elim: rl=> [|x y rx p q rp] {l l'};
    rewrite /spec /spec_seqpoly //=.
  rewrite ![spec_seqpoly_aux 1 _]spec_aux_shift=> ->.
  have -> : (p == 0)%C = (q == 0)%C.
    elim: rp=> [|a b ra l l' rl] {p q} //=.
    rewrite /eq_op /eq_seqpoly /=.
    by simpC; rewrite [(_ == _)]refines_eq !sub_seqpoly_0=> ->.
  rewrite /spec /specR [spec_id _]refines_eq /spec [(_ == _)%C]refines_eq.
  by rewrite [(_ == 1)%C]refines_eq.
Qed.

End seqpoly_param.

End seqpoly_theory.

(* Always simpl Poly. Maybe have refinement instance instead? Is this *)
(* more efficient? *)
Hint Extern 0 (refines _ (Poly _) _) => simpl : typeclass_instances.
Hint Extern 0 (refines _ _ (Poly _)) => simpl : typeclass_instances.

Section testpoly.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binnat binint.

Goal (0 == 0 :> {poly int}).
by coqeal.
Abort.

Goal (0 == (0 : {poly {poly {poly int}}})).
by coqeal.
Abort.

Goal (1 == 1 :> {poly int}).
by coqeal.
Abort.

Goal (1 == (1 : {poly {poly {poly int}}})).
by coqeal.
Abort.

Goal ((1 + 2%:Z *: 'X + 3%:Z *: 'X^2) + (1 + 2%:Z%:P * 'X + 3%:Z%:P * 'X^2)
      == (1 + 1 + (2%:Z + 2%:Z) *: 'X + (3%:Z + 3%:Z)%:P * 'X^2)).
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
by coqeal.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] + Poly [:: 1; 2%:Z; 3%:Z]) ==
      Poly [:: 1 + 1; 2%:Z + 2%:Z; 2%:Z + 4%:Z].
by coqeal.
Abort.

Goal (- 1 == - (1: {poly {poly int}})).
by coqeal.
Abort.

Goal (- (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2) == -1 - 2%:Z%:P * 'X - 3%:Z *: 'X^2).
by coqeal.
Abort.

Goal (- Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: - 1; - 2%:Z; - 3%:Z].
by coqeal.
Abort.

Goal (1 + 2%:Z *: 'X + 3%:Z *: 'X^2 - (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 0).
by coqeal.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] - Poly [:: 1; 2%:Z; 3%:Z]) == 0.
by coqeal.
Abort.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X) == 1 + 4%:Z *: 'X + 4%:Z *: 'X^2).
by coqeal.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
by coqeal.
Abort.

(* (1 + xy) * x = x + x^2y *)
Goal ((1 + 'X * 'X%:P) * 'X == 'X + 'X^2 * 'X%:P :> {poly {poly int}}).
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
by coqeal.
Abort.

Goal (Poly [:: Poly [:: 1; 0]; 1] * Poly [:: 1; 0]) ==
      Poly [:: Poly [:: 1; 0]; 1 ; 0] :> {poly {poly int}}.
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
by coqeal.
Abort.

Goal (sizep ('X^2 : {poly int}) ==
      sizep (- 3%:Z *: 'X^(sizep ('X : {poly int})))).
by coqeal.
Abort.

Goal (sizep (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 3).
by coqeal.
Abort.

Goal (sizep (Poly [:: 1; 2%:Z; 3%:Z]) == 3%nat).
by coqeal.
Abort.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X^(sizep (1 : {poly int}))) ==
      1 + 4%:Z *: 'X + 4%:Z *: 'X^(sizep (10%:Z *: 'X))).
by coqeal.
Abort.

Goal (splitp 2 (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2 + 4%:Z *: 'X^3) ==
      (3%:Z%:P + 4%:Z *: 'X, 1 + 2%:Z%:P * 'X)).
by coqeal.
Abort.

Goal (splitp (sizep ('X : {poly int}))
             (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2 + 4%:Z *: 'X^3) ==
      (3%:Z%:P + 4%:Z *: 'X, 1 + 2%:Z%:P * 'X)).
by coqeal.
Abort.

Goal (splitp 2%nat (Poly [:: 1; 2%:Z; 3%:Z; 4%:Z]) ==
     (Poly [:: 3%:Z; 4%:Z], Poly [:: 1; 2%:Z])).
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

(* Test shiftp *)
Goal (2%:Z *: shiftp 2%nat 1 == Poly [:: 0; 0; 2%:Z]).
by coqeal.
Abort.

End testpoly.
