(** * Main tactic for multivariate polynomial positivity. *)

Require Import ZArith.
From Flocq Require Import Fcore. Require Import Datatypes.
From Interval Require Import Interval_definitions Interval_xreal.
From Interval Require Import Interval_missing.
From CoqEAL.refinements Require Import hrel refinements param seqmx binint rational.
Require Import binrat.
Require Import Reals Flocq.Core.Fcore_Raux QArith CBigZ CBigQ Psatz FSetAVL.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype tuple matrix ssralg bigop.
From mathcomp Require Import ssrnum ssrint rat div.
From SsrMultinomials Require Import mpoly.
Require Import ssrmultinomials_complements.
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
Import Refinements.Op.
Require Import cholesky_prog coqinterval_infnan.
Require Import multipoly. Import PolyAVL.
From ValidSDP Require Import zulp.
Require Import seqmx_complements misc.
From ValidSDP Require Export soswitness.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Require Import parse_reals.

Inductive p_abstr_poly :=
  (* | Const of Poly.t *)
  (* | Mult_scalar of Poly.Coeff.t * abstr_poly *)
  | PConst of p_real_cst
  | PVar of nat
  | POpp of p_abstr_poly
  | PAdd of p_abstr_poly & p_abstr_poly
  | PSub of p_abstr_poly & p_abstr_poly
  | PMul of p_abstr_poly & p_abstr_poly
  | PPowN of p_abstr_poly & binnat.N
  | PPown of p_abstr_poly & nat
  | PCompose of p_abstr_poly & seq p_abstr_poly.

Fixpoint all_prop (T : Type) (a : T -> Prop) (s : seq T) : Prop :=
  match s with
  | [::] => True
  | x :: s' => a x /\ all_prop a s'
  end.

Lemma all_prop_nthP T (P : T -> Prop) (s : seq T) (x0 : T) :
  (forall i, (i < size s)%N -> P (nth x0 s i)) <-> all_prop P s.
Proof.
elim: s => [//|h t Ht] /=; split.
{ move=> H1; split; [by apply (H1 O)|].
  by apply Ht => i Hi; apply (H1 i.+1). }
by move=> [Hh Ht'] [|i] Hi //=; apply Ht.
Qed.

Lemma all_prop_forall T1 T2 (P : T1 -> T2 -> Prop) (s : seq T1) :
  all_prop (fun x : T1 => forall y : T2, P x y) s ->
  forall y : T2, all_prop (fun x : T1 => P x y) s.
Proof.
elim: s => [|x s IHs] H y =>//=.
by have /= [H1 H2] := H; split; last exact: IHs.
Qed.

Lemma eq_map_all_prop T1 T2 (f1 f2 : T1 ->  T2) (s : seq T1) :
  all_prop (fun x : T1 => f1 x = f2 x) s ->
  [seq f1 i | i <- s] =
  [seq f2 i | i <- s].
Proof.
elim: s => [|x s IHs] H //=.
have /= [-> H2] := H; congr cons; exact: IHs.
Qed.

Lemma all_prop_cat (T : Type) (a : T -> Prop) (s1 s2 : seq T) :
  all_prop a (s1 ++ s2) <-> all_prop a s1 /\ all_prop a s2.
Proof. by elim: s1 => [|x s1 IHs] //=; intuition. Qed.

Section Defix.
Variable (P : p_abstr_poly -> Prop).
Let P' := all_prop P.
Variable (f : forall p : p_real_cst, P (PConst p)).
Variable (f0 : forall n : nat, P (PVar n)) (f1 : forall p : p_abstr_poly, P p -> P (POpp p)).
Variable (f2 : forall p : p_abstr_poly, P p -> forall p0 : p_abstr_poly, P p0 -> P (PAdd p p0)).
Variable (f3 : forall p : p_abstr_poly, P p -> forall p0 : p_abstr_poly, P p0 -> P (PSub p p0)).
Variable (f4 : forall p : p_abstr_poly, P p -> forall p0 : p_abstr_poly, P p0 -> P (PMul p p0)).
Variable (f5 : forall p : p_abstr_poly, P p -> forall n : BinNums.N, P (PPowN p n)).
Variable (f6 : forall p : p_abstr_poly, P p -> forall n : nat, P (PPown p n)).
Variable (f7 : forall p : p_abstr_poly, P p -> forall l : seq p_abstr_poly, P' l -> P (PCompose p l)).

Fixpoint p_abstr_poly_ind' (p : p_abstr_poly) : P p :=
  let fix p_abstr_poly_ind2 (l : seq p_abstr_poly) : P' l :=
  match l as l0 return (P' l0) with
  | [::] => I
  | p :: l' => conj (p_abstr_poly_ind' p) (p_abstr_poly_ind2 l')
  end in
  match p as p0 return (P p0) with
  | PConst p0 => f p0
  | PVar n => f0 n
  | POpp p0 => f1 (p_abstr_poly_ind' p0)
  | PAdd p0 p1 => f2 (p_abstr_poly_ind' p0) (p_abstr_poly_ind' p1)
  | PSub p0 p1 => f3 (p_abstr_poly_ind' p0) (p_abstr_poly_ind' p1)
  | PMul p0 p1 => f4 (p_abstr_poly_ind' p0) (p_abstr_poly_ind' p1)
  | PPowN p0 n => f5 (p_abstr_poly_ind' p0) n
  | PPown p0 n => f6 (p_abstr_poly_ind' p0) n
  | PCompose p0 l => f7 (p_abstr_poly_ind' p0) (p_abstr_poly_ind2 l)
  end.
End Defix.

Fixpoint interp_p_abstr_poly (vm : seq R) (ap : p_abstr_poly) {struct ap} : R :=
  match ap with
  | PConst c => interp_p_real_cst c
  | POpp p => Ropp (interp_p_abstr_poly vm p)
  | PAdd p q => Rplus (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | PSub p q => Rminus (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | PMul p q => Rmult (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | PPowN p n => powerRZ (interp_p_abstr_poly vm p) (Z.of_N n)
  | PPown p n => pow (interp_p_abstr_poly vm p) n
  | PVar i => seq.nth R0 vm i
  | PCompose p qi => interp_p_abstr_poly (map (interp_p_abstr_poly vm) qi) p
  end.

(** [list_add] was taken from CoqInterval *)
Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | Datatypes.nil        => constr:((n, Datatypes.cons a l))
    | Datatypes.cons a _   => constr:((n, l))
    | Datatypes.cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, Datatypes.cons x l))
      end
    end in
  aux a l O.

(** [list_idx a l = (idx, l)], [idx] being the index of [a] in [l].
    Otherwise return [assert_false] *)
Ltac list_idx a l :=
  let rec aux a l n :=
    match l with
    | Datatypes.nil        => constr:((assert_false, l))
    | Datatypes.cons a _   => constr:((n, l))
    | Datatypes.cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, Datatypes.cons x l))
      end
    end in
  aux a l O.

Ltac reverse T l :=
  let rec aux l accu :=
    match l with
    | Datatypes.nil => accu
    | Datatypes.cons ?x ?l => aux l constr:(Datatypes.cons x accu)
    end in
  aux l (@Datatypes.nil T).

Ltac iter_tac tac l :=
  let rec aux l :=
    match l with
    | Datatypes.nil => idtac
    | Datatypes.cons ?x ?l => tac x; aux l
    end
  in aux l.

(** [equate] was taken from CPDT *)
Ltac equate x y :=
  let dummy := constr:(erefl x : x = y) in idtac.

(** Trick (evar-making tactic with continuation passing style) *)
Ltac newvar T k :=
  let x := fresh "dummy" in
  evar (x : T);
  let x' := (eval unfold x in x) in
  clear x;
  k x'.

Ltac deb tac := idtac.
(* Ltac deb tac ::= tac. *)

Ltac fold_get_poly get_poly lq vm k :=
  deb ltac:(idtac "fold_get_poly on .." lq vm "..");
  let z0 := constr:((@Datatypes.nil p_abstr_poly, vm)) in
  let rec aux lq vm k :=
      match lq with
      | Datatypes.nil => k z0
      | Datatypes.cons ?q1 ?lq1 =>
        aux lq1 vm ltac:(fun res =>
          match res with
          | (?lq2, ?vm1) =>
            get_poly q1 vm1 ltac:(fun res =>
              match res with
              | (?q2, ?vm2) =>
                let res := constr:((Datatypes.cons q2 lq2, vm2)) in k res
              end)
          end)
      end in
  aux lq vm k.

(** [get_comp_poly tac0 tac1 t vm tac2 k] will check if [t] matches [?f ?x] *)
Ltac get_comp_poly get_poly_cur get_poly_pure t vm tac_var k :=
  deb ltac:(idtac "get_comp_poly on .. .." t vm ".. ..");
  let rec aux2 f0 f qi xx vm k := (* Second step *)
      match type of f with
      | R =>
        let f := (eval unfold f0 in f) in
        let xx := reverse R xx in
        get_poly_pure f xx ltac:(fun res =>
          match res with
          | assert_false => k assert_false (* todo: remove and replace with match failure? *)
          | (?p, _) => (* Ignore the xx that is returned and that hasn't changed *)
            fold_get_poly get_poly_cur qi vm ltac:(fun res =>
              match res with
              | (?qi, ?vm) =>
                let res := constr:((PCompose p qi, vm)) in
                let dummy := R0 in
                iter_tac ltac:(fun it => equate it dummy) xx; k res
              end)
          end)
      | forall x : R, _ =>
        newvar R ltac:(fun x => let fx := constr:(f x) in
                             let xx := constr:(Datatypes.cons x xx) in
                             aux2 f0 fx qi xx vm k)
        (* TODO/FIXME: instantiate evars *)
      end in
  let rec aux1 t0 t qi vm k := (* First step *)
      match t with
      | ?p ?q =>
        let qi1 := constr:(Datatypes.cons q qi) in
        aux1 t0 p qi1 vm k
      | ?f =>
        aux2 f f qi (@Datatypes.nil R) vm ltac:(fun res =>
        match res with
        | assert_false => (* If second step fails, return a PVar *)
          match list_add t0 vm with
          | (?n, ?vm) => constr:((PVar n, vm))
          end
        | ?res => k res
        end)
      end in
  (* Ensure [t] is a function applied to a real *)
  match t with
  | ?fp ?xn =>
    match type of xn with
    | R => aux1 t t (@Datatypes.nil R) vm k
    | _ => tac_var t vm k
    end
  | _ => tac_var t vm k
  end.

(** [get_poly_pure t vm k] creates no var.
    Return [assert_false] if [t] isn't poly over [vm] *)
Ltac get_poly_pure t vm k :=
  deb ltac:(idtac "get_poly_pure on " t vm "..");
  let rec aux t vm k :=
    let aux_u o a k :=
      aux a vm ltac:(fun res =>
        match res with
        | (?u, ?vm) => let res := constr:((o u, vm)) in k res
        end) in
    let aux_u' o a b k :=
      aux a vm ltac:(fun res =>
        match res with
        | (?u, ?vm) => let res := constr:((o u b, vm)) in k res
        end) in
    let aux_b o a b k :=
      aux b vm ltac:(fun res =>
        match res with
        | (?v, ?vm) =>
          aux a vm ltac:(fun res =>
            match res with
            | (?u, ?vm) => let res := constr:((o u v, vm)) in k res
            end)
        end) in
    match t with
    | Rplus ?a ?b => aux_b PAdd a b k
    | Rminus ?a ?b => aux_b PSub a b k
    | Ropp ?a => aux_u POpp a k
    | Rmult ?a ?b => aux_b PMul a b k
 (* | Rsqr ?a => aux (Rmult a a) l *)
    | powerRZ ?a ?b =>
      match b with
      | Z.pos ?p => aux_u' PPowN a (N.pos p) k
      | _ => fail 200 "Only constant, positive exponents are allowed"
      end
    | pow ?a ?n => aux_u' PPown a n k
    | Rdiv ?a ?b => aux (Rmult a (Rinv b)) vm k (* Both are convertible *)
    | _ =>
      match get_real_cst t with
      | assert_false =>
        (* Differs w.r.t. get_poly *)
        get_comp_poly get_poly_pure get_poly_pure t vm ltac:(fun t vm k =>
          match list_idx t vm with
          | (assert_false, _) => k assert_false
          | (?n, ?vm) => let res := constr:((PVar n, vm)) in k res
          end) ltac:(fun res =>
          match res with
          | (?p, ?vm) => let res := constr:((p, vm)) in k res
          end)
      | ?c => let res := constr:((PConst c, vm)) in k res
      end
    end in
  aux t vm k.

Ltac get_poly t vm k :=
  deb ltac:(idtac "get_poly on" t vm "..");
  let rec aux t vm k :=
    let aux_u o a k :=
      aux a vm ltac:(fun res =>
        match res with
        | (?u, ?vm) => let res := constr:((o u, vm)) in k res
        end) in
    let aux_u' o a b k :=
      aux a vm ltac:(fun res =>
        match res with
        | (?u, ?vm) => let res := constr:((o u b, vm)) in k res
        end) in
    let aux_b o a b k :=
      aux b vm ltac:(fun res =>
        match res with
        | (?v, ?vm) =>
          aux a vm ltac:(fun res =>
            match res with
            | (?u, ?vm) => let res := constr:((o u v, vm)) in k res
            end)
        end) in
    match t with
    | Rplus ?a ?b => aux_b PAdd a b k
    | Rminus ?a ?b => aux_b PSub a b k
    | Ropp ?a => aux_u POpp a k
    | Rmult ?a ?b => aux_b PMul a b k
 (* | Rsqr ?a => aux (Rmult a a) l *)
    | powerRZ ?a ?b =>
      match b with
      | Z.pos ?p => aux_u' PPowN a (N.pos p) k
      | _ => fail 200 "Only constant, positive exponents are allowed"
      end
    | pow ?a ?n => aux_u' PPown a n k
    | Rdiv ?a ?b => aux (Rmult a (Rinv b)) vm k (* Both are convertible *)
    | _ =>
      match get_real_cst t with
      | assert_false =>
        get_comp_poly get_poly get_poly_pure t vm ltac:(fun t vm k =>
          match list_add t vm with
          | (?n, ?vm) => let res := constr:((PVar n, vm)) in k res
          end) ltac:(fun res =>
          match res with
          | (?p, ?vm) => let res := constr:((p, vm)) in k res
          end)
      | ?c => let res := constr:((PConst c, vm)) in k res
      end
    end in
  aux t vm k.

(* (* Test cases *)
Ltac deb tac ::= tac.
Definition p2 x y := x * (1 - y) ^ 2 / 3.
Definition p1 x := 1 - p2 (1 + x) ((1 - x) * 1 / 2).

Axiom poly_correct : forall (x : p_abstr_poly) vm,
    (if x isn't PConst (PConstR0) then true else false) = true ->
    interp_p_abstr_poly vm x >= R0.

Lemma test_p2 x y : (2/3 * x ^ 2 + p2 x y >= 0)%Re.
match goal with
| [ |- (?r >= 0)%Re ] => get_poly r (@Datatypes.nil R) ltac:(fun p =>
                      match p with
                      | (?po, ?vm) => apply (@poly_correct po vm)
                      end)
end.
reflexivity.
Qed.
Set Printing All.
Print test_p2.

Lemma test_p1 x y : (2/3 * x ^ 2 + p1 x * y >= 0)%Re.
match goal with
| [ |- (?r >= 0)%Re ] => get_poly r (@Datatypes.nil R) ltac:(fun p =>
                      match p with
                      | (?po, ?vm) => apply (@poly_correct po vm)
                      end)
end.
reflexivity.
Qed.
Print test_p1.
 *)

Inductive abstr_poly :=
  | Const of bigQ
  | Var of nat
  | Add of abstr_poly & abstr_poly
  | Sub of abstr_poly & abstr_poly
  | Mul of abstr_poly & abstr_poly
  | PowN of abstr_poly & binnat.N
  | Compose of abstr_poly & seq abstr_poly.

Section Defix'.
Variable (P : abstr_poly -> Prop).
Let P' := all_prop P.
Variable (f : forall t : bigQ, P (Const t)).
Variable (f0 : forall n : nat, P (Var n)).
Variable (f1 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Add a a0)).
Variable (f2 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Sub a a0)).
Variable (f3 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Mul a a0)).
Variable (f4 : forall a : abstr_poly, P a -> forall n : BinNums.N, P (PowN a n)).
Variable (f5 : forall a : abstr_poly, P a -> forall l : seq abstr_poly, P' l -> P (Compose a l)).

Fixpoint abstr_poly_ind' (p : abstr_poly) : P p :=
  let fix abstr_poly_ind2 (l : seq abstr_poly) : P' l :=
  match l as l0 return (P' l0) with
  | [::] => I
  | p :: l' => conj (abstr_poly_ind' p) (abstr_poly_ind2 l')
  end in
  match p as p0 return (P p0) with
  | Const t => f t
  | Var n => f0 n
  | Add a0 a1 => f1 (abstr_poly_ind' a0) (abstr_poly_ind' a1)
  | Sub a0 a1 => f2 (abstr_poly_ind' a0) (abstr_poly_ind' a1)
  | Mul a0 a1 => f3 (abstr_poly_ind' a0) (abstr_poly_ind' a1)
  | PowN a0 n => f4 (abstr_poly_ind' a0) n
  | Compose a0 l => f5 (abstr_poly_ind' a0) (abstr_poly_ind2 l)
  end.
End Defix'.

Fixpoint all_type (T : Type) (a : T -> Type) (s : seq T) : Type :=
  match s with
  | [::] => True
  | x :: s' => a x * all_type a s'
  end.

Lemma all_type_nth T (P : T -> Type) (s : seq T) (x0 : T):
  all_type P s -> forall i, (i < size s)%N -> P (nth x0 s i).
Proof. by elim: s => [//|? ? /= Hi [? ?] [//|?] ?]; apply Hi. Qed.

Lemma nth_all_type T (P : T -> Type) (s : seq T) (x0 : T):
  (forall i, (i < size s)%N -> P (nth x0 s i)) -> all_type P s.
Proof.
elim: s => [//|h t Ht H]; split; [by apply (H O)|].
by apply Ht => i Hi; apply (H (S i)).
Qed.

Section Defix''.
Variable (P : abstr_poly -> Type).
Let P' := all_type P.
Variable (f : forall t : bigQ, P (Const t)).
Variable (f0 : forall n : nat, P (Var n)).
Variable (f1 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Add a a0)).
Variable (f2 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Sub a a0)).
Variable (f3 : forall a : abstr_poly, P a -> forall a0 : abstr_poly, P a0 -> P (Mul a a0)).
Variable (f4 : forall a : abstr_poly, P a -> forall n : BinNums.N, P (PowN a n)).
Variable (f5 : forall a : abstr_poly, P a -> forall l : seq abstr_poly, P' l -> P (Compose a l)).

Fixpoint abstr_poly_rect' (p : abstr_poly) : P p :=
  let fix abstr_poly_rect2 (l : seq abstr_poly) : P' l :=
  match l as l0 return (P' l0) with
  | [::] => I
  | p :: l' => (abstr_poly_rect' p, abstr_poly_rect2 l')
  end in
  match p as p0 return (P p0) with
  | Const t => f t
  | Var n => f0 n
  | Add a0 a1 => f1 (abstr_poly_rect' a0) (abstr_poly_rect' a1)
  | Sub a0 a1 => f2 (abstr_poly_rect' a0) (abstr_poly_rect' a1)
  | Mul a0 a1 => f3 (abstr_poly_rect' a0) (abstr_poly_rect' a1)
  | PowN a0 n => f4 (abstr_poly_rect' a0) n
  | Compose a0 l => f5 (abstr_poly_rect' a0) (abstr_poly_rect2 l)
  end.
End Defix''.

Fixpoint abstr_poly_of_p_abstr_poly (p : p_abstr_poly) : abstr_poly :=
  match p with
  | PConst c => Const (bigQ_of_p_real_cst c)
  | PVar n => Var n
  | POpp x => Sub (Const 0%bigQ) (abstr_poly_of_p_abstr_poly x)
  | PAdd x y => Add (abstr_poly_of_p_abstr_poly x) (abstr_poly_of_p_abstr_poly y)
  | PSub x y => Sub (abstr_poly_of_p_abstr_poly x) (abstr_poly_of_p_abstr_poly y)
  | PMul x y => Mul (abstr_poly_of_p_abstr_poly x) (abstr_poly_of_p_abstr_poly y)
  | PPowN x n => PowN (abstr_poly_of_p_abstr_poly x) n
  | PPown x n => PowN (abstr_poly_of_p_abstr_poly x) (N.of_nat n)
  | PCompose p qi => Compose (abstr_poly_of_p_abstr_poly p) (map abstr_poly_of_p_abstr_poly qi)
  end.

Fixpoint interp_abstr_poly (vm : seq R) (p : abstr_poly) {struct p} : R :=
  match p with
  | Const c => bigQ2R c
  | Add p q => Rplus (interp_abstr_poly vm p) (interp_abstr_poly vm q)
  | Sub p q => Rminus (interp_abstr_poly vm p) (interp_abstr_poly vm q)
  | Mul p q => Rmult (interp_abstr_poly vm p) (interp_abstr_poly vm q)
  | PowN p n => powerRZ (interp_abstr_poly vm p) (Z.of_N n)
  | Var i => seq.nth R0 vm i
  | Compose p qi => interp_abstr_poly (map (interp_abstr_poly vm) qi) p
  end.

Lemma abstr_poly_of_p_abstr_poly_correct (vm : seq R) (p : p_abstr_poly) :
  interp_abstr_poly vm (abstr_poly_of_p_abstr_poly p) =
  interp_p_abstr_poly vm p.
Proof.
elim/p_abstr_poly_ind': p vm => //.
{ move=> *; apply bigQ_of_p_real_cst_correct. }
{ move=> p IHp vm /=.
  by rewrite (IHp vm) /bigQ2R /Q2R Rsimpl /Rminus Rplus_0_l. }
{ by move=> p1 IHp1 p2 IHp2 vm; rewrite /= (IHp1 vm) (IHp2 vm). }
{ by move=> p1 IHp1 p2 IHp2 vm; rewrite /= (IHp1 vm) (IHp2 vm). }
{ by move=> p1 IHp1 p2 IHp2 vm; rewrite /= (IHp1 vm) (IHp2 vm). }
{ by move=> p IHp n vm; rewrite /= (IHp vm). }
{ by move=> p IHp n vm; rewrite /= pow_powerRZ nat_N_Z (IHp vm). }
move=> pp IHpp qqi IHqqi vm; rewrite /=.
rewrite IHpp; f_equal.
rewrite -map_comp.
rewrite (eq_map_all_prop (f2 := interp_p_abstr_poly vm)) //.
exact: (all_prop_forall (P := fun p vm =>
  interp_abstr_poly vm (abstr_poly_of_p_abstr_poly p) = interp_p_abstr_poly vm p)).
Qed.

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

Fixpoint interp_poly_ssr (n : nat) (ap : abstr_poly) {struct ap} : {mpoly rat[n]} :=
  match ap with
  | Const t => (bigQ2rat t)%:MP_[n]
  | Var i =>
    match n with
    | O => 0%:MP_[O]
    | S n' => 'X_(inord i)
    end
  | Add a0 a1 => (interp_poly_ssr n a0 + interp_poly_ssr n a1)%R
  | Sub a0 a1 => (interp_poly_ssr n a0 - interp_poly_ssr n a1)%R
  | Mul a0 a1 => (interp_poly_ssr n a0 * interp_poly_ssr n a1)%R
  | PowN a0 n' => mpoly_exp (interp_poly_ssr n a0) n'
  | Compose a0 qi =>
    let qi' := map (interp_poly_ssr n) qi in
    match sumb (size qi' == size qi) with
    | right prf => 0%:MP_[n]
    | left prf =>
      comp_mpoly (tcast (eqP prf) (in_tuple qi'))
                 (interp_poly_ssr (size qi) a0)
    end
  end.

Fixpoint interp_poly_eff n (ap : abstr_poly) : effmpoly bigQ :=
  match ap with
  | Const c => @mpolyC_eff bigQ n c
  | Var i => @mpvar_eff bigQ n 1%bigQ 1 (N.of_nat i)
  | Add p q => mpoly_add_eff (interp_poly_eff n p) (interp_poly_eff n q)
  | Sub p q => mpoly_sub_eff (interp_poly_eff n p) (interp_poly_eff n q)
  | Mul p q => mpoly_mul_eff (interp_poly_eff n p) (interp_poly_eff n q)
  | PowN p m => mpoly_exp_eff (n := n) (interp_poly_eff n p) m
  | Compose p qi =>
    let qi' := map (interp_poly_eff n) qi in
    comp_mpoly_eff (n := n) qi' (interp_poly_eff (size qi) p)
  end.

Fixpoint vars_ltn n (ap : abstr_poly) : bool :=
  match ap with
  | Const _ => true
  | Var i => (i < n)%N
  | Add p q | Sub p q | Mul p q => vars_ltn n p && vars_ltn n q
  | PowN p _ => vars_ltn n p
  | Compose p qi => all (vars_ltn n) qi && vars_ltn (size qi) p
  end.

Lemma vars_ltn_ge (n n' : nat) (ap : abstr_poly) :
  (n <= n')%N -> vars_ltn n ap -> vars_ltn n' ap.
Proof.
move=> Hn'; elim/abstr_poly_ind': ap.
{ by []. }
{ by move=> i /= Hi; move: Hn'; apply leq_trans. }
{ by move=> a0 Ha0 a1 Ha1 /= /andP [] Hn0 Hn1; rewrite Ha0 // Ha1. }
{ by move=> a0 Ha0 a1 Ha1 /= /andP [] Hn0 Hn1; rewrite Ha0 // Ha1. }
{ by move=> a0 Ha0 a1 Ha1 /= /andP [] Hn0 Hn1; rewrite Ha0 // Ha1. }
{ by []. }
move=> a Ha; case=> [//|h t] /= [] Hh Ht /andP [] /andP [] Hh' Ht' Ha'.
rewrite Hh //= Ha' andb_true_r.
apply/(all_nthP (Const 0)) => i Hi.
move: Ht => /all_prop_nthP; apply=> //.
by move: Ht' => /all_nthP; apply.
Qed.

Lemma interp_poly_ssr_correct (l : seq R) (n : nat) (ap : abstr_poly) :
  size l = n -> vars_ltn n ap ->
  let p := map_mpoly rat2R (interp_poly_ssr n ap) in
  interp_abstr_poly l ap = p.@[fun i : 'I_n => nth R0 l i].
Proof.
elim/abstr_poly_ind': ap l n => //.
{ by move=> ? ? ? _ _ /=; rewrite map_mpolyC mevalC bigQ2R_rat. }
{ move=> ? ? [|?] ? //= ?.
  by rewrite map_mpolyX mevalX; f_equal; rewrite inordK. }
{ move=> p Hp q Hq l n Hn /= /andP [] Hnp Hnq.
  by rewrite (Hp _ _ Hn Hnp) (Hq _ _ Hn Hnq) !rmorphD. }
{ move=> p Hp q Hq l n Hn /= /andP [] Hnp Hnq.
  by rewrite (Hp _ _ Hn Hnp) (Hq _ _ Hn Hnq) !rmorphB. }
{ move=> p Hp q Hq l n Hn /= /andP [] Hnp Hnq.
  by rewrite (Hp _ _ Hn Hnp) (Hq _ _ Hn Hnq) !rmorphM. }
{ move=> p Hp m l n Hn /= Hnp; rewrite (Hp _ _ Hn Hnp).
  rewrite -{1}[m]spec_NK /binnat.implem_N bin_of_natE nat_N_Z.
  by rewrite -Interval_missing.pow_powerRZ misc.pow_rexp !rmorphX. }
move=> p Hp qi Hqi l n Hn /= /andP [Hqi' Hp'].
case (sumb _) => [e|]; [|by rewrite size_map eqxx].
set qi' := map _ _.
rewrite (Hp qi' (size qi)); [|by rewrite /qi' /= size_map|by []].
rewrite (map_mpoly_comp (@ratr_inj _)) comp_mpoly_meval /=.
apply meval_eq => i.
rewrite tnth_map tcastE /tnth /= (set_nth_default 0%R (tnth_default _ _));
  [|by rewrite /= size_map; case i].
rewrite (nth_map (Const 0)) => //.
move: Hqi => /all_prop_nthP Hqi.
move: Hqi' => /all_nthP Hqi'.
rewrite (Hqi _ _ _ _ n) => //; [|by apply Hqi'].
by rewrite (nth_map (Const 0)).
Qed.

Lemma interp_poly_ssr_correct' vm p :
  let n := size vm in
  let p' := abstr_poly_of_p_abstr_poly p in
  let p'' := map_mpoly rat2R (interp_poly_ssr n p') in
  vars_ltn n p' ->
  interp_p_abstr_poly vm p = p''.@[fun i : 'I_n => nth R0 vm i].
Proof.
move=> *; rewrite -interp_poly_ssr_correct //.
by rewrite abstr_poly_of_p_abstr_poly_correct.
Qed.

(** ** Part 0: Definition of operational type classes *)

Class sempty_of setT := sempty : setT.
Class sadd_of T setT := sadd : T -> setT -> setT.
Class smem_of T setT := smem : T -> setT -> bool.

Class mul_monom_of monom := mul_monom_op : monom -> monom -> monom.

Class list_of_poly_of T monom polyT := list_of_poly_op :
  polyT -> seq (monom * T).

Class polyC_of T polyT := polyC_op : T -> polyT.

Class polyX_of monom polyT := polyX_op : monom -> polyT.

Class poly_sub_of polyT := poly_sub_op : polyT -> polyT -> polyT.

Class poly_mul_of polyT := poly_mul_op : polyT -> polyT -> polyT.

Notation map_mx2_of B :=
  (forall {T T'} {m n : nat}, map_mx_of T T' (B T m n) (B T' m n)) (only parsing).

(** ** Part 1: Generic programs *)

Section generic_soscheck.

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context {monom : Type} {polyT : Type}.
Context `{!mul_monom_of monom, !list_of_poly_of T monom polyT}.
Context `{!polyC_of T polyT, !polyX_of monom polyT, !poly_sub_of polyT}.

Context {set : Type}.
Context `{!sempty_of set, !sadd_of monom set, !smem_of monom set}.

Context `{!zero_of T, !opp_of T, !leq_of T}.
Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!fun_of_of monom ord (mx monom)}.
Context `{!fun_of_of polyT ord (mx polyT)}.
Context {I0n : forall n, I0_class ord n.+1}.
Context {succ0n : forall n, succ0_class ord n.+1}.
Context {natof0n : forall n, nat_of_class ord n.+1}.
Context `{!I0_class ord 1}.

Definition max_coeff (p : polyT) : T :=
  foldl (fun m mc => max m (max mc.2 (-mc.2)%C)) 0%C (list_of_poly_op p).

Context `{!trmx_of (mx polyT)}.
(* Multiplication of matrices of polynomials. *)
Context `{!hmul_of (mx polyT)}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Context `{!fun_of_of F ord (mx F), !row_of ord (mx F), !store_of F ord (mx F), !dotmulB0_of F ord (mx F)}.
Context `{!heq_of (mx F), !trmx_of (mx F)}.

Context `{!map_mx2_of mx}.

Section generic_soscheck_size.

Context {s : nat}.
Context `{!I0_class ord s, !succ0_class ord s, !nat_of_class ord s}.

Definition check_base (p : polyT) (z : mx monom s 1) : bool :=
  let sm :=
    iteri_ord s
      (fun i =>
         iteri_ord s
           (fun j => sadd (mul_monom_op (fun_of_op z i I0)
                                        (fun_of_op z j I0))))
      sempty in
  all (fun mc => smem mc.1 sm) (list_of_poly_op p).

(* Prove that p >= 0 by proving that Q - s \delta I is a positive
   definite matrix with \delta >= max_coeff(p - z^T Q z) *)
Definition soscheck (p : polyT) (z : mx monom s 1) (Q : mx F s s) : bool :=
  check_base p z &&
  let r :=
    let p' :=
      let zp := map_mx_op polyX_op z in
      let Q' := map_mx_op (polyC_op \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC in
      (* TODO: profiling pour voir si nécessaire d'améliorer la ligne
       * ci dessus (facteur 40 en Caml, mais peut être du même ordre de
       * grandeur que la décomposition de Cholesky
       * (effectivement, sur d'assez gros exemples, ça semble être le cas)) *)
      fun_of_op p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    max_coeff pmp' in
  posdef_check_itv (@float_infnan_spec.fieps fs) (@float_infnan_spec.fieta fs)
                   (@float_infnan_spec.finite fs) Q (T2F r).

End generic_soscheck_size.

Context `{!poly_mul_of polyT}.

Context {s : nat}.
Context `{!I0_class ord s, !succ0_class ord s, !nat_of_class ord s}.

Variant sz_witness :=
  | Wit : polyT -> forall s, mx monom s.+1 1 -> mx F s.+1 s.+1 -> sz_witness.

(* Prove that /\_i pi >= 0 -> p >= 0 by proving that
   - \forall i, pi >= 0 with zi, Qi as above
   - p - \sum_i si pi >= 0 with z and Q as above *)
Definition soscheck_hyps
    (pszQi : seq (polyT * sz_witness))
    (p : polyT) (z : mx monom s 1) (Q : mx F s s) : bool :=
  let p' :=
      foldl
        (fun p' (pszQ : polyT * sz_witness) =>
           match pszQ.2 with
             | Wit s _ _ _ => poly_sub_op p' (poly_mul_op s pszQ.1)
           end) p pszQi in
  soscheck p' z Q
  && all
       (fun pzQ : polyT * sz_witness =>
          match pzQ.2 with
            | Wit s _ z Q => soscheck s z Q
          end) pszQi.

Context `{!eq_of monom, !zero_of monom}.

Definition has_const (z : mx monom s 1) := (fun_of_op z I0 I0 == (0:monom))%C.

End generic_soscheck.

Module S := FSetAVL.Make MultinomOrd.

Section eff_soscheck.

(** *** General definitions for seqmx and effmpoly *)

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context `{!zero_of T, !one_of T, !opp_of T, !add_of T, !sub_of T, !mul_of T, !eq_of T}.

Let monom := seqmultinom.

Let polyT := effmpoly T.

Global Instance mul_monom_eff : mul_monom_of monom := mnm_add_seq.

Global Instance list_of_poly_eff : list_of_poly_of T monom polyT :=
  list_of_mpoly_eff (T:=T).

Global Instance polyC_eff : polyC_of T polyT := @mpolyC_eff _ n.

Global Instance polyX_eff : polyX_of monom polyT := mpolyX_eff.

Global Instance poly_sub_eff : poly_sub_of polyT := mpoly_sub_eff.

Let set := S.t.

Global Instance sempty_eff : sempty_of set := S.empty.

Global Instance sadd_eff : sadd_of monom set := S.add.

Global Instance smem_eff : smem_of monom set := S.mem.

Context `{!leq_of T}.

Let ord := ord_instN.

Let mx := @hseqmx.

Context {s : nat}.

Global Instance fun_of_seqmx_monom : fun_of_of monom ord (mx monom) :=
  @fun_of_seqmx _ [::].

Definition check_base_eff : polyT -> mx monom s.+1 1 -> bool :=
  check_base (I0_class0:=I0_instN).

Definition max_coeff_eff : polyT -> T := max_coeff.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Global Instance fun_of_seqmx_polyT : fun_of_of polyT ord (mx polyT) :=
  @fun_of_seqmx _ mp0_eff.

Global Instance mulseqmx_polyT : hmul_of (mx polyT) :=
  @mul_seqmx _ mp0_eff mpoly_add_eff mpoly_mul_eff.

Definition soscheck_eff : polyT -> mx monom s.+1 1 -> mx F s.+1 s.+1 -> bool :=
  soscheck (F2T:=F2T) (T2F:=T2F).

Global Instance poly_mul_eff : poly_mul_of polyT := mpoly_mul_eff.

Definition soscheck_hyps_eff :
  seq (polyT * sz_witness) ->
  polyT -> mx monom s.+1 1 -> mx F s.+1 s.+1 -> bool :=
  soscheck_hyps (set:=set) (F2T:=F2T) (T2F:=T2F)
                (I0n:=fun n => O) (succ0n:=fun n => S) (natof0n:=fun _ => id).

Global Instance monom_eq_eff : eq_of monom := mnmc_eq_seq.

Definition has_const_eff {n : nat} : mx monom s.+1 1 -> bool :=
  has_const (zero_of1 := @mnm0_seq n).

End eff_soscheck.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_soscheck.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

Context {n : nat} {T : comRingType}.

Let monom := 'X_{1..n}.

Let polyT := mpoly n T.

Global Instance mul_monom_ssr : mul_monom_of monom := mnm_add.

Global Instance list_of_poly_ssr : list_of_poly_of T monom polyT :=
  list_of_mpoly.

Global Instance polyC_ssr : polyC_of T polyT := fun c => mpolyC n c.

Global Instance polyX_ssr : polyX_of monom polyT := fun m => mpolyX T m.

Global Instance poly_sub_ssr : poly_sub_of polyT := fun p q => (p - q)%R.

Let set := seq monom.

Global Instance sempty_ssr : sempty_of set := [::].

Global Instance sadd_ssr : sadd_of monom set := fun e s => e :: s.

Global Instance smem_ssr : smem_of monom set := fun e s => e \in s.

Local Instance zero_ssr : zero_of T := 0%R.
Local Instance opp_ssr : opp_of T := fun x => (-x)%R.

Context `{!leq_of T}.

Let ord := ordinal.

Let mx := matrix.

Definition max_coeff_ssr : polyT -> T := max_coeff.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2T : F -> T}.  (* exact conversion for finite values *)
Context {T2F : T -> F}.  (* overapproximation *)

Global Instance trmx_instPolyT_ssr : trmx_of (mx polyT) :=
  @matrix.trmx polyT.

Global Instance hmul_mxPolyT_ssr : hmul_of (mx polyT) := @mulmx _.

Global Instance map_mx_ssr : map_mx2_of mx := fun T T' m n f => @map_mx T T' f m n.

Definition check_base_ssr (s : nat) :
  polyT -> 'cV[monom]_s.+1 -> bool := check_base.

Definition soscheck_ssr (s : nat) :
  polyT -> 'cV[monom]_s.+1 -> 'M[F]_s.+1 -> bool :=
  soscheck (F2T:=F2T) (T2F:=T2F).

Global Instance poly_mul_ssr : poly_mul_of polyT := fun p q => (p * q)%R.

Definition soscheck_hyps_ssr (s : nat) :
  seq (polyT * sz_witness) ->
  polyT -> 'cV[monom]_s.+1 -> 'M[F]_s.+1 -> bool :=
  soscheck_hyps (F2T:=F2T) (T2F:=T2F).

Global Instance monom_eq_ssr : eq_of monom := eqtype.eq_op.
Global Instance monom0_ssr : zero_of monom := mnm0.

Definition has_const_ssr (s : nat) : 'cV[monom]_s.+1 -> bool := has_const.

(** *** Proofs *)

Variable (T2R : T -> R).
Hypothesis T2R_additive : additive T2R.
Canonical T2R_additive_struct := Additive T2R_additive.
Hypothesis T2F_correct : forall x, finite (T2F x) -> T2R x <= FIS2FS (T2F x).
Hypothesis T2R_F2T : forall x, T2R (F2T x) = FIS2FS x.
(** NOTE: we would like to use [Num.max x y] here, but it is not possible as is
given there is no canonical structure that merges comRingType & numDomainType *)
Hypothesis max_l : forall x y : T, T2R x <= T2R (max x y).
Hypothesis max_r : forall x y, T2R y <= T2R (max x y).

Lemma max_coeff_pos (p : polyT) : 0 <= T2R (max_coeff p).
Proof.
rewrite /max_coeff; set f := fun _ => _; set l := _ p; clearbody l.
suff : forall x, 0 <= T2R x -> 0 <= T2R (foldl f x l).
{ by apply; rewrite GRing.raddf0; right. }
elim l => [//|h t IH x Hx /=]; apply IH; rewrite /f.
apply (Rle_trans _ _ _ Hx), max_l.
Qed.

Lemma max_coeff_correct (p : polyT) (m : monom) :
  Rabs (T2R p@_m) <= T2R (max_coeff p).
Proof.
case_eq (m \in msupp p);
  [|rewrite mcoeff_msupp; move/eqP->; rewrite GRing.raddf0 Rabs_R0;
    by apply max_coeff_pos].
rewrite /max_coeff /list_of_poly_of /list_of_poly_ssr /list_of_mpoly.
have Hmax : forall x y, Rabs (T2R x) <= T2R (max y (max x (- x)%C)).
{ move=> x y; apply Rabs_le; split.
  { rewrite -(Ropp_involutive (T2R x)); apply Ropp_le_contravar.
    change (- (T2R x))%Re with (- (T2R x))%Ri.
    rewrite -GRing.raddfN /=.
    apply (Rle_trans _ _ _ (max_r _ _) (max_r _ _)). }
  apply (Rle_trans _ _ _ (max_l _ _) (max_r _ _)). }
rewrite -(path.mem_sort mnmc_le) /list_of_poly_op.
elim: (path.sort _) 0%C=> [//|h t IH] z; move/orP; elim.
{ move/eqP-> => /=; set f := fun _ => _; set l := map _ _.
  move: (Hmax p@_h z); set z' := max z _; generalize z'.
  elim l => /= [//|h' l' IH' z'' Hz'']; apply IH'.
  apply (Rle_trans _ _ _ Hz''), max_l. }
by move=> Ht; apply IH.
Qed.

Lemma check_base_correct s (p : polyT) (z : 'cV_s.+1) : check_base p z ->
  forall m, m \in msupp p -> exists i j, (z i ord0 + z j ord0 == m)%MM.
Proof.
rewrite /check_base /list_of_poly_of /list_of_poly_ssr /sadd /sadd_ssr.
rewrite /smem /smem_ssr /sempty /sempty_ssr; set sm := iteri_ord _ _ _.
move/allP=> Hmem m Hsupp.
have : m \in sm.
{ apply (Hmem (m, p@_m)).
  by rewrite -/((fun m => (m, p@_m)) m); apply map_f; rewrite path.mem_sort. }
pose P := fun (_ : nat) (sm : set) =>
            m \in sm -> exists i j, (z i ord0 + z j ord0)%MM == m.
rewrite {Hmem} -/(P 0%N sm) {}/sm; apply iteri_ord_ind => // i s0.
rewrite {}/P /nat_of /nat_of_ssr => Hi Hs0; set sm := iteri_ord _ _ _.
pose P := fun (_ : nat) (sm : set) =>
            m \in sm -> exists i j, (z i ord0 + z j ord0)%MM == m.
rewrite -/(P 0%N sm) {}/sm; apply iteri_ord_ind => // j s1.
rewrite {}/P /nat_of /nat_of_ssr in_cons => Hj Hs1.
by move/orP; elim; [move/eqP->; exists i, j|].
Qed.

Require Import bigop_tactics.

Lemma soscheck_correct s p z Q : @soscheck_ssr s p z Q ->
  forall x, 0%R <= (map_mpoly T2R p).@[x]
            /\ (has_const_ssr z -> 0%R < (map_mpoly T2R p).@[x]).
Proof.
rewrite /has_const_ssr /has_const /eq_op /monom_eq_ssr /zero_op /monom0_ssr.
rewrite /soscheck_ssr /soscheck /fun_of_op /fun_of_ssr /map_mx_ssr /map_mx_op.
set zp := matrix.map_mx _ z.
set Q' := matrix.map_mx _ _.
set p' := _ (_ *m _) _ _.
set pmp' := poly_sub_op _ _.
set r := max_coeff _.
pose zpr := matrix.map_mx [eta mpolyX real_ringType] z.
pose Q'r := matrix.map_mx (map_mpoly T2R) Q'.
pose mpolyC_R := fun c : R => mpolyC n c.
pose map_mpolyC_R := fun m : 'M_s.+1 => matrix.map_mx mpolyC_R m.
move/andP=> [Hbase Hpcheck].
have : exists E : 'M_s.+1,
  Mabs E <=m: matrix.const_mx (T2R r)
  /\ map_mpoly T2R p = (zpr^T *m (Q'r + map_mpolyC_R E) *m zpr) ord0 ord0.
{ pose zij := fun i j => (z i ord0 + z j ord0)%MM.
  pose I_sp1_2 := prod_finType (ordinal_finType s.+1) (ordinal_finType s.+1).
  pose nbij := fun i j => size [seq ij <- index_enum I_sp1_2 |
                                zij ij.2 ij.1 == zij i j].
  pose E := (\matrix_(i, j) (T2R pmp'@_(zij i j) / INR (nbij i j))%Re).
  exists E.
  have Pnbij : forall i j, (0 < nbij i j)%N.
  { move=> i j; rewrite /nbij filter_index_enum; rewrite <-cardE.
    by apply/card_gt0P; exists (j, i); rewrite /in_mem /=. }
  have Pr := max_coeff_pos _ : 0%R <= T2R r.
  split.
  { move=> i j; rewrite !mxE Rabs_mult.
    have NZnbij : INR (nbij i j) <> 0%Re.
    { by change 0%Re with (INR 0); move/INR_eq; move: (Pnbij i j); case nbij. }
    rewrite Rabs_Rinv // (Rabs_pos_eq _ (pos_INR _)).
    apply (Rmult_le_reg_r (INR (nbij i j))).
    { apply Rnot_ge_lt=> H; apply NZnbij.
      by apply Rle_antisym; [apply Rge_le|apply pos_INR]. }
    rewrite Rmult_assoc Rinv_l // Rmult_1_r.
    have nbij_ge_1 : 1 <= INR (nbij i j).
    { move: NZnbij; case nbij=>// nb _; rewrite S_INR -{1}(Rplus_0_l 1).
      apply Rplus_le_compat_r, pos_INR. }
    apply (Rle_trans _ (T2R r)); [by apply max_coeff_correct|].
    rewrite -{1}(Rmult_1_r (T2R r)); apply Rmult_le_compat_l=>//. }
  apply/mpolyP => m; rewrite mcoeff_map_mpoly /= mxE.
  set M := (Q'r + _)%R.
  under big ? _ rewrite mxE big_distrl /=; under big ? _ rewrite mxE.
  rewrite pair_bigA /= (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  have -> : M = map_mpolyC_R (matrix.map_mx (T2R \o F2T) Q + E)%R.
  { apply/matrixP=> i j; rewrite /map_mpolyC_R /mpolyC_R.
    by rewrite !mxE mpolyCD map_mpolyC. }
  move {M}; set M := map_mpolyC_R _.
  under big ? _ rewrite (GRing.mulrC (zpr _ _)) -GRing.mulrA mxE mcoeffCM.
  under big ? _ rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX.
  rewrite (bigID (fun ij => zij ij.2 ij.1 == m)) /= GRing.addrC.
  rewrite big1 ?GRing.add0r; last first.
  { by move=> ij; move/negbTE=> ->; rewrite GRing.mul0r. }
  under big ? Hi rewrite Hi GRing.mul1r 2!mxE.
  rewrite big_split /= GRing.addrC.
  pose nbm := size [seq ij <- index_enum I_sp1_2 | zij ij.2 ij.1 == m].
  under big ? Hi
    (move/eqP in Hi; rewrite mxE /nbij Hi -/nbm mcoeffB GRing.raddfB /=).
  rewrite misc.big_sum_pred_const -/nbm /Rdiv !unfoldR.
  rewrite mulrDl mulrDr -addrA.
  rewrite -{1}(GRing.addr0 (T2R _)); f_equal.
  { rewrite GRing.mulrC -GRing.mulrA; case_eq (m \in msupp p).
    { move=> Hm; move: (check_base_correct Hbase Hm).
      move=> [i [j {Hm}Hm]]; rewrite /GRing.mul /=; field.
      apply Rgt_not_eq, Rlt_gt.
      rewrite -unfoldR; change 0%Re with (INR 0); apply lt_INR.
      rewrite /nbm filter_index_enum; rewrite <-cardE.
      by apply/ltP/card_gt0P; exists (j, i); rewrite /in_mem /=. }
    by rewrite mcoeff_msupp; move/eqP->; rewrite GRing.raddf0 GRing.mul0r. }
  rewrite /p' mxE.
  under big ? _ (rewrite mxE big_distrl /=; under big ? _ rewrite mxE).
  rewrite pair_bigA /= (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  under big ? _ rewrite (GRing.mulrC (zp _ _)) -GRing.mulrA mxE mcoeffCM.
  under big ? _ rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX.
  rewrite GRing.raddf_sum /= (bigID (fun ij => zij ij.2 ij.1 == m)) /=.
  under big ? Hi rewrite Hi GRing.mul1r.
  set b := bigop _ _ _; rewrite big1; last first; [|rewrite {}/b GRing.addr0].
  { by move=> ij; move/negbTE => ->; rewrite GRing.mul0r GRing.raddf0. }
  rewrite -big_filter /nbm /I_sp1_2; case [seq i <- _ | _].
  { by rewrite big_nil GRing.addr0 GRing.oppr0 GRing.mul0r. }
  move=> h t; rewrite GRing.mulrC -GRing.mulrA /GRing.mul /= Rinv_l.
  { by rewrite Rmult_1_r GRing.addNr. }
  case size; [exact R1_neq_R0|].
  move=> n'; apply Rgt_not_eq, Rlt_gt.
  by apply/RltP; rewrite unfoldR ltr0Sn. }
move=> [E [HE ->]] x.
set M := _ *m _.
replace (meval _ _)
with ((matrix.map_mx (meval x) M) ord0 ord0); [|by rewrite mxE].
replace 0%R with ((@matrix.const_mx _ 1 1 R0) ord0 ord0); [|by rewrite mxE].
rewrite /M !map_mxM -map_trmx map_mxD.
replace (matrix.map_mx _ (map_mpolyC_R E)) with E;
  [|by apply/matrixP => i j; rewrite !mxE /= mevalC].
replace (matrix.map_mx _ _) with (matrix.map_mx (T2R \o F2T) Q);
  [|by apply/matrixP => i j;
    rewrite !mxE /= map_mpolyC mevalC].
have Hposdef : posdef (map_mx (T2R \o F2T) Q + E).
{ apply (posdef_check_itv_correct Hpcheck).
  apply Mle_trans with (Mabs E).
  { right; rewrite !mxE /=; f_equal.
    by rewrite T2R_F2T GRing.addrC GRing.addKr. }
  apply (Mle_trans HE) => i j; rewrite !mxE.
  by apply T2F_correct; move: Hpcheck; move/andP; elim. }
split; [by apply /Mle_scalar /posdef_semipos|].
move=> /eqP z0; apply /Mlt_scalar /Hposdef.
move/matrixP => H; move: {H}(H ord0 ord0).
rewrite /GRing.zero /= /const_mx /map_mx !mxE.
by rewrite z0 mpolyX0 meval1 => /eqP; rewrite GRing.oner_eq0.
Qed.

Hypothesis T2R_multiplicative : multiplicative T2R.
Canonical T2R_morphism_struct := AddRMorphism T2R_multiplicative.

Lemma soscheck_hyps_correct s p pzQi z Q :
  @soscheck_hyps_ssr s pzQi p z Q ->
  forall x,
    all_prop (fun pzQ => 0%R <= (map_mpoly T2R pzQ.1).@[x]) pzQi ->
    (0%R <= (map_mpoly T2R p).@[x]
     /\ (has_const_ssr z -> 0%R < (map_mpoly T2R p).@[x])).
Proof.
move: p z Q.
elim: pzQi => [|pzQ0 pzQi Hind] p z Q;
  rewrite /soscheck_hyps_ssr /soscheck_hyps /=.
{ rewrite andbC /=  => H x _; apply (soscheck_correct H). }
case pzQ0 => p0 zQ0.
case zQ0 => s0 sz0 z0 Q0 /=.
set p' := poly_sub_op p (poly_mul_op s0 p0).
move=> /and3P [] Hsoscheck Hsoscheck0 Hall x [] Hp0 Hall_prop.
have : 0 <= (map_mpoly T2R p').@[x]
       /\ (has_const_ssr z -> 0 < (map_mpoly T2R p').@[x]).
{ by apply (Hind p' z Q); [by apply /andP; split|]. }
rewrite !rmorphB !rmorphM /=.
move=> [] H1 H2; split=> [|H3]; [move: H1|move: (H2 H3)].
{ rewrite /GRing.add /GRing.opp -Rcomplements.Rminus_le_0.
  by apply Rle_trans, Rmult_le_pos; [apply (soscheck_correct Hsoscheck0)|]. }
rewrite /GRing.add /GRing.opp -Rcomplements.Rminus_lt_0.
by apply Rle_lt_trans, Rmult_le_pos; [apply (soscheck_correct Hsoscheck0)|].
Qed.

End theory_soscheck.

(* Future definition of F2C *)
Definition bigZZ2Q (m : bigZ) (e : bigZ) :=
  match m,e with
  | BigZ.Pos n, BigZ.Pos p => BigQ.Qz (BigZ.Pos (BigN.shiftl n p))
  | BigZ.Neg n, BigZ.Pos p => BigQ.Qz (BigZ.Neg (BigN.shiftl n p))
  | _, BigZ.Neg p =>
  (*
  BigQ.mul (BigQ.Qz m) (BigQ.inv (BigQ.Qz (BigZ.Pos (BigN.shiftl p 1%bigN))))
  *)
  BigQ.Qq m (BigN.shiftl 1%bigN p)
  end.

Lemma bigZZ2Q_correct m e :
  Q2R [bigZZ2Q m e]%bigQ = Z2R [m]%bigZ * bpow radix2 [e]%bigZ.
Proof.
case: m => m; case: e => e.
{ rewrite /= BigN.spec_shiftl_pow2 /Q2R Z2R_mult Rcomplements.Rdiv_1.
  rewrite (Z2R_Zpower radix2) //.
  exact: BigN.spec_pos. }
{ rewrite /= ifF /Q2R /=; last exact/BigN.eqb_neq/BigN.shiftl_eq_0_iff.
  rewrite BigN.spec_shiftl_pow2 /=.
  rewrite bpow_opp -Z2R_Zpower; last exact: BigN.spec_pos.
  move: (Zpower_gt_0 radix2 [e]%bigN (BigN.spec_pos _)); simpl.
  by case: Zpower =>// p Hp. }
{ rewrite /= BigN.spec_shiftl_pow2 /= -Z2R_Zpower; last exact: BigN.spec_pos.
  by rewrite /Q2R /= Zopp_mult_distr_l Z2R_mult Rcomplements.Rdiv_1. }
{ rewrite /= ifF /Q2R /=; last exact/BigN.eqb_neq/BigN.shiftl_eq_0_iff.
  rewrite BigN.spec_shiftl_pow2 /=.
  rewrite bpow_opp -Z2R_Zpower; last exact: BigN.spec_pos.
  move: (Zpower_gt_0 radix2 [e]%bigN (BigN.spec_pos _)); simpl.
  by case: Zpower =>// p Hp. }
Qed.

Definition F2bigQ (q : coqinterval_infnan.F.type) : bigQ :=
  match q with
  | Interval_specific_ops.Float m e => bigZZ2Q m e
  | Interval_specific_ops.Fnan => 0%bigQ
  end.

(* TODO LATER:
   Generalize the formalization w.r.t
   [Variable fs : Float_round_up_infnan_spec.]
   Remark:
   - fs == coqinterval_round_up_infnan
   - fris fs == coqinterval_infnan
*)

Local Notation fs := coqinterval_infnan.coqinterval_round_up_infnan (only parsing).

Delimit Scope Z_scope with coq_Z.  (* should be unnecessary *)

(* pris ici rat2bigQ *)

Definition bigQ2F' := snd \o bigQ2F.
Definition bigQ2FIS := FI2FIS \o F2FI \o bigQ2F'.
Definition rat2FIS := bigQ2FIS \o rat2bigQ.

Definition FIS2bigQ : FIS coqinterval_infnan -> bigQ := F2bigQ \o FI_val.
Definition FIS2rat : FIS coqinterval_infnan -> rat := bigQ2rat \o FIS2bigQ.

(* Erik: [toR] could be proved extensionnaly equal to [F_val \o FI2F]. *)

Lemma F2FI_valE f :
  mantissa_bounded f ->
  F.toX (F2FI_val f) = F.toX f.
Proof.
case: f => [//|m e].
by move/signif_digits_correct; rewrite /F2FI_val =>->.
Qed.

Lemma BigZ_Pos_NofZ n : [BigZ.Pos (BigN.N_of_Z n)]%bigZ = if (0 <=? n)%coq_Z then n else Z0.
Proof. by rewrite -[RHS](BigZ.spec_of_Z); case: n. Qed.

Lemma rat2FIS_correct r :
  @finite fs (rat2FIS r) ->
  rat2R r <= FS_val (@FIS2FS fs (rat2FIS r)).
Proof.
Opaque F.div.
move => Hr; have := real_FtoX_toR Hr.
rewrite F2FI_correct //=.
rewrite /rat2bigQ /ratr.
set n := numq r; set d := denq r.
rewrite /bigQ2F' /=.
rewrite F2FI_valE; last first.
{ apply/mantissa_boundedP; rewrite /bigQ2F.
  set r' := BigQ.red _; case r'=>[t|t t0]; apply/fidiv_proof. }
move=>->/=; rewrite /bigQ2F.
have Hd: (0 < int2Z d)%coq_Z.
{ by move: (denq_gt0 r); rewrite -/d -int2Z_lt /= /is_true Z.ltb_lt. }
have Hd' := Z.lt_le_incl _ _ Hd.
set nr := BigQ.red _.
move: (Qeq_refl [nr]%bigQ).
rewrite {2}BigQ.strong_spec_red Qred_correct /Qeq /=.
rewrite ifF /=; last first.
{ rewrite BigN.spec_eqb !BigN.spec_N_of_Z //=; apply/negP.
  by rewrite /is_true Z.eqb_eq=> H; move: Hd; rewrite H. }
rewrite BigN.spec_N_of_Z // Z2Pos.id // BigZ.spec_of_Z.
case E: nr.
{ move=> /= Hnr; rewrite F.div_correct /Xround real_FtoX_toR //=.
  rewrite /Xdiv' ifF; [|by apply Req_bool_false, R1_neq_R0].
  rewrite /Rdiv Rinv_1 Rmult_1_r /round /rnd_of_mode /=.
  set x := proj_val _; apply (Rle_trans _ x); last first.
  { by apply round_UP_pt, FLX_exp_valid. }
  rewrite /x -!Z2R_int2Z real_FtoX_toR // toR_Float /= Rmult_1_r.
  apply (Rmult_le_reg_r (Z2R (int2Z d))).
  { by rewrite -[0%Re]/(Z2R 0); apply Z2R_lt. }
  rewrite -Z2R_mult Hnr Z.mul_1_r /GRing.mul /= Rmult_assoc.
  rewrite Rstruct.mulVr ?Rmult_1_r; [by right|].
  rewrite -[0%Re]/(Z2R 0); apply/negP=>/eqP; apply Z2R_neq=>H.
  by move: Hd; rewrite H. }
rewrite /= ifF /=; last first.
{ move: E; rewrite /nr; set nrnr := (_ # _)%bigQ; move: (BigQ_red_den_neq0 nrnr).
  by case (BigQ.red _)=>[//|n' d'] H [] _ <-; move: H=>/negbTE. }
rewrite F.div_correct /Xround /Xdiv real_FtoX_toR //= real_FtoX_toR //=.
rewrite /Xdiv' ifF; last first.
{ apply Req_bool_false; rewrite real_FtoX_toR // toR_Float /= Rmult_1_r.
  rewrite -[0%Re]/(Z2R 0); apply Z2R_neq.
  move: E; rewrite /nr; set nrnr := (_ # _)%bigQ.
  move: (BigQ_red_den_neq0_aux nrnr).
  by case (BigQ.red _)=>[//|n' d'] H [] _ <-. }
rewrite Z2Pos.id; last first.
{ move: E; rewrite /nr; set nrnr := (_ # _)%bigQ.
  move: (BigQ_red_den_neq0_aux nrnr); case (BigQ.red _)=>[//|? d'] H [] _ <-.
  by case (Z_le_lt_eq_dec _ _ (BigN.spec_pos d'))=>// H'; exfalso; apply H. }
move=> Hnd; rewrite /round /rnd_of_mode /=.
set x := _ / _; apply (Rle_trans _ x); [|by apply round_UP_pt, FLX_exp_valid].
rewrite /x -!Z2R_int2Z; do 2 rewrite real_FtoX_toR // toR_Float /= Rmult_1_r.
apply (Rmult_le_reg_r (Z2R (int2Z d))).
{ by rewrite -[0%Re]/(Z2R 0); apply Z2R_lt. }
set lhs := _ * _; rewrite Rmult_assoc (Rmult_comm (/ _)) -Rmult_assoc -Z2R_mult.
rewrite Hnd {}/lhs /GRing.mul /= Rmult_assoc.
rewrite Rstruct.mulVr ?Rmult_1_r; [right|]; last first.
{ rewrite -[0%Re]/(Z2R 0); apply/negP=>/eqP; apply Z2R_neq=>H.
  by move: Hd; rewrite H. }
rewrite Z2R_mult Rmult_assoc Rinv_r ?Rmult_1_r //.
move: (erefl nr); rewrite /nr; set nrnr := (_ # _)%bigQ=>_.
move: (BigQ_red_den_neq0_aux nrnr); rewrite /nrnr -/nr E=>H.
by rewrite -[0%Re]/(Z2R 0); apply Z2R_neq.
Transparent F.div.
Qed.

Lemma rat2R_FIS2rat :
 forall x0 : FIS fs, rat2R (FIS2rat x0) = FS_val (FI2FS x0).
Proof.
move=> x; rewrite -bigQ2R_rat /bigQ2R.
case: x => -[|m e] H /=.
{ move/mantissa_boundedP in H.
  case: H => H.
  by rewrite Q2R_0.
  by case: H => r H1 H2 /=; rewrite /F.toX /= in H1 *. }
rewrite /FIS2bigQ /=.
move/mantissa_boundedP in H.
case: H => H /=; first by rewrite real_FtoX_toR in H.
case: H => r H1 H2 /=.
by rewrite bigZZ2Q_correct toR_Float.
Qed.

Definition eqF (a b : F.type) := F.toX a = F.toX b.
Definition eqFI (a b : FI) := F.toX a = F.toX b.
Definition eqFIS (a b : FIS coqinterval_round_up_infnan) := F.toX a = F.toX b.

Instance FIS_rat_bigQ : refines (eqFIS ==> r_ratBigQ) FIS2rat FIS2bigQ.
Proof.
ref_abstr => a1 a2 ref_a.
rewrite refinesE /r_ratBigQ /FIS2rat /FIS2bigQ /=.
rewrite refinesE /eqFIS in ref_a.
rewrite /F2bigQ.
case: a1 ref_a => [a Ha]; case: a2 => [b Hb] /= ref_a.
case: a Ha ref_a => [|m e] Ha ref_a;
case: b Hb ref_a => [|m' e'] Hb ref_b =>//.
by symmetry in ref_b; rewrite real_FtoX_toR in ref_b.
by rewrite real_FtoX_toR in ref_b.
move/(congr1 proj_val) in ref_b.
rewrite !toR_Float in ref_b.
rewrite /fun_hrel /bigQ2rat.
apply: val_inj =>/=.
suff->: Qred [bigZZ2Q m' e']%bigQ = Qred [bigZZ2Q m e]%bigQ by [].
apply: Qred_complete; apply: Qeq_Q2R.
by rewrite !bigZZ2Q_correct.
Qed.

Definition id1 {T} (x : T) := x.

Definition r_QbigQ := fun_hrel BigQ.to_Q.

Instance bigQ2ratK : refines (eq ==>  BigQ.eq) (rat2bigQ \o bigQ2rat) id.
Proof.
rewrite refinesE => x x' ref_x.
apply/BigQ.eqb_eq.
rewrite BigQ.spec_eq_bool.
apply/Qeq_bool_iff.
set p := Qden (Qred [x]%bigQ).
have Pp := nat_of_pos_gt0 p.
rewrite /= -(prednK Pp) (prednK Pp) -!binnat.to_natE Pos2Nat.id ifF; last first.
{ by rewrite BigN.spec_eqb BigN.spec_0 BigN.spec_N_of_Z. }
rewrite BigZ.spec_of_Z BigN.BigN.spec_N_of_Z //= /p.
rewrite /numq /= Z2intK.
set qx := _ # _.
suff->: qx = [BigQ.red x']%bigQ by apply: BigQ.spec_red.
rewrite /qx -ref_x BigQ.strong_spec_red.
set x0 := Qred [x]%bigQ.
by case: x0.
Qed.

Lemma FI_val_inj : injective FI_val.
Proof.
move=> x y Hxy.
case: x Hxy => [vx px] Hxy.
case: y Hxy => [vy py] Hxy.
simpl in Hxy.
move: py; rewrite -Hxy => py; f_equal; clear Hxy vy.
exact: bool_irrelevance.
Qed.

Lemma eqF_signif_digits m e m' e' :
  eqF (Float m e) (Float m' e') ->
  (signif_digits m <=? 53)%bigZ = (signif_digits m' <=? 53)%bigZ.
Proof.
move=> HeqF.
apply/idP/idP.
{ move/signif_digits_correct => H.
  rewrite /eqF in HeqF.
  move/(congr1 proj_val) in HeqF.
  rewrite !toR_Float in HeqF.
  apply/(signif_digits_correct _ e').
  rewrite /mantissa_bounded /x_bounded in H *; right.
  have {H} [|[r H1 H2]] := H e; first by rewrite real_FtoX_toR.
  exists r =>//.
  rewrite real_FtoX_toR // toR_Float; congr Xreal.
  move/(congr1 proj_val) in H1.
  rewrite !toR_Float /= in H1.
  by rewrite -{}H1 {}HeqF. }
{ move/signif_digits_correct => H.
  rewrite /eqF in HeqF.
  move/(congr1 proj_val) in HeqF.
  rewrite !toR_Float in HeqF.
  apply/(signif_digits_correct _ e).
  rewrite /mantissa_bounded /x_bounded in H *; right.
  have {H} [|[r H1 H2]] := H e'; first by rewrite real_FtoX_toR.
  exists r =>//.
  rewrite real_FtoX_toR // toR_Float; congr Xreal.
  move/(congr1 proj_val) in H1.
  rewrite !toR_Float /= in H1.
  by rewrite -{}H1 -{}HeqF. }
Qed.

Instance : refines (eqF ==> eqFI) F2FI F2FI.
rewrite refinesE => f f' ref_f.
rewrite /F2FI /eqFI /=.
rewrite /eqF in ref_f.
case: f ref_f => [|m e] ref_f; case: f' ref_f => [|m' e'] ref_f //.
by symmetry in ref_f; rewrite real_FtoX_toR in ref_f.
by rewrite real_FtoX_toR in ref_f.
rewrite /= (eqF_signif_digits ref_f).
by case: ifP.
Qed.

Instance : refines (BigQ.eq ==> eqF) bigQ2F' bigQ2F'.
Proof.
Opaque F.div.
rewrite refinesE => a b /BigQ.eqb_eq; rewrite BigQ.spec_eq_bool.
rewrite /bigQ2F' /bigQ2F /= => rab.
pose m := fun x => match BigQ.red x with
                    | BigQ.Qz m => (m, 1%bigN)
                    | (m # n)%bigQ => (m, n)
                  end.
rewrite -/(m a) -/(m b).
pose f := fun (mn : bigZ * bigN) => let (m, n) := mn in ([m]%bigZ, [n]%bigN).
suff H : f (m a) = f (m b).
{ move: H; rewrite /f; case (m a), (m b); case=> H1 H2.
  rewrite /eqF !F.div_correct.
  do 4 rewrite real_FtoX_toR ?toR_Float=>//.
  by rewrite H1 /= H2. }
rewrite /f /m.
have Hred: Qred [a]%bigQ = Qred [b]%bigQ.
{ by apply Qred_complete, Qeq_bool_iff. }
have H: [BigQ.red a]%bigQ = [BigQ.red b]%bigQ.
{ by rewrite !BigQ.strong_spec_red. }
case Ea: (BigQ.red a); case Eb: (BigQ.red b).
{ by move: H; rewrite Ea Eb /=; case=>->. }
{ move: H; rewrite Ea Eb /=.
  case E: (_ =? _)%bigN.
  { by move: (BigQ_red_den_neq0 b); rewrite Eb E. }
  case=> ->; rewrite -Z2Pos.inj_1 Z2Pos.inj_iff; [by move<-|done|].
  by apply BigQ.N_to_Z_pos; rewrite -Z.eqb_neq -BigN.spec_eqb. }
{ move: H; rewrite Ea Eb /=.
  case E: (_ =? _)%bigN.
  { by move: (BigQ_red_den_neq0 a); rewrite Ea E. }
  case=> ->; rewrite -Z2Pos.inj_1 Z2Pos.inj_iff; [by move->| |done].
  by apply BigQ.N_to_Z_pos; rewrite -Z.eqb_neq -BigN.spec_eqb. }
move: H; rewrite Ea Eb /=.
case E: (_ =? _)%bigN.
{ by move: (BigQ_red_den_neq0 a); rewrite Ea E. }
case E': (_ =? _)%bigN.
{ by move: (BigQ_red_den_neq0 b); rewrite Eb E'. }
case=>->; rewrite Z2Pos.inj_iff; [by move->| |];
  by apply BigQ.N_to_Z_pos; rewrite -Z.eqb_neq -BigN.spec_eqb.
Transparent F.div.
Qed.

Instance : refines (r_ratBigQ ==> eqFIS) rat2FIS bigQ2FIS.
Proof.
rewrite /rat2FIS .
rewrite refinesE => x x' ref_x /=.
rewrite -[x']/(id1 x') -ref_x.
rewrite -[bigQ2FIS _]/(bigQ2FIS ((rat2bigQ \o bigQ2rat) x')).
apply refinesP.
refines_apply1.
rewrite /bigQ2FIS.
rewrite refinesE => y y' ref_y /=.
apply refinesP.
refines_apply1.
by rewrite refinesE.
by refines_apply1; rewrite refinesE.
Qed.

(** This "abstract/proof-oriented" instance is needed by [max_l, max_r] below,
given that we cannot use [Num.max] here (see the note before [max_l] above) *)

Global Instance leq_rat : leq_of rat := Num.Def.ler.

Lemma rat2R_le (x y : rat) : (x <= y)%Ri -> rat2R x <= rat2R y.
Proof. by move=> Hxy; apply/RleP; rewrite unfoldR; rewrite ler_rat. Qed.

Lemma max_l (x0 y0 : rat) : rat2R x0 <= rat2R (max x0 y0).
Proof.
rewrite /max; case: ifP; rewrite /leq_op /leq_rat => H; apply: rat2R_le =>//=.
by rewrite lerNgt ltr_def negb_and H orbT.
Qed.

Lemma max_r (x0 y0 : rat) : rat2R y0 <= rat2R (max x0 y0).
Proof.
by rewrite /max; case: ifP; rewrite /leq_op /leq_rat => H; apply: rat2R_le. Qed.

(** ** Part 3: Parametricity *)

Section refinement_soscheck.

Variables (A : comRingType) (C : Type) (rAC : A -> C -> Type).
Context `{!zero_of C, !one_of C, !opp_of C, !add_of C, !sub_of C, !mul_of C, !eq_of C}.
Context {n s : nat}.

Context `{!refines rAC 0%R 0%C}.
Context `{!refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) (fun x y => x + -y)%R sub_op}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> eq) eqtype.eq_op eq_op}.

Instance zero_instMnm : zero_of 'X_{1..n} := mnm0.

Instance zero_mpoly : zero_of (mpoly n A) := 0%R.

(* Goal forall n, nat_R n.+1 n.+1 <=> nat_R_S_R (nat_Rxx n). *)

Instance refine_check_base {s} :
  refines (ReffmpolyC rAC ==> RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_Rxx 1) ==> eq)
    (check_base_ssr (s:=s)) (check_base_eff (s:=s)).
Proof.
rewrite refinesE=> p p' rp z z' rz.
rewrite /check_base_ssr /check_base_eff /check_base.
set sm := iteri_ord _ _ _.
set sm' := iteri_ord _ _ _.
set l := _ p; set l' := _ p'.
suff : forall (m : 'X_{1..n}) m', Rseqmultinom m m' ->
  smem_ssr m sm = smem_eff m' sm'.
{ move=> H; apply refinesP, refines_bool_eq; rewrite refinesE.
  have : list_R (prod_R Rseqmultinom rAC) l l'.
  { rewrite /l /l'; apply refinesP; eapply refines_apply.
    { by apply ReffmpolyC_list_of_mpoly_eff. }
    by rewrite refinesE. }
  apply all_R=> mc mc' rmc.
  move: (H mc.1 mc'.1); rewrite /smem_ssr /smem_eff /smem=>H'.
  rewrite H'; [by apply bool_Rxx|].
  by apply refinesP; refines_apply1. }
move=> m m' rm.
rewrite /sm /sm'.
set f := fun _ => _; set f' := fun _ => iteri_ord _ _.
set P := fun s s' => smem_ssr m s = smem_eff m' s'; rewrite -/(P _ _).
apply iteri_ord_ind2 => [//|i i' se se' Hi Hi' Hse|//].
rewrite /P in Hse; rewrite {}/P {}/f {}/f'.
set f := fun _ => _; set f' := fun _ => _ _.
set P := fun s s' => smem_ssr m s = smem_eff m' s'; rewrite -/(P _ _).
apply iteri_ord_ind2=> [//|j j' se'' se''' Hj Hj' Hse''|//].
rewrite /P in Hse''; rewrite {}/P {}/f {}/f'.
rewrite /smem_ssr /smem /sadd /sadd_ssr in_cons.
rewrite /smem_ssr /smem in Hse''; rewrite Hse''.
rewrite /smem_eff /sadd_eff.
apply/idP/idP.
{ move/orP=> [].
  { move=>/eqP H; apply S.mem_1, S.add_1.
    apply/mnmc_eq_seqP/eqP/esym.
    set mm' := mul_monom_op _ _.
    apply/eqP;  move: H=>/eqP; set mm := mul_monom_op _ _.
    suff: (m == mm) = (m' == mm'); [by move=>->|].
    apply Rseqmultinom_eq; [by rewrite refinesE|].
    rewrite /mm /mm' /mul_monom_op /mul_monom_ssr /mul_monom_eff.
    refines_apply1; first refines_apply1; first refines_apply1;
      first refines_apply1; try by rewrite refinesE.
    refines_apply1; first refines_apply1; by rewrite refinesE. }
  by move/S.mem_2=> H; apply S.mem_1, S.add_2. }
move/S.mem_2.
set mm := mul_monom_op _ _; case Em' : (m' == mm).
{ case eqP=>//= Hm HIn; apply S.mem_1.
  move: HIn; apply S.add_3=>_; apply /Hm /eqP.
  rewrite /is_true -Em'; apply Rseqmultinom_eq.
  { by rewrite refinesE. }
  refines_apply1; first refines_apply1; first refines_apply1;
    first refines_apply1; try by rewrite refinesE.
  refines_apply1; first refines_apply1; by rewrite refinesE. }
move/S.add_3=>H; apply/orP; right; apply S.mem_1, H.
  by move/mnmc_eq_seqP; rewrite eq_sym Em'.
Qed.

Context `{!leq_of A}.
Context `{!leq_of C}.
Context `{!refines (rAC ==> rAC ==> bool_R) leq_op leq_op}.

Instance refine_max_coeff :
  refines (ReffmpolyC (n:=n) rAC ==> rAC) max_coeff_ssr max_coeff_eff.
Proof.
rewrite refinesE=> p p' rp.
rewrite /max_coeff_ssr /max_coeff_eff /max_coeff.
apply refinesP; refines_apply1.
refines_apply1.
refines_apply1.
apply refines_abstr2 => m m' rm mc mc' rmc.
do 2! refines_apply1; refines_abstr => *.
rewrite /max !ifE; eapply refines_if_expr; tc.
by move=> _ _; eapply refinesP; tc.
by move=> _ _; eapply refinesP; tc.
do 2! refines_apply1; refines_abstr => *.
rewrite /max !ifE; eapply refines_if_expr; tc.
all: by move=> _ _; eapply refinesP; tc.
Qed.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2A : F -> A}.  (* exact conversion for finite values *)
Context {A2F : A -> F}.  (* overapproximation *)
Context {F2C : F -> C}.  (* exact conversion for finite values *)
Context {C2F : C -> F}.  (* overapproximation *)
Variable eq_F : F -> F -> Prop.
Context `{!refines (eq_F ==> rAC) F2A F2C}.
Context `{!refines (rAC ==> eq_F) A2F C2F}.

Let eqFIS := eq_F.
Context `{!Equivalence eqFIS}.
Context `{!refines (eqFIS) zero_instFIS zero_instFIS}.
Context `{!refines (eqFIS) one_instFIS one_instFIS}.
Context `{!refines (eqFIS ==> eqFIS) opp_instFIS opp_instFIS}.
Context `{!refines (eqFIS ==> eqFIS) sqrt_instFIS sqrt_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) add_instFIS add_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) mul_instFIS mul_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) div_instFIS div_instFIS}.
Context `{ref_fin : !refines (eqFIS ==> bool_R) (@finite fs) (@finite fs)}.
Context `{!refines (eqFIS ==> eqFIS ==> bool_R) eq_instFIS eq_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> bool_R) leq_instFIS leq_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> bool_R) lt_instFIS lt_instFIS}.

Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) addup_instFIS addup_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) subdn_instFIS subdn_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) mulup_instFIS mulup_instFIS}.
Context `{!refines (eqFIS ==> eqFIS ==> eqFIS) divup_instFIS divup_instFIS}.
Context `{!refines (nat_R ==> eqFIS) nat2Fup_instFIS nat2Fup_instFIS}.

Hypothesis eqFIS_P : forall x y, reflect (eqFIS x y) (eq_instFIS x y).

Local Instance refine_soscheck {s} :
  refines (ReffmpolyC rAC ==> RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_Rxx 1) ==>
          RseqmxC eq_F (nat_Rxx s.+1) (nat_Rxx s.+1) ==> bool_R)
    (soscheck_ssr (s:=s) (F2T:=F2A) (T2F:=A2F))
    (soscheck_eff (n:=n) (s:=s) (F2T:=F2C) (T2F:=C2F)).
Proof.
rewrite refinesE=> p p' rp z z' rz Q Q' rQ.
rewrite /soscheck_ssr /soscheck_eff /soscheck.
suff_eq bool_Rxx.
apply f_equal2.
{ apply refinesP; refines_apply. }
eapply refinesP, refines_bool_eq.
eapply refines_apply.
eapply refines_apply.
eapply (refine_posdef_check_itv' (fs := fs) (eqFIS := eqFIS)).
exact: eqFIS_P.
exact: id.
eapply refines_apply. tc.
eapply refines_apply. tc.
eapply refines_apply. tc.
eapply refines_apply.
eapply refines_apply.
eapply refines_apply. tc.
eapply refines_apply.
eapply refines_apply. tc.
eapply refines_apply. tc.
eapply refines_apply.
eapply refines_apply. tc.
refines_abstr; simpl. (* elim comp *)
eapply refines_apply; tc.
by rewrite refinesE.
all: tc.
by rewrite refinesE /Rord.
by rewrite refinesE /Rord.
Qed.

Variant RWit (w : sz_witness) (w' : sz_witness) : Type :=
| RWit_spec :
    forall s p z Q p' z' Q' (_ : w = Wit p z Q) (_ : w' = Wit p' z' Q')
           (_ : ReffmpolyC (n:=n) rAC p p')
           (_ : RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_Rxx 1) z z')
           (_ : RseqmxC eq_F (nat_Rxx s.+1) (nat_Rxx s.+1) Q Q'),
      RWit w w'.

Lemma refine_soscheck_hyps :
  refines (list_R (prod_R (ReffmpolyC rAC) RWit) ==>
           ReffmpolyC rAC ==> 
           RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_Rxx 1) ==>
           RseqmxC eq_F (nat_Rxx s.+1) (nat_Rxx s.+1) ==>
           bool_R)
    (soscheck_hyps_ssr (s:=s) (F2T:=F2A) (T2F:=A2F))
    (soscheck_hyps_eff (n:=n) (s:=s) (F2T:=F2C) (T2F:=C2F)).
Proof.
rewrite refinesE=> p p' rp pszQ pszQ' rpszQ z z' rz Q Q' rQ.
rewrite /soscheck_hyps_ssr /soscheck_hyps_eff /soscheck_hyps.
apply andb_R.
{ apply refinesP; refines_apply.
  rewrite refinesE => p'0 p'0' rp'0 pszQi pszQi' rpszQi.
  move: rpszQi; case pszQi, pszQi' => /=; case s0, s1 => rpszQi.
  apply refinesP; refines_apply; inversion rpszQi; rewrite refinesE //.
  by inversion X4; inversion H2; inversion H4. }
apply (all_R (T_R := prod_R (ReffmpolyC rAC) RWit)) => //.
case=> p0 w; case=> p0' w' rpw /=.
inversion rpw; inversion X4; rewrite H2 H4 /=.
apply refinesP; refines_apply.
Qed.

Lemma refine_has_const :
  refines (RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_Rxx 1) ==> bool_R)
    (has_const_ssr (s:=s)) (has_const_eff (n:=n)).
Proof.
rewrite refinesE=> z z' rz.
rewrite /has_const_ssr /has_const_eff /has_const.
rewrite /eq_op /monom_eq_ssr /monom_eq_eff.
suff_eq bool_Rxx.
set z00 := fun_of_op z _ _; set z'00 := fun_of_op z' _ _.
suff : z00 == monom0_ssr = (z'00 == @mnm0_seq n).
{ by move->; apply/idP/idP; [apply/mnmc_eq_seqP|move/mnmc_eq_seqP]. }
apply Rseqmultinom_eq.
{ eapply refines_apply; [eapply refines_apply|].
  { eapply refines_apply; tc. }
  { by rewrite refinesE. }
  by rewrite refinesE. }
apply refine_mnm0.
Qed.

End refinement_soscheck.

Section refinement_interp_poly.

(* TODO: PR CoqEAL ? *)
Lemma nth_lt_list_R T1 T2 (T_R : T1 -> T2 -> Type) (x01 : T1) (x02 : T2) s1 s2 :
  size s1 = size s2 ->
  (forall n, (n < size s1)%N -> T_R (nth x01 s1 n) (nth x02 s2 n)) -> list_R T_R s1 s2.
Proof.
elim: s1 s2 => [|hs1 ts1 Hind]; [by move=> [//|]|].
move=> [//|hs2 ts2 /= Hs H]; apply list_R_cons_R; [by apply (H O)|].
by apply Hind; [apply eq_add_S|move=> n Hn; apply (H (S n))].
Qed.

(* TODO: begin PR CoqEAL Multipoly ? *)
Lemma size_seq_ReffmpolyC (A : ringType) (C : Type) (rAC : A -> C -> Type)
      (n k : nat) (lq : k.-tuple {mpoly A[n]}) (lq' : seq (effmpoly C)) :
  seq_ReffmpolyC rAC lq lq' -> size lq' = k.
Proof.
move=> [b [[Hb _] Hb']]; rewrite -Hb; apply esym, nat_R_eq, (size_R Hb').
Qed.

Lemma nth_seq_ReffmpolyC (A : ringType) (C : Type) (rAC : A -> C -> Type)
      (n k : nat) (lq : k.-tuple {mpoly A[n]}) (lq' : seq (effmpoly C)) :
  seq_ReffmpolyC rAC lq lq' ->
  forall i, refines (ReffmpolyC rAC) lq`_i (nth mp0_eff lq' i).
Proof.
move=> [b [[Hb Hb'] Hb'']] i; apply (refines_trans _ (Hb' i)).
rewrite refinesE; apply nth_R; [|by []|apply nat_Rxx].
apply refinesP, refine_M_hrel_mp0_eff.
Qed.

Lemma seq_ReffmpolyC_spec (A : ringType) (C : Type) (rAC : A -> C -> Type)
      (n k : nat) (lq : k.-tuple {mpoly A[n]}) (lq' : seq (effmpoly C)) :
  ((size lq' = k)
   * (forall i, refines (ReffmpolyC rAC) lq`_i (nth mp0_eff lq' i)))%type ->
  seq_ReffmpolyC rAC lq lq'.
Proof.
move=> [Hs H].
have H' : forall i, ReffmpolyC rAC lq`_i (nth mp0_eff lq' i).
{ by move=> i; move: (H i); rewrite refinesE. }
exists [seq projT1 (H' i) | i <- iota O k]; split; [split|].
{ by rewrite size_map size_iota. }
{ move=> i; case (ltnP i k) => Hk.
  { rewrite (nth_map O) ?size_iota // nth_iota //= refinesE.
    by case (H' _) => /= ? [? _]. }
  rewrite nth_default ?size_tuple // nth_default ?size_map ?size_iota //.
  apply refine_mp0_eff. }
apply (nth_lt_list_R (x01:=mp0_eff) (x02:=mp0_eff)).
{ by rewrite size_map size_iota. }
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map O) ?size_iota // nth_iota //.
by case (H' _) => /= ? [].
Qed.
(* TODO: end PR CoqEAL Multipoly *)

Lemma refine_interp_poly n ap : vars_ltn n ap ->
  refines (ReffmpolyC r_ratBigQ) (interp_poly_ssr n ap) (interp_poly_eff n ap).
Proof.
elim/abstr_poly_rect': ap n => //.
{ move=> c ? /= _; eapply refines_apply;
    [eapply ReffmpolyC_mpolyC_eff; try by tc|].
  by rewrite refinesE. }
{ move=> i [|n] //= Hn.
  rewrite -(GRing.scale1r (mpolyX _ _)) -/(mpvar 1 1 (inord i)).
  eapply refines_apply; first eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpvar_eff. }
  { tc. }
  { by rewrite refinesE. }
  by rewrite refinesE /Rord0 -bin_of_natE bin_of_natK inordK. }
{ move=> p Hp q Hq n /= /andP [] Hlp Hlq.
  rewrite /GRing.add /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_add_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq n /= /andP [] Hlp Hlq.
  set p' := _ _ p; set q' := _ _ q.
  rewrite -[(_ - _)%R]/(mpoly_sub p' q').
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_sub_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq n /= /andP [] Hlp Hlq.
  rewrite /GRing.mul /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_mul_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp m n /= Hlp.
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_exp_eff; tc. }
  { by apply Hp. }
  by rewrite refinesE. }
move=> p Hp qi Hqi n /= /andP [Hnqi Hnp].
case (sumb _) => [e|]; [|by rewrite size_map eqxx].
eapply refines_apply; [|by apply Hp].
eapply refines_apply; [by apply ReffmpolyC_comp_mpoly_eff; tc|].
rewrite refinesE; apply seq_ReffmpolyC_spec; split; [by rewrite size_map|].
move=> i; rewrite ssrcomplements.tval_tcast in_tupleE.
case (ltnP i (size qi)) => Hi.
{ rewrite !(nth_map (Const 0)) //.
  by apply (all_type_nth _ Hqi Hi); move: Hnqi => /all_nthP; apply. }
rewrite !nth_default ?size_map //; apply ReffmpolyC_mp0_eff.
Qed.

End refinement_interp_poly.

(** ** Part 4: The final tactic *)

Lemma map_R_nth (T1 T2 : Type) (x0 : T2) (T_R : T1 -> T2 -> Type) (f : T2 -> T1) l :
  (forall i, (i < size l)%N -> T_R (f (nth x0 l i)) (nth x0 l i)) ->
  list_R T_R [seq f x | x <- l] l.
Proof.
elim: l=> [|a l IH H]; first by simpl.
constructor 2.
{ by move: (H 0%N) => /=; apply. }
apply IH=> i Hi.
by move: (H i.+1)=> /=; apply; rewrite ltnS.
Qed.

Lemma listR_seqmultinom_map (n : nat)
  (z : seq (seq BinNums.N)) :
  let za := [seq [:: x] | x <- z] in
  (all (fun m => size m == n) z) ->
  list_R (list_R (Rseqmultinom (n := n)))
    (map_seqmx (spec (spec_of := multinom_of_seqmultinom_val n)) za)
    za.
Proof.
move=> za H.
apply (map_R_nth (x0:=[::]))=> i Hi.
rewrite size_map in Hi.
apply (map_R_nth (x0:=[::]))=> j Hj.
rewrite /spec.
apply refinesP, refine_multinom_of_seqmultinom_val.
move /all_nthP in H.
rewrite /za (nth_map [::]) //.
suff -> : j = 0%N by simpl; apply H.
move: Hj; rewrite /za (nth_map [::]) //=.
by rewrite ltnS leqn0; move/eqP->.
Qed.

Lemma eqFIS_P x y : reflect (eqFIS x y) (eq_instFIS x y).
Proof.
apply: (iffP idP).
{ rewrite /eqFIS /eq_instFIS /fieq /float_infnan_spec.ficompare /= /ficompare;
  rewrite F.cmp_correct !F.real_correct;
  do 2![case: F.toX =>//=] => rx ry /=; case: Rcompare_spec =>// ->//. }
rewrite /eqFIS /eq_instFIS /fieq /float_infnan_spec.ficompare /= /ficompare;
  rewrite F.cmp_correct !F.real_correct;
  do 2![case: F.toX =>//=] => rx ry [] <-; case: Rcompare_spec =>//;
  by move/Rlt_irrefl.
Qed.

Ltac op1 lem := let H := fresh in
  rewrite refinesE /eqFIS => ?? H /=; rewrite !lem H.

Ltac op2 lem := let H1 := fresh in let H2 := fresh in
  rewrite refinesE /eqFIS => ?? H1 ?? H2 /=; rewrite !lem H1 H2.

Ltac op22 lem1 lem2 := let H1 := fresh in let H2 := fresh in
  rewrite refinesE /eqFIS => ?? H1 ?? H2 /=; rewrite !(lem1, lem2) H1 H2.

Ltac op202 tac lem1 lem2 := let H1 := fresh in let H2 := fresh in
  rewrite refinesE /eqFIS => ?? H1 ?? H2 /=; tac; rewrite !(lem1, lem2) H1 H2.

Lemma Rle_minus_le r1 r2 : (0 <= r2 - r1)%Re -> (r1 <= r2)%Re.
Proof. now intros H0; apply Rge_le, Rminus_ge, Rle_ge. Qed.

Lemma Rlt_minus_lt r1 r2 : (0 < r2 - r1)%Re -> (r1 < r2)%Re.
Proof. now intros H0; apply Rgt_lt, Rminus_gt, Rlt_gt. Qed.

(** *** The main tactic. *)

Inductive p_abstr_ineq :=
| ILe of p_abstr_poly & p_abstr_poly
| IGe of p_abstr_poly & p_abstr_poly
| ILt of p_abstr_poly & p_abstr_poly
| IGt of p_abstr_poly & p_abstr_poly
.

Inductive p_abstr_hyp :=
| Hineq of p_abstr_ineq
| Hand of p_abstr_hyp & p_abstr_hyp
.

Inductive p_abstr_goal :=
  | Gineq of p_abstr_ineq
  | Ghyp of p_abstr_hyp & p_abstr_goal
  .

Fixpoint interp_p_abstr_ineq (vm : seq R) (i : p_abstr_ineq) {struct i} : Prop :=
  match i with
  | ILe p q => Rle (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | IGe p q => Rge (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | ILt p q => Rlt (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  | IGt p q => Rgt (interp_p_abstr_poly vm p) (interp_p_abstr_poly vm q)
  end.

Fixpoint interp_p_abstr_hyp (vm : seq R) (h : p_abstr_hyp) : Prop :=
  match h with
  | Hineq i => interp_p_abstr_ineq vm i
  | Hand a b => interp_p_abstr_hyp vm a /\ interp_p_abstr_hyp vm b
  end.

Fixpoint interp_p_abstr_goal (vm : seq R) (g : p_abstr_goal) {struct g} : Prop :=
  match g with
  | Gineq i => interp_p_abstr_ineq vm i
  | Ghyp h g => interp_p_abstr_hyp vm h -> interp_p_abstr_goal vm g
  end.

(** (li, p, true) stands for /\_i 0 <= li -> 0 < p
    (li, p, false) stands for /\_i 0 <= li -> 0 <= p *)
Definition abstr_goal := (seq p_abstr_poly * p_abstr_poly * bool)%type.

Definition sub_p_abstr_poly p q :=
  match p, q with
  | PConst PConstR0, q => POpp q
  | p, PConst PConstR0 => p
  | _, _ => PSub p q
  end.

Lemma sub_p_abstr_poly_correct vm p q :
  interp_p_abstr_poly vm (sub_p_abstr_poly p q) =
  interp_p_abstr_poly vm p - interp_p_abstr_poly vm q.
Proof.
case: p=> [p|n|p|p p'|p p'|p p'|p n|p n|p pi];
case: q=> [q|d|q|q q'|q q'|q q'|q d|q d|q qi] //;
try (case: p =>//=; case: q =>//= *; ring).
by case: p =>//= *; ring.
by case: q =>//= *; ring.
Qed.

Fixpoint seq_p_abstr_poly_of_hyp h :=
  match h with
  | Hineq i =>
    match i with
    | ILt p q | ILe p q => [:: sub_p_abstr_poly q p]
    | IGt p q | IGe p q => [:: sub_p_abstr_poly p q]
    end
  | Hand a b =>
    seq_p_abstr_poly_of_hyp a ++ seq_p_abstr_poly_of_hyp b
  end.

Fixpoint abstr_goal_of_p_abstr_goal_aux
  (accu : seq p_abstr_poly) (g : p_abstr_goal) {struct g} : abstr_goal :=
  match g with
  | Gineq i =>
    match i with
    | ILt p q => (accu, (sub_p_abstr_poly q p), true)
    | IGt p q => (accu, (sub_p_abstr_poly p q), true)
    | ILe p q => (accu, (sub_p_abstr_poly q p), false)
    | IGe p q => (accu, (sub_p_abstr_poly p q), false)
    end
  (* Note: strict hyps are weakened to large hyps *)
  | Ghyp h g =>
    abstr_goal_of_p_abstr_goal_aux (accu ++ seq_p_abstr_poly_of_hyp h) g
  end.

Definition abstr_goal_of_p_abstr_goal := abstr_goal_of_p_abstr_goal_aux [::].

Definition interp_abstr_goal (vm : seq R) (g : abstr_goal) : Prop :=
  match g with
  | (l, p, true) =>
      all_prop (fun p => 0 <= interp_p_abstr_poly vm p)%Re l ->
      0 < interp_p_abstr_poly vm p
  | (l, p, false) =>
      all_prop (fun p => 0 <= interp_p_abstr_poly vm p)%Re l ->
      0 <= interp_p_abstr_poly vm p
  end.

Ltac tac := rewrite /= !sub_p_abstr_poly_correct; psatzl R.

Theorem abstr_goal_of_p_abstr_goal_correct vm (g : p_abstr_goal) :
  interp_abstr_goal vm (abstr_goal_of_p_abstr_goal g) ->
  interp_p_abstr_goal vm g.
Proof.
rewrite /abstr_goal_of_p_abstr_goal.
have : all_prop (fun p => 0 <= interp_p_abstr_poly vm p) [::] by simpl.
elim: g [::] => [p|h g IHg] l.
{ case: p => p q /=; do [case: l => [|x l]; last move=> Hxl /(_ Hxl); tac]. }
move=> /= Hl Hlhg Hh.
apply: IHg Hlhg.
apply/all_prop_cat; split =>//; clear - Hh.
elim: h Hh => [i Hi|a A b B H]  /=.
{ by case: i Hi =>//= p q; tac. }
have {H} [H1 H2] := H.
by apply/all_prop_cat; split =>//=; auto.
Qed.

Definition soscheck_hyps_eff_wrapup (vm : seq R) (g : p_abstr_goal)
  (szQi : seq (seq (seq BinNums.N * bigQ)
               * (seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ)))))
  (zQ : seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ))) :=
  let '(papi, pap, strict) := abstr_goal_of_p_abstr_goal g in
  let n := size vm in
  let ap := abstr_poly_of_p_abstr_poly pap in
  let bp := interp_poly_eff n ap in
  let apl := [seq abstr_poly_of_p_abstr_poly p | p <- papi] in
  let bpl := [seq interp_poly_eff n p | p <- apl] in
  let s := size zQ.1 in
  let s' := s.-1 in
  let z := map (fun x => [:: x]) zQ.1 in
  let Q := map (map F2FI) zQ.2 in
  let szQl :=
    map (fun szQ =>
           let s := mpoly_of_list_eff szQ.1 in
           let sz := size szQ.2.1 in
           let z := map (fun x => [:: x]) szQ.2.1 in
           let Q := map (map F2FI) szQ.2.2 in
           Wit (mx := @hseqmx) (fs := fs) s (s := sz.-1) z Q)
        szQi in
  let pszQl := zip bpl szQl in
  [&&
   n != 0%N,
   all (fun m => size m == n) zQ.1,
   all (fun szQ => all (fun m => size m == n) szQ.2.1) szQi,
   all (fun szQ => match szQ with
                     | Wit s _ _ _ => P.for_all (fun k _ => size k == n) s
                   end) szQl,
   s != 0%N,
   size Q == s,
   all (fun e => size e == s) Q,
   all (fun szQ => size szQ.2.1 != 0%N) szQi,
   all (fun szQ => size szQ.2.2 == size szQ.2.1) szQi,
   all (fun szQ => (all (fun e => size e == size szQ.2.1) szQ.2.2)) szQi,
   vars_ltn n ap,
   all (vars_ltn n) apl,
   size papi == size szQl,
   strict ==> has_const_eff (s:=s.-1) (n:=n) z &
   soscheck_hyps_eff
     (n := n) (s := s')
     (fs := coqinterval_infnan.coqinterval_round_up_infnan)
     (F2T := F2bigQ \o (*FI2F*) coqinterval_infnan.FI_val)
     (T2F := F2FI \o bigQ2F')
     pszQl bp z Q].

Theorem soscheck_hyps_eff_wrapup_correct
  (vm : seq R) (g : p_abstr_goal)
  (szQi : seq (seq (seq BinNums.N * bigQ)
               * (seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ)))))
  (zQ : (seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ)))) :
  soscheck_hyps_eff_wrapup vm g szQi zQ ->
  interp_p_abstr_goal vm g.
Proof.
rewrite /soscheck_hyps_eff_wrapup => hyps.
apply abstr_goal_of_p_abstr_goal_correct; move: hyps.
set papipapb := _ g; case papipapb; case=> papi pap b {papipapb}.
set n := size vm.
set ap := abstr_poly_of_p_abstr_poly pap.
set bp := interp_poly_eff n ap.
set apl := [seq abstr_poly_of_p_abstr_poly p | p <- papi].
set bpl := [seq interp_poly_eff n p | p <- apl].
set s := size zQ.1.
set s' := s.-1.
set z := map (fun x => [:: x]) zQ.1.
set Q := map (map F2FI) zQ.2.
set szQl := map _ szQi.
set pszQl := zip bpl szQl.
pose zb := @spec_seqmx _ (@mnm0 n) _ (@multinom_of_seqmultinom_val n) s'.+1 1 z.
pose Qb := @spec_seqmx _ (FIS0 fs) _ (id) s'.+1 s'.+1 Q.
pose szQlb :=
  [seq
     match szQ with
       | Wit s sz z Q =>
         let sb := mpoly_of_effmpoly_val n (M.map bigQ2rat s) in
         let zb := @spec_seqmx _ (@mnm0 n) _ (@multinom_of_seqmultinom_val n) sz.+1 1 z in
         let Qb := @spec_seqmx _ (FIS0 fs) _ (id) sz.+1 sz.+1 Q in
         Wit sb zb Qb
     end | szQ <- szQl].
pose bplb := [seq interp_poly_ssr n p | p <- apl].
pose pszQlb := zip bplb szQlb.
case/and5P => Hn Hz HszQi_s Hns /and5P [Hs HzQ HzQ' HszQi].
case/and5P => HszQi_z HszQi_z' Hltn Hltn' /and3P [Hsbpl Hstrict Hsos_hyps].
have Hs' : s'.+1 = s by rewrite prednK // lt0n Hs.
rewrite /interp_abstr_goal.
set apapi := all_prop _ _.
suff: apapi -> if b then 0 < interp_p_abstr_poly vm pap
               else 0 <= interp_p_abstr_poly vm pap by case b.
rewrite {}/apapi => Hall_prop.
rewrite interp_poly_ssr_correct' //.
set x := fun _ => _.
have Hall_prop' :
  all_prop (fun pszQ => 0 <= (map_mpoly ratr pszQ.1).@[x]) pszQlb.
{ move: Hsbpl Hltn' Hall_prop; rewrite /pszQlb /bplb /bpl /apl.
  have -> : size szQl = size szQlb by rewrite /szQlb size_map.
  move: szQlb {pszQlb}; elim papi => /= [|h t Hind]; [by case|].
  case=> // szQlbh szQlbt /= /eqP [] HszQlbt /andP [] Hltnh Hltnt [] H1 H2.
  split; [|by apply Hind; [apply/eqP| |]].
  by rewrite -interp_poly_ssr_correct'. }
set papx := _.@[x].
suff: 0 <= papx /\ (has_const_ssr zb -> 0 < papx).
{ move: Hstrict; case b => /= [Hcz [] _ Hczb|_ [] //]; apply Hczb.
  move: Hcz; rewrite /is_true => <-.
  apply refines_eq, refines_bool_eq; refines_apply1.
  { apply refine_has_const. }
  rewrite /zb /z.
  rewrite refinesE; apply RseqmxC_spec_seqmx.
  { apply /andP; split; [by rewrite size_map Hs'|].
    by apply /allP => x' /mapP [] x'' _ ->. }
  by apply listR_seqmultinom_map. }
move: Hall_prop'.
apply soscheck_hyps_correct with
  (1 := GRing.RMorphism.base (ratr_is_rmorphism _))
  (2 := rat2FIS_correct)
  (3 := rat2R_FIS2rat)
  (4 := max_l)
  (5 := max_r)
  (6 := GRing.RMorphism.mixin (ratr_is_rmorphism _))
  (Q0 := Qb).
move: Hsos_hyps; apply etrans.
apply refines_eq, refines_bool_eq.
refines_apply1; first refines_apply1;
  first refines_apply1; first refines_apply1.
{ eapply (refine_soscheck_hyps (eq_F := eqFIS) (rAC := r_ratBigQ)).
  exact: eqFIS_P. }
{ rewrite refinesE; apply zip_R.
  { rewrite /bplb /bpl; move: Hltn'.
    elim apl => [|h t Hind] //= /andP [] Hltnh Hltnt; apply list_R_cons_R.
    { by apply refinesP, refine_interp_poly. }
    by apply Hind. }
  move: Hns HszQi HszQi_s HszQi_z HszQi_z'; rewrite /szQlb /szQl.
  elim szQi => [//=|h t Hind] /andP [hnsh Hnst].
  move=> /andP [Hsh Hst] /andP [Hnh Hnt] /andP [Hsh' Hst'] /andP [Hsh'' Hst''].
  apply list_R_cons_R; [|by apply Hind].
  set s0' := mpoly_of_list_eff h.1; set s0 := mpoly_of_effmpoly_val _ _.
  set z0' := map _ h.2.1; set z0 := spec_seqmx _ _ z0'.
  set Q0' := map _ h.2.2; set Q0 := spec_seqmx _ _ Q0'.
  apply (RWit_spec (p:=s0) (z:=z0) (Q:=Q0) (p':=s0') (z':=z0') (Q':=Q0')) => //.
  { exists (M.map bigQ2rat s0'); split.
    { rewrite /Reffmpoly /s0 /mpoly_of_effmpoly_val /ofun_hrel /mpoly_of_effmpoly.
      rewrite ifT // /is_true (P.for_all_iff _) => k e.
      { rewrite F.map_mapsto_iff => [] [] x' [] _ Hk.
        move: hnsh; rewrite /is_true (P.for_all_iff _) -/s0' => H.
        { by move: (H _ _ Hk). }
        by move=> y' /mnmc_eq_seqP /eqP ->. }
      by move=> /mnmc_eq_seqP /eqP ->. }
    split=> [k|k e e']; [by apply F.map_in_iff|].
    move /(map_mapsto_iff_dec s0' k e bigQ2rat) => [] e'' [] He'' Hke'' Hke'.
    by have <- : e'' = e'; [move: Hke'' Hke'; apply F.MapsTo_fun|]. }
  { eapply RseqmxC_spec_seqmx.
    { rewrite prednK ?lt0n // size_map eqxx /= /z.
      by apply/allP => x' /mapP [y Hy] ->. }
    apply: listR_seqmultinom_map.
    by rewrite ?lt0n // size_map eqxx. }
  apply refinesP; refines_trans; rewrite refinesE.
  { eapply Rseqmx_spec_seqmx.
    rewrite size_map prednK ?lt0n // Hsh' /= all_map /is_true -Hsh''.
    by apply eq_all => e /=; rewrite size_map. }
  by apply list_Rxx => x'; apply list_Rxx. }
{ by apply refine_interp_poly; rewrite ?lt0n. }
{ rewrite refinesE; eapply RseqmxC_spec_seqmx.
  { rewrite prednK ?lt0n // size_map eqxx /= /z.
    by apply/allP => x' /mapP [y Hy] ->. }
  apply: listR_seqmultinom_map.
  by rewrite ?lt0n // size_map eqxx. }
refines_trans.
{ rewrite refinesE; eapply Rseqmx_spec_seqmx.
  rewrite !size_map in HzQ.
  by rewrite prednK ?lt0n // !size_map HzQ. }
{ by rewrite refinesE; apply: list_Rxx => x'; apply: list_Rxx => y. }
Unshelve.
{ split =>//.
  by move=> x' y z' Hxy Hyz; red; rewrite Hxy. }
{ by rewrite refinesE. }
{ by rewrite refinesE. }
{ by op1 F.neg_correct. }
{ by op1 F.sqrt_correct. }
{ by op2 F.add_correct. }
{ by op2 F.mul_correct. }
{ by op2 F.div_correct. }
{ op1 F.real_correct; exact: bool_Rxx. }
{ by op202 ltac:(rewrite /leq_instFIS /file /= /ficompare /=; suff_eq bool_Rxx)
  F.cmp_correct F.real_correct. }
{ by op202 ltac:(rewrite /lt_instFIS /filt /= /ficompare /=; suff_eq bool_Rxx)
  F.cmp_correct F.real_correct. }
{ by op2 F.add_correct. }
{ by op22 F.neg_correct F.add_correct. }
{ by op2 F.mul_correct. }
{ by op2 F.div_correct. }
by rewrite refinesE => ?? H; rewrite (nat_R_eq H).
Qed.

Ltac get_ineq i l k :=
  let aux c x y :=
      get_poly x l ltac:(fun res => match res with
      | (?p, ?l) =>
        get_poly y l ltac:(fun res => match res with
        | (?q, ?l) =>
          let res := constr:((c p q, l)) in k res
        end)
      end) in
  match i with
  | Rle ?x ?y => aux ILe x y k
  | Rge ?x ?y => aux IGe x y k
  | Rlt ?x ?y => aux ILt x y k
  | Rgt ?x ?y => aux IGt x y k
  | _ => k false
  end.

Ltac get_hyp h l :=
  match h with
  | and ?a ?b =>
    match get_hyp a l with
    | (?a, ?l) =>
      match get_hyp b l with
      | (?b, ?l) => constr:((Hand a b, l))
      | false => false
      end
    | false => false
    end
  | _ => match get_ineq h l with
        | (?i, ?l) => constr:((Hineq i, l))
        | _ => false
        end
  end.

Ltac get_goal g l :=
  match g with
  | (?h -> ?g) =>
    match get_hyp h l with
    | (?h, ?l) =>
      match get_goal g l with
      | (?g, ?l) => constr:((Ghyp h g, l))
      | false => false
      end
    | false => false
    end
  | _ => match get_ineq g l with
        | (?i, ?l) => constr:((Gineq i, l))
        | false => false
        end
  end.

Ltac do_validsdp params :=
  lazymatch goal with
  | [ |- ?g ] =>
    match get_goal g (@Datatypes.nil R) with
    | (?g, ?vm) =>
      abstract (
      let n := eval vm_compute in (size vm) in
      let lgb := eval vm_compute in (abstr_goal_of_p_abstr_goal g) in
      match lgb with
      | (?l, ?p, ?b) =>
        let pi := constr:(map (@M.elements bigQ \o
                               interp_poly_eff n \o
                               abstr_poly_of_p_abstr_poly) l) in
        let p := constr:((@M.elements bigQ \o
                          interp_poly_eff n \o
                          abstr_poly_of_p_abstr_poly) p) in
        let ppi := eval vm_compute in (p, pi) in
        let zQ_szQi := fresh "zQ_szQi" in
        (soswitness of ppi as zQ_szQi with params);
        apply (@soscheck_hyps_eff_wrapup_correct vm g zQ_szQi.2 zQ_szQi.1);
        (vm_cast_no_check (erefl true))
      end)
    | false => fail 100 "unsupported goal"
    | _ => fail "validsdp failed to conclude"
    end
  end.

(* [tuple_to_list] was taken from CoqInterval *)
Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | ?b => constr:(b :: l)
  | ?z => fail 100 "Unknown tactic parameter" z
  end.

Tactic Notation "validsdp" :=
  do_validsdp (@Datatypes.nil validsdp_tac_parameters).

Tactic Notation "validsdp" "with" constr(params) :=
 do_validsdp ltac:(tuple_to_list params (@Datatypes.nil validsdp_tac_parameters)).

(** Some quick tests. *)

Let test1 : forall x y : R, 0 < x -> 1 <= y -> x + y >= 0.
intros x y.
Time validsdp.
Qed.

Let test2 : forall x y : R, (2 / 3 * x ^ 2 + y ^ 2 >= 0)%Re.
intros x y.
Time validsdp.
Qed.

Let test3 : forall x y : R, (2 / 3 * x ^ 2 + y ^ 2 + 1 > 0)%Re.
intros x y.
Time validsdp.
Qed.
