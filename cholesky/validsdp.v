Require Import Reals Flocq.Core.Fcore_Raux QArith BigZ BigQ Psatz FSetAVL.
From Flocq Require Import Fcore.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements seqmatrix.
From SsrMultinomials Require Import mpoly (* freeg *).
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix coqinterval_infnan.
Import Refinements.Op.
Require Import cholesky_prog multipoly.
Require Import Quote.

Inductive abstr_poly :=
  (* | Const of Poly.t *)
  (* | Mult_scalar of Poly.Coeff.t * abstr_poly *)
  | Const of R
  | Var of index
  | Add of abstr_poly & abstr_poly
  | Sub of abstr_poly & abstr_poly
  | Mul of abstr_poly & abstr_poly
  | Pow of abstr_poly & nat
  (* | Compose of abstr_poly * abstr_poly list *).

Fixpoint eval_abstr_poly (vm : varmap R) (f : abstr_poly) {struct f} : R :=
  match f with
  | Const r => r
  | Add p q => Rplus (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Sub p q => Rminus (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Mul p q => Rmult (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Pow p n => pow (eval_abstr_poly vm p) n
  | Var i => varmap_find R0 i vm
  end.

Definition const (r : R) := r.

Goal forall x y : R, (1 + 6 * x * pow y 1) >= 0.
  intros.
  change 2 with (IZR 2); change R1 with (IZR 1); change R0 with (IZR 0);
  repeat
  rewrite <- plus_IZR || rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus.
  match goal with
    | [ |- (?p >= IZR 0)%R ] =>
    quote eval_abstr_poly [O S xO xH xI Zplus Z0 Zpos Zneg IZR Zmult] in p using (fun x => idtac x)
  end.
Abort.

(** ** Part 0: Definition of operational type classes *)

Class sempty_class set := sempty : forall {T: Type}, set T.
Class sadd_class set := sadd : forall {T}, T -> set T -> set T.
Class smem_class set := smem : forall {T}, T -> set T -> bool.

Class mul_monom monom := mul_monom_op :
  forall {n : nat}, monom n -> monom n -> monom n.

Class list_of_poly_class monom poly := list_of_poly :
  forall {T : Type} {n : nat}, poly n T -> seq (monom n * T).

Class polyC_class poly := polyC :
  forall {T : Type} {n : nat}, T -> poly n T.

Class polyX_class monom poly := polyX :
  forall {T : Type} {n : nat}, monom n -> poly n T.

Class poly_sub poly := poly_sub_op :
  forall {T : Type} {n : nat}, poly n T -> poly n T -> poly n T.

(* TODO: regarder si pas déjà dans Coq_EAL *)
Class max_class T := max : T -> T -> T.

(** ** Part 1: Generic programs *)

Section generic_soscheck.

Context {monom : nat -> Type} {poly : nat -> Type -> Type}.
Context `{!mul_monom monom, !list_of_poly_class monom poly}.
Context `{!polyC_class poly, !polyX_class monom poly, !poly_sub poly}.

Context {set : Type -> Type}.
Context `{!sempty_class set, !sadd_class set, !smem_class set}.

Context {n s : nat} {T : Type}.
Context `{!zero T, !opp T, !max_class T}.
Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!fun_of (monom n) ord (mx (monom n))}.
Context `{!fun_of (poly n T) ord (mx (poly n T))}.
Context `{!I0_class ord s, !I0_class ord 1, !succ0_class ord s(*, !nat_of_class ord s*)}.

Definition check_base (p : poly n T) (z : mx (monom n) s 1) : bool :=
  let sm :=
    iteri_ord s
      (fun i =>
         iteri_ord s
           (fun j => sadd (mul_monom_op (fun_of_matrix z i I0)
                                        (fun_of_matrix z j I0))))
      sempty in
  all (fun mc => smem mc.1 sm) (list_of_poly p).

Context {F : Type}.  (* Floating-point values. *)
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Context `{!map_mx_class mx}.
Context `{!transpose_class (mx (poly n T))}.
(* Multiplication of matrices of polynomials. *)
Context `{!hmul (mx (poly n T))}.

Definition soscheck' (p : poly n T)
                    (z : mx (monom n) s 1) (Q : mx F s s) : T :=
  let r :=
    let p' :=
      let zp := map_mx polyX z in
      let Q' := map_mx (polyC \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC : mx (poly n T) 1 1 in
      fun_of_matrix p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    foldl (fun m mc => m) 0%C (list_of_poly pmp') in
  r.

(*Typeclasses eauto := debug.*)  (* @Érik: merci, c'est super utile ! *)

(* Pour posdef_check_itv_F (un peu pénible ce type F en double). *)
Variable F' : Type.
Variables (feps feta : F') (is_finite : F' -> bool) (F2F' : F -> F').

Context `{!zero F', !one F', !opp F', !div F', !sqrt F'}.
Context `{!fun_of F' ord (mx F'), !row_class ord (mx F'), !store_class F' ord (mx F'), !dotmulB0_class F' ord (mx F')}.
Context `{!heq (mx F'), !transpose_class (mx F'), !leq F', !lt F'}.
Context `{!addup_class F', !mulup_class F', !divup_class F'}.
Context `{!nat2Fup_class F', !subdn_class F'}.
Context `{!fun_of T ord (mx T), !row_class ord (mx T), !store_class T ord (mx T), !dotmulB0_class T ord (mx T)}.
Context `{!nat_of_class ord s}.

Definition soscheck (p : poly n T)
                    (z : mx (monom n) s 1) (Q : mx F s s) : bool :=
  let r :=
    let p' :=
      let zp := map_mx polyX z in
      let Q' := map_mx (polyC \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC : mx (poly n T) 1 1 in
      fun_of_matrix p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    foldl (fun m mc => max m (max mc.2 (-mc.2)%C)) 0%C (list_of_poly pmp') in
  posdef_check_itv_F feps feta is_finite F2F' Q (T2F r).

End generic_soscheck.

(*
Module S := FSetAVL.Make MultinomOrd.

Definition check_base (p : effmpoly bigQ) (z : seq seqmultinom) : bool :=
  let s :=
      foldl
        (fun acc i => foldl (fun acc j => S.add (mnm_add_seq i j) acc) acc z)
        S.empty z in
  MProps.for_all (fun m _ => S.mem m s) p.

Definition ZZtoQ (m : bigZ) (e : bigZ) :=
  match m,e with
  | BigZ.Pos n, BigZ.Pos p => BigQ.Qz (BigZ.Pos (BigN.shiftl n p))
  | BigZ.Neg n, BigZ.Pos p => BigQ.Qz (BigZ.Neg (BigN.shiftl n p))
  | _, BigZ.Neg p =>
  (*
  BigQ.mul (BigQ.Qz m) (BigQ.inv (BigQ.Qz (BigZ.Pos (BigN.shiftl p 1%bigN))))
  *)
  BigQ.Qq m (BigN.shiftl 1%bigN p)
  end.

Lemma ZZtoQ_correct :
( forall m e,
  BigQ.to_Q (ZZtoQ m e) =
  (Qmake (BigZ.to_Z m) 1) * (Qpower (Qmake 2 1) (BigZ.to_Z e)) )%Q.
Proof.
Admitted.

Definition F2BigQ (q : F.type) : bigQ :=
  match q with
  | Interval_specific_ops.Float m e => ZZtoQ m e
  | Interval_specific_ops.Fnan => 0%bigQ
  end.

Definition soscheck (p : effmpoly bigQ) (zQ : seq seqmultinom * seq (seq F.type)) : bool :=
  let z := zQ.1 in
  let Q := zQ.2 in
  let n := size z in
  check_base p z &&
  let r :=
      let p' :=
          effmpoly_of_list (flatten (zipwith (fun mi Qi => zipwith (fun mj Qij => (mnm_add_seq mi mj, F2BigQ Qij)) z Qi) z Q)) in
      let pmp' := @mpoly_sub_eff _ BigQ.opp BigQ.sub p p' in
      M.fold (fun _ e acc => BigQ.max acc (BigQ.max e (- e)%bigQ)) pmp' 0%bigQ in
  test_posdef_check_itv zQ.2 r.

(* TODO: Move to misc *)
Local Coercion RMicromega.IQR : Q >-> R.
Local Coercion BigQ.to_Q : bigQ >-> Q.

Definition R_of_effmpoly (p : effmpoly bigQ) : effmpoly R :=
  M.map (fun q : bigQ => q : R) p.

Lemma soscheck_correct p zQ :
  let n := size zQ.1 in
  soscheck p zQ ->
  forall x,
  (0 <= (mpoly_of_effmpoly_val n (R_of_effmpoly p)).@[x])%R.
Admitted.
*)
