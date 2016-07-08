Require Import Reals Flocq.Core.Fcore_Raux QArith BigZ BigQ Psatz FSetAVL.
From Flocq Require Import Fcore.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements seqmatrix.
From SsrMultinomials Require Import mpoly (* freeg *).
Require Import Rstruct.
Require Import float_infnan_spec real_matrix coqinterval_infnan.
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
