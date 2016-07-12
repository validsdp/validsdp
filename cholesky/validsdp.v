Require Import Reals Flocq.Core.Fcore_Raux QArith BigZ BigQ Psatz FSetAVL.
From Flocq Require Import Fcore.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements seqmatrix.
From SsrMultinomials Require Import mpoly (* freeg *).
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
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

Class sempty_class setT := sempty : setT.
Class sadd_class T setT := sadd : T -> setT -> setT.
Class smem_class T setT := smem : T -> setT -> bool.

Class mul_monom monom := mul_monom_op : monom -> monom -> monom.

Class list_of_poly_class T monom polyT := list_of_poly :
  polyT -> seq (monom * T).

Class polyC_class T polyT := polyC : T -> polyT.

Class polyX_class monom polyT := polyX : monom -> polyT.

Class poly_sub polyT := poly_sub_op : polyT -> polyT -> polyT.

(* TODO: regarder si pas déjà dans Coq_EAL *)
Class max_class T := max : T -> T -> T.

(** ** Part 1: Generic programs *)

Section generic_soscheck.

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context {monom : Type} {polyT : Type}.
Context `{!mul_monom monom, !list_of_poly_class T monom polyT}.
Context `{!polyC_class T polyT, !polyX_class monom polyT, !poly_sub polyT}.

Context {set : Type}.
Context `{!sempty_class set, !sadd_class monom set, !smem_class monom set}.

Context `{!zero T, !opp T, !max_class T}.
Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!fun_of monom ord (mx monom)}.
Context `{!fun_of polyT ord (mx polyT)}.
Context {s : nat}.
Context `{!I0_class ord s, !I0_class ord 1, !succ0_class ord s}.

Definition check_base (p : polyT) (z : mx monom s 1) : bool :=
  let sm :=
    iteri_ord s
      (fun i =>
         iteri_ord s
           (fun j => sadd (mul_monom_op (fun_of_matrix z i I0)
                                        (fun_of_matrix z j I0))))
      sempty in
  all (fun mc => smem mc.1 sm) (list_of_poly p).

Context `{!map_mx_class mx}.
Context `{!transpose_class (mx polyT)}.
(* Multiplication of matrices of polynomials. *)
Context `{!hmul (mx polyT)}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FI fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Context `{!fun_of F ord (mx F), !row_class ord (mx F), !store_class F ord (mx F), !dotmulB0_class F ord (mx F)}.
Context `{!heq (mx F), !transpose_class (mx F)}.
Context `{!nat_of_class ord s}.

Definition soscheck (p : polyT) (z : mx monom s 1) (Q : mx F s s) : bool :=
  let r :=
    let p' :=
      let zp := map_mx polyX z in
      let Q' := map_mx (polyC \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC in
      fun_of_matrix p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    foldl (fun m mc => max m (max mc.2 (-mc.2)%C)) 0%C (list_of_poly pmp') in
  posdef_check_itv (@fieps fs) (@fieta fs) (@is_finite fs) Q (T2F r).

End generic_soscheck.

Module S := FSetAVL.Make MultinomOrd.

Section eff_soscheck.

(** *** 1.2 Generic defs for seqmx and effmpoly *)

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context `{!one T, !opp T, !add T, !sub T, !mul T}.

Let monom := seqmultinom.

Let polyT := effmpoly T.

Global Instance mul_monom_eff : mul_monom monom := mnm_add_seq.

Global Instance list_of_poly_eff : list_of_poly_class T monom polyT :=
  @list_of_effmpoly T.

Global Instance polyC_eff : polyC_class T polyT := @mpolyC_eff _ n.

Global Instance polyX_eff : polyX_class monom polyT := mpolyX_eff.

Global Instance poly_sub_eff : poly_sub polyT := mpoly_sub_eff.

Let set := S.t.

Global Instance sempty_eff : sempty_class set := S.empty.

Global Instance sadd_eff : sadd_class monom set := S.add.

Global Instance smem_eff : smem_class monom set := S.mem.

Context `{!zero T, !max_class T}.

Let ord := ord_instN.

Let mx := seqmatrix'.

Context {s : nat}.

(* @Érik: global? *)
Global Instance fun_of_seqmx_monom : fun_of monom ord (mx monom) :=
  @fun_of_seqmx _ [::].

Definition check_base_eff : polyT -> mx monom s.+1 1 -> bool :=
  check_base (I0_class0:=I0_instN).  (* aucune idée de pourquoi celle ci n'est pas inférée *)

Context {fs : Float_round_up_infnan_spec}.
Let F := FI fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

(* @Érik: global? *)
Global Instance fun_of_seqmx_polyT : fun_of polyT ord (mx polyT) :=
  @fun_of_seqmx _ mp0_eff.

(* @Érik: global? *)
Global Instance mulseqmx_polyT : hmul (mx polyT) :=
  @mulseqmx _ mp0_eff mpoly_add_eff mpoly_mul_eff.

Definition soscheck_eff : polyT -> mx monom s.+1 1 -> mx F s.+1 s.+1 -> bool :=
  soscheck (map_mx_class0:=map_mx_seqmx) (I0_class0:=@I0_instN s)
    (F2T:=F2T) (T2F:=T2F).

End eff_soscheck.

About soscheck_eff.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_soscheck.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

(* Context {monom : nat -> Type} {poly : nat -> Type -> Type}. *)
(* monom: multinom, polyT: fun n => mpoly n T *)

Context {n : nat} {T : ringType}.

Let monom := 'X_{1..n}.

Let polyT := mpoly n T.

Global Instance mul_monom_ssr : mul_monom monom := mnm_add.

Global Instance list_of_poly_ssr : list_of_poly_class T monom polyT :=
  fun p => [seq (m, p@_m) |m <- msupp p].

Global Instance polyC_ssr : polyC_class T polyT := fun c => mpolyC n c.

Global Instance polyX_ssr : polyX_class monom polyT := fun m => mpolyX T m.

Global Instance poly_sub_ssr : poly_sub polyT := fun p q => p - q.

Let set := seq monom.

Global Instance sempty_ssr : sempty_class set := [::].

Global Instance sadd_ssr : sadd_class monom set := fun e s => e :: s.

Global Instance smem_ssr : smem_class monom set := fun e s => e \in s.

(* @Érik: should these two be global?
 * Should we even name them (current naming is bad)? *)
Local Instance zero_ssr : zero T := 0.
Local Instance opp_ssr : opp T := fun x => -x.

Context `{!max_class T}.

Let ord := ordinal.

Let mx := matrix.

Context {s : nat}.

Definition check_base_ssr : polyT -> 'cV[monom]_s.+1 -> bool := check_base.

Context {fs : Float_round_up_infnan_spec}.
Let F := FI fs.
Context {F2T : F -> T}.  (* exact conversion for finite values *)
Context {T2F : T -> F}.  (* overapproximation *)

Global Instance trmx_instPolyT_ssr : transpose_class (mx polyT) :=
  @matrix.trmx polyT.

Global Instance hmul_mxPolyT_ssr : hmul (mx polyT) := @mulmx _.

Definition soscheck_ssr : polyT -> 'cV[monom]_s.+1 -> 'M[F]_s.+1 -> bool :=
  soscheck (F2T:=F2T) (T2F:=T2F).

(** *** Proofs *)

Variable (T2R : T -> R).
Hypothesis T2R0 : T2R 0 = 0.
Hypothesis T2F_correct : forall x, is_finite (T2F x) -> T2R x <= FI2F (T2F x).
Hypothesis T2R_F2T : forall x, T2R (F2T x) = FI2F x.
Hypothesis max_l : forall x y, T2R x <= T2R (max x y).
Hypothesis max_r : forall x y, T2R y <= T2R (max x y).
(* probably more hypotheses needed, see during proof *)

(* seemingly missing in mpoly *)
Lemma map_mpolyC (R S : ringType) (f : R -> S) (Hf0 : f 0 = 0) n' c :
  map_mpoly f c%:MP_[n'] = (f c)%:MP_[n'].
Proof.
rewrite /map_mpoly /mmap msuppC.
case_eq (c == 0); [by move/eqP ->; rewrite big_nil Hf0 mpolyC0|].
move=> _; rewrite big_cons big_nil GRing.addr0 mmap1_id.
by rewrite mpolyX0 mcoeffC eqxx !GRing.mulr1 /=.
Qed.

Lemma soscheck_correct p z Q : soscheck_ssr p z Q ->
  forall x, (0 <= (map_mpoly T2R p).@[x])%R.
Proof.
rewrite /soscheck_ssr /soscheck /I0 /I0_ssr /fun_of_matrix /fun_of_ssr.
rewrite /hmul_op /hmul_mxPolyT_ssr /transpose_op /trmx_instPolyT_ssr.
rewrite /polyX /polyX_ssr /polyC /polyC_ssr /map_mx /map_mx_ssr.
set zp := matrix.map_mx _ z.
set Q' := matrix.map_mx _ _.
set p'm := _ (_ *m _) _ _.
set pmp' := poly_sub_op _ _.
set r := foldl _ _ _.
pose zpr := matrix.map_mx [eta mpolyX real_ringType] z.
pose Q'r := matrix.map_mx (map_mpoly T2R) Q'.
pose map_mpolyC_R :=
  fun m : 'M_s.+1 => matrix.map_mx [eta mpolyC n (R:=real_ringType)] m.
have : exists E : 'M_s.+1,
  Mabs E <=m: matrix.const_mx (T2R r)
  /\ map_mpoly T2R p = (zpr^T *m (Q'r + map_mpolyC_R E) *m zpr) ord0 ord0.
{ admit.  (* c'est ici que tout se passe *) }
move=> [E [HE ->]] Hpcheck x.
set M := _ *m _.
replace (meval _ _)
with ((matrix.map_mx (meval x) M) ord0 ord0); [|by rewrite mxE].
replace R0 with ((@matrix.const_mx _ 1 1 R0) ord0 ord0); [|by rewrite mxE].
rewrite /M !map_mxM -map_trmx map_mxD; apply /Mle_scalar /posdef_semipos.
replace (matrix.map_mx _ (map_mpolyC_R E)) with E;
  [|by apply/matrixP => i j; rewrite !mxE /= mevalC].
replace (matrix.map_mx _ _) with (matrix.map_mx (T2R \o F2T) Q);
  [|by apply/matrixP => i j; rewrite !mxE /= (map_mpolyC _ _ _ T2R0) mevalC].
apply (posdef_check_itv_correct Hpcheck).
apply Mle_trans with (Mabs E).
{ by right; rewrite !mxE /=; f_equal; rewrite T2R_F2T GRing.addrC GRing.addKr. }
apply (Mle_trans HE) => i j; rewrite !mxE.
by apply T2F_correct; move: Hpcheck; move/andP; elim.
Admitted.

End theory_soscheck.

(** ** Part 3: Parametricity *)

Section refinement_soscheck.

Variables (A : ringType) (C : Type) (rAC : A -> C -> Prop).
Context {n s : nat}.

Lemma param_check_base :
  param (ReffmpolyA rAC ==> RseqmxA (@Rseqmultinom n) ==> Logic.eq)
    (check_base_ssr (s:=s)) (check_base_eff (s:=s)).
Admitted.

Context `{!max_class A}.

Context `{!zero C, !one C, !opp C, !add C, !sub C, !mul C}.
Context `{!max_class C}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FI fs.
Context {F2A : F -> A}.  (* exact conversion for finite values *)
Context {A2F : A -> F}.  (* overapproximation *)
Context {F2C : F -> C}.  (* exact conversion for finite values *)
Context {C2F : C -> F}.  (* overapproximation *)
(* probably more hypotheses about these ones *)

(* Typeclasses eauto := debug. *)

Lemma param_soscheck :
  param (ReffmpolyA rAC ==> RseqmxA (@Rseqmultinom n) ==> Rseqmx ==> Logic.eq)
    (soscheck_ssr (s:=s) (F2T:=F2A) (T2F:=A2F))
    (soscheck_eff (n:=n) (s:=s) (F2T:=F2C) (T2F:=C2F)).
Admitted.

End refinement_soscheck.

(* Future definition of F2C *)
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

(* TODO: Move to misc *)
Local Coercion RMicromega.IQR : Q >-> R.
Local Coercion BigQ.to_Q : bigQ >-> Q.
