Require Import ZArith.
From Flocq Require Import Fcore.
From Interval Require Import Interval_definitions Interval_xreal.
From Interval Require Import Interval_missing.
From CoqEAL.refinements Require Import hrel refinements param (*seqmx*) binint rational.
Require Import seqmx.
Require Import Reals Flocq.Core.Fcore_Raux QArith BigZ BigQ Psatz FSetAVL.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From mathcomp Require Import ssrnum ssrint rat div.
From SsrMultinomials Require Import mpoly (* freeg *).
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
Import Refinements.Op.
Require Import cholesky_prog multipoly coqinterval_infnan.
(* Require Import Quote. *)
From ValidSDP Require Import soswitness zulp.
Require Import seqmx_complements misc.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Q_scope with Qrat.

Local Open Scope R_scope.
(* Local Open Scope bigQ_scope. *)

Coercion bigQ2R : BigQ.t_ >-> R.

Inductive p_real_cst :=
| PConstR0
(* | PConstQz of bigZ *)
| PConstQq of bigZ & bigN
| PConstP2R of positive
| PConstRdiv of p_real_cst & positive
| PConstRopp of p_real_cst
| PConstRinv of positive.

Ltac get_positive t :=
  let rec aux t :=
    match t with
    | 1%Re => xH
    | 2%Re => constr:(xO xH)
    | 3%Re => constr:(xI xH)
    | (2 * ?v)%Re => let w := aux v in constr:(xO w)
    | (1 + 2 * ?v)%Re => let w := aux v in constr:(xI w)
    end in
  aux t.

Ltac get_real_cst t :=
  let rec aux t :=
    match t with
    (* | Z2R [?z]%bigZ *)
    | bigQ2R (?z # ?n)%bigQ => constr:(PConstQq z n)
    | R0 => PConstR0
    | Rdiv ?x ?y => let x := aux x in
                    let y := get_positive y in
                    constr:(PConstRdiv x y)
    | Ropp ?x => let x := aux x in
                 constr:(PConstRopp x)
    | Rinv ?x => let x := get_positive x in
                 constr:(PConstRinv x)
    | ?n => let p := get_positive n in constr:(PConstP2R p)
    | _ => false
    end in
  aux t.

Fixpoint interp_p_real_cst (p : p_real_cst) : R :=
  match p with
  | PConstR0 => R0
(* | PConstQz z => Z2R [z]%bigZ *)
  | PConstQq z n => bigQ2R (z # n)%bigQ
  | PConstP2R p => P2R p
  | PConstRdiv x y => Rdiv (interp_p_real_cst x) (P2R y)
  | PConstRopp x => Ropp (interp_p_real_cst x)
  | PConstRinv x => Rinv (P2R x)
  end.

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
  (* | Compose of abstr_poly * abstr_poly list *).

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
  end.

(* [list_add] was taken from CoqInterval *)
Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | Datatypes.nil        => constr:(n, Datatypes.cons a l)
    | Datatypes.cons a _   => constr:(n, l)
    | Datatypes.cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:(n, Datatypes.cons x l)
      end
    end in
  aux a l O.

Ltac get_poly t l :=
  let rec aux t l :=
    let aux_u o a :=
      match aux a l with
      | (?u, ?l) => constr:(o u, l)
      end in
    let aux_u' o a b :=
      match aux a l with
      | (?u, ?l) => constr:(o u b, l)
    end in
      let aux_b o a b :=
        match aux b l with
        | (?v, ?l) =>
          match aux a l with
          | (?u, ?l) => constr:(o u v, l)
          end
        end in
    match t with
    | Rplus ?a ?b => aux_b PAdd a b
    | Rminus ?a ?b => aux_b PSub a b
    | Ropp ?a => aux_u POpp a
    | Rmult ?a ?b => aux_b PMul a b
 (* | Rsqr ?a => aux (Rmult a a) l  *)
    | powerRZ ?a ?b =>
      match b with
      | Z.pos ?p => aux_u' PPowN a (N.pos p)
      | _ => fail 100 "Only constant, positive exponents are allowed."
      end
    | pow ?a ?n => aux_u' PPown a n
    | _ =>
      match get_real_cst t with
      | false =>
        match list_add t l with
        | (?n, ?l) => constr:(PVar n, l)
        end
      | ?c => constr:(PConst c, l)
      end
    end in
  aux t l.

(* (* Testcase *)

Axiom poly_correct : forall (x : p_abstr_poly) vm,
    (if x isn't PConst (PConstR0) then true else false) = true ->
    interp_p_abstr_poly vm x >= R0.

Lemma test_get_poly x y : (2/3 * x ^ 2 + x * y >= 0)%Re.
match goal with
| [ |- (?r >= 0)%Re ] => let p := get_poly r (@Datatypes.nil R) in
                      match p with
                      | (?p, ?vm) => apply (@poly_correct p vm)
                      end
end.
Abort.
*)

Inductive abstr_poly :=
  | Const of bigQ
  | Var of nat
  | Add of abstr_poly & abstr_poly
  | Sub of abstr_poly & abstr_poly
  | Mul of abstr_poly & abstr_poly
  | PowN of abstr_poly & binnat.N.

Fixpoint bigQ_of_p_real_cst (c : p_real_cst) : bigQ :=
  let aux := bigQ_of_p_real_cst in
  match c with
  | PConstR0 => 0%bigQ
  | PConstQq z n => (z # n)%bigQ
  | PConstP2R p => BigQ.of_Q (inject_Z (Z.pos p))
  | PConstRdiv x y => (aux x / BigQ.of_Q (inject_Z (Z.pos y)))%bigQ
  | PConstRopp x => (- aux x)%bigQ
  | PConstRinv x => (1 / BigQ.of_Q (inject_Z (Z.pos x)))%bigQ
  end.

Lemma bigQ_of_p_real_cst_correct c :
  bigQ2R (bigQ_of_p_real_cst c) = interp_p_real_cst c.
Proof.
have IQRp : forall p,
  Q2R [BigQ.Qz (BigZ.Pos (BigN.of_pos p))]%bigQ = P2R p.
{ by move=> p; rewrite /Q2R /= BigN.spec_of_pos /= Rsimpl. }
elim c.
{ by rewrite /bigQ2R /Q2R /= /Rdiv Rmult_0_l. }
{ done. }
{ exact: IQRp. }
{ move=> c' Hc' p; rewrite /= -Hc' /bigQ2R /Rdiv -IQRp -Q2R_inv.
  { by rewrite -Q2R_mult; apply Q2R_Qeq; rewrite BigQ.spec_div. }
  by rewrite /= BigN.spec_of_pos /Q2R /= Rsimpl; pos_P2R. }
{ move=> p Hp; rewrite /= -Hp /bigQ2R -Q2R_opp; apply Q2R_Qeq, BigQ.spec_opp. }
{ move=> p; rewrite /bigQ2R /interp_p_real_cst -IQRp -Q2R_inv.
  { apply Q2R_Qeq; rewrite -(Qmult_1_l (Qinv _)) -/([1]%bigQ).
    by rewrite -BigQ.spec_inv -BigQ.spec_mul. }
  by rewrite /= BigN.spec_of_pos /Q2R /= Rsimpl; pos_P2R. }
Qed.

Fixpoint abstr_poly_of_p_abstr_poly (p : p_abstr_poly) : abstr_poly :=
  let aux := abstr_poly_of_p_abstr_poly in
  match p with
  | PConst c => Const (bigQ_of_p_real_cst c)
  | PVar n => Var n
  | POpp x => Sub (Const 0%bigQ) (aux x)
  | PAdd x y => Add (aux x) (aux y)
  | PSub x y => Sub (aux x) (aux y)
  | PMul x y => Mul (aux x) (aux y)
  | PPowN x n => PowN (aux x) n
  | PPown x n => PowN (aux x) (N.of_nat n)
  end.

Fixpoint interp_abstr_poly (vm : seq R) (p : abstr_poly) {struct p} : R :=
  let aux := interp_abstr_poly in
  match p with
  | Const c => bigQ2R c
  | Add p q => Rplus (aux vm p) (aux vm q)
  | Sub p q => Rminus (aux vm p) (aux vm q)
  | Mul p q => Rmult (aux vm p) (aux vm q)
  | PowN p n => powerRZ (aux vm p) (Z.of_N n)
  | Var i => seq.nth R0 vm i
  end.

Lemma abstr_poly_of_p_abstr_poly_correct (vm : seq R) (p : p_abstr_poly) :
  interp_abstr_poly vm (abstr_poly_of_p_abstr_poly p) =
  interp_p_abstr_poly vm p.
Proof.
elim p.
{ apply bigQ_of_p_real_cst_correct. }
{ done. }
{ move=> p' /= ->.
  by rewrite /bigQ2R /Q2R Rsimpl /Rminus Rplus_0_l. }
{ by move=> ? /= -> ? /= ->. }
{ by move=> ? /= -> ? /= ->. }
{ by move=> ? /= -> ? /= ->. }
{ by move=> ? /= ->. }
by move=> ? /= -> ?; rewrite pow_powerRZ nat_N_Z.
Qed.

Definition interp_poly_ssr n (ap : abstr_poly) : {mpoly rat[n.+1]} :=
  let fix aux ap :=
    match ap with
    | Const c => (bigQ2rat c)%:MP_[n.+1]
    | Var i => 'X_(inord i)
    | Add p q => (aux p + aux q)%R
    | Sub p q => (aux p - aux q)%R
    | Mul p q => (aux p * aux q)%R
    | PowN p m => mpoly_exp (aux p) m
    end in
  aux ap.

Global Instance zero_bigQ : zero_of bigQ := 0%bigQ.
Global Instance one_bigQ : one_of bigQ := 1%bigQ.
Global Instance opp_bigQ : opp_of bigQ := BigQ.opp.
Global Instance add_bigQ : add_of bigQ := BigQ.add.
Global Instance sub_bigQ : sub_of bigQ := BigQ.sub.
Global Instance mul_bigQ : mul_of bigQ := BigQ.mul.
Global Instance eq_bigQ : eq_of bigQ := BigQ.eq_bool.

Definition interp_poly_eff n (ap : abstr_poly) : effmpoly bigQ :=
  let fix aux ap :=
    match ap with
    | Const c => @mpolyC_eff bigQ n.+1 c
    | Var i => @mpvar_eff bigQ n.+1 1%bigQ 1 (N.of_nat i) (* should be "i" *)
    | Add p q => mpoly_add_eff (aux p) (aux q)
    | Sub p q => mpoly_sub_eff (aux p) (aux q)
    | Mul p q => mpoly_mul_eff (aux p) (aux q)
    | PowN p m => mpoly_exp_eff (n := n.+1) (aux p) m
    end in
  aux ap.

Definition r_ratBigQ := fun_hrel bigQ2rat.

Fixpoint vars_ltn n (ap : abstr_poly) : bool :=
  match ap with
  | Const _ => true
  | Var i => (i < n)%N
  | Add p q | Sub p q | Mul p q => vars_ltn n p && vars_ltn n q
  | PowN p _ => vars_ltn n p
  end.

(* seemingly missing in mpoly *)
Lemma map_mpolyC (R S : ringType) (f : R -> S) (Hf0 : f 0%R = 0%R) n' c :
  map_mpoly f c%:MP_[n'] = (f c)%:MP_[n'].
Proof.
rewrite /map_mpoly /mmap msuppC.
case_eq (c == 0%R)%B; [by move/eqP ->; rewrite big_nil Hf0 mpolyC0|].
move=> _; rewrite big_cons big_nil GRing.addr0 mmap1_id.
by rewrite mpolyX0 mcoeffC eqxx !GRing.mulr1 /=.
Qed.

(* seemingly missing in mpoly *)
Lemma map_mpolyX (R S : ringType) (f : R -> S) n' (m : 'X_{1..n'}) :
  map_mpoly f 'X_[m] = (f 1 *: 'X_[m])%R.
Proof.
rewrite /map_mpoly /mmap msuppX big_cons big_nil GRing.addr0 mmap1_id.
by rewrite mul_mpolyC mcoeffX eqxx.
Qed.

Local Open Scope R_scope.

Lemma interp_abstr_poly_correct (l : seq R) (ap : abstr_poly) :
  let n := size l in (0 < n)%N -> vars_ltn n ap ->
  let n' := n.-1 in
  let p := map_mpoly rat2R (interp_poly_ssr n' ap) in
  interp_abstr_poly l ap = p.@[fun i : 'I_n'.+1 => nth R0 l i].
Proof.
move=> n Pn Hvars n'; set env := fun _ => _.
have Hn : n = n'.+1 by rewrite prednK.
elim: ap Hvars.
{ by move=> c _ /=; rewrite map_mpolyC ?GRing.raddf0 // mevalC bigQ2R_rat. }
{ move=> i /= Hi; rewrite map_mpolyX mevalZ mevalX.
  rewrite GRing.rmorph1 GRing.mul1r /env; f_equal.
  by rewrite inordK -?Hn. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq; rewrite (Hp Hlp) (Hq Hlq).
  by rewrite -[_+_]/(_.@[env] + _)%R !GRing.rmorphD. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq; rewrite (Hp Hlp) (Hq Hlq).
  by rewrite -[_-_]/(_.@[env] - _)%R !GRing.rmorphB. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq; rewrite (Hp Hlp) (Hq Hlq).
  by rewrite -[_*_]/(_.@[env] * _)%R !GRing.rmorphM. }
move=> p Hp m /= Hlp; rewrite (Hp Hlp).
rewrite -{1}[m]spec_NK /binnat.implem_N bin_of_natE nat_N_Z.
by rewrite -Interval_missing.pow_powerRZ misc.pow_rexp !GRing.rmorphX.
Qed.

(* vraiment nécessaire ? *)
Lemma interp_correct vm p :
  let n := size vm in
  let n' := n.-1 in
  let p' := abstr_poly_of_p_abstr_poly p in
  let p'' := map_mpoly rat2R (interp_poly_ssr n' p') in
  (0 < n)%N ->
  vars_ltn n p' ->
  interp_p_abstr_poly vm p = p''.@[fun i : 'I_n'.+1 => nth R0 vm i].
Proof.
move=> *; rewrite -interp_abstr_poly_correct //.
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

(* TODO: regarder si pas déjà dans Coq_EAL *)
Class max_of T := max_op : T -> T -> T.

Class map_mx2_of B := map_mx2_op :
  forall {T T'} {m n : nat}, (T -> T') -> B T m n -> B T' m n.

Global Instance max_bigQ : max_of bigQ := BigQ.max.

(** ** Part 1: Generic programs *)

Section generic_soscheck.

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context {monom : Type} {polyT : Type}.
Context `{!mul_monom_of monom, !list_of_poly_of T monom polyT}.
Context `{!polyC_of T polyT, !polyX_of monom polyT, !poly_sub_of polyT}.

Context {set : Type}.
Context `{!sempty_of set, !sadd_of monom set, !smem_of monom set}.

Context `{!zero_of T, !opp_of T, !max_of T}.
Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!fun_of_of monom ord (mx monom)}.
Context `{!fun_of_of polyT ord (mx polyT)}.
Context {s : nat}.
Context `{!I0_class ord s, !I0_class ord 1, !succ0_class ord s}.

Definition check_base (p : polyT) (z : mx monom s 1) : bool :=
  let sm :=
    iteri_ord s
      (fun i =>
         iteri_ord s
           (fun j => sadd (mul_monom_op (fun_of_op z i I0)
                                        (fun_of_op z j I0))))
      sempty in
  all (fun mc => smem mc.1 sm) (list_of_poly_op p).

Definition max_coeff (p : polyT) : T :=
  foldl (fun m mc => max_op m (max_op mc.2 (-mc.2)%C)) 0%C (list_of_poly_op p).

Context `{!trmx_of (mx polyT)}.
(* Multiplication of matrices of polynomials. *)
Context `{!hmul_of (mx polyT)}.

Context {fs : Float_round_up_infnan_spec}.
Let F := float_infnan_spec.FI fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Context `{!fun_of_of F ord (mx F), !row_of ord (mx F), !store_of F ord (mx F), !dotmulB0_of F ord (mx F)}.
Context `{!heq_of (mx F), !trmx_of (mx F)}.
Context `{!nat_of_class ord s}.

Context `{!map_mx2_of mx}.

Program Definition soscheck (p : polyT) (z : mx monom s 1) (Q : mx F s s) : bool :=
  check_base p z &&
  let r :=
    let p' :=
      let zp := map_mx2_op polyX_op z in
      let Q' := map_mx2_op (polyC_op \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC in
      (* TODO: profiling pour voir si nécessaire d'améliorer la ligne
       * ci dessus (facteur 40 en Caml, mais peut être du même ordre de
       * grandeur que la décomposition de Cholesky
       * (effectivement, sur d'assez gros exemples, ça semble être le cas)) *)
      fun_of_op p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    max_coeff pmp' in
  posdef_check_itv (@float_infnan_spec.fieps fs) (@float_infnan_spec.fieta fs)
                   (@is_finite fs) Q (T2F r).

(* Why Coq doesn't complain [!one_of T] is not in the context ? *)

End generic_soscheck.

Module S := FSetAVL.Make MultinomOrd.

Section eff_soscheck.

(** *** 1.2 Generic defs for seqmx and effmpoly *)

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

Context `{!max_of T}.

Let ord := ord_instN.

Let mx := @hseqmx.

Context {s : nat}.

(* @Érik: global? *)
Global Instance fun_of_seqmx_monom : fun_of_of monom ord (mx monom) :=
  @fun_of_seqmx _ [::].

Definition check_base_eff : polyT -> mx monom s.+1 1 -> bool :=
  check_base (I0_class0:=I0_instN).  (* aucune idée de pourquoi celle ci n'est pas inférée *)

Definition max_coeff_eff : polyT -> T := max_coeff.

Context {fs : Float_round_up_infnan_spec}.
Let F := float_infnan_spec.FI fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

(* @Érik: global? *)
Global Instance fun_of_seqmx_polyT : fun_of_of polyT ord (mx polyT) :=
  @fun_of_seqmx _ mp0_eff.

(* @Érik: global? *)
Global Instance mulseqmx_polyT : hmul_of (mx polyT) :=
  @mul_seqmx _ mp0_eff mpoly_add_eff mpoly_mul_eff.

(* Workaround: *)
Global Instance map_seqmx' : map_mx2_of mx := fun T T' _ _ => map_seqmx (B := T').

Definition soscheck_eff : polyT -> mx monom s.+1 1 -> mx F s.+1 s.+1 -> bool :=
  soscheck (F2T:=F2T) (T2F:=T2F).

End eff_soscheck.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_soscheck.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

(* Context {monom : nat -> Type} {poly : nat -> Type -> Type}. *)
(* monom: multinom, polyT: fun n => mpoly n T *)

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

(* @Érik: should these two be global?
 * Should we even name them (current naming is bad)? *)
Local Instance zero_ssr : zero_of T := 0%R.
Local Instance opp_ssr : opp_of T := fun x => (-x)%R.

Context `{!max_of T}.

Let ord := ordinal.

Let mx := matrix.

Context {s : nat}.

Definition check_base_ssr : polyT -> 'cV[monom]_s.+1 -> bool := check_base.

Definition max_coeff_ssr : polyT -> T := max_coeff.

Context {fs : Float_round_up_infnan_spec}.
Let F := float_infnan_spec.FI fs.
Context {F2T : F -> T}.  (* exact conversion for finite values *)
Context {T2F : T -> F}.  (* overapproximation *)

Global Instance trmx_instPolyT_ssr : trmx_of (mx polyT) :=
  @matrix.trmx polyT.

Global Instance hmul_mxPolyT_ssr : hmul_of (mx polyT) := @mulmx _.

Global Instance map_mx_ssr : map_mx2_of mx := fun T T' m n f => @map_mx T T' f m n.

Definition soscheck_ssr : polyT -> 'cV[monom]_s.+1 -> 'M[F]_s.+1 -> bool :=
  soscheck (F2T:=F2T) (T2F:=T2F).

(** *** Proofs *)

Variable (T2R : T -> R).
Hypothesis T2R_additive : additive T2R.
Canonical T2R_additive_struct := Additive T2R_additive.
Hypothesis T2F_correct : forall x, is_finite (T2F x) -> T2R x <= float_infnan_spec.FI2F (T2F x).
Hypothesis T2R_F2T : forall x, T2R (F2T x) = float_infnan_spec.FI2F x.
(* Note/Érik: we could replace [max_op] by [max], assuming [leq_of] *)
Hypothesis max_l : forall x y : T, T2R x <= T2R (max_op x y).
Hypothesis max_r : forall x y, T2R y <= T2R (max_op x y).

Lemma check_base_correct (p : polyT) (z : 'cV_s.+1) : check_base p z ->
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
have Hmax : forall x y, Rabs (T2R x) <= T2R (max_op y (max_op x (- x)%C)).
{ move=> x y; apply Rabs_le; split.
  { rewrite -(Ropp_involutive (T2R x)); apply Ropp_le_contravar.
    change (- (T2R x))%Re with (- (T2R x))%Ri.
    rewrite -GRing.raddfN /=.
    apply (Rle_trans _ _ _ (max_r _ _) (max_r _ _)). }
  apply (Rle_trans _ _ _ (max_l _ _) (max_r _ _)). }
rewrite -(path.mem_sort mnmc_le) /list_of_poly_op.
elim: (path.sort _) 0%C=> [//|h t IH] z; move/orP; elim.
{ move/eqP-> => /=; set f := fun _ => _; set l := map _ _.
  move: (Hmax p@_h z); set z' := max_op z _; generalize z'.
  elim l => /= [//|h' l' IH' z'' Hz'']; apply IH'.
  apply (Rle_trans _ _ _ Hz''), max_l. }
by move=> Ht; apply IH.
Qed.

Require Import bigop_tactics.

Lemma soscheck_correct p z Q : soscheck_ssr p z Q ->
  forall x, 0%R <= (map_mpoly T2R p).@[x].
Proof.
rewrite /soscheck_ssr /soscheck /fun_of_op /fun_of_ssr /map_mx2_op /map_mx_ssr.
set zp := matrix.map_mx _ z.
set Q' := matrix.map_mx _ _.
set p' := _ (_ *m _) _ _.
set pmp' := poly_sub_op _ _.
set r := max_coeff _ .
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
    by rewrite !mxE mpolyCD (map_mpolyC (GRing.raddf0 _)). }
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
      rewrite -unfoldR; change R0 with (INR 0); apply lt_INR.
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
apply /Mle_scalar /posdef_semipos.
replace (matrix.map_mx _ (map_mpolyC_R E)) with E;
  [|by apply/matrixP => i j; rewrite !mxE /= mevalC].
replace (matrix.map_mx _ _) with (matrix.map_mx (T2R \o F2T) Q);
  [|by apply/matrixP => i j;
    rewrite !mxE /= (map_mpolyC (GRing.raddf0 _)) mevalC].
apply (posdef_check_itv_correct Hpcheck).
apply Mle_trans with (Mabs E).
{ by right; rewrite !mxE /=; f_equal; rewrite T2R_F2T GRing.addrC GRing.addKr. }
apply (Mle_trans HE) => i j; rewrite !mxE.
by apply T2F_correct; move: Hpcheck; move/andP; elim.
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
*)

Let fs := coqinterval_infnan.coqinterval_round_up_infnan.

Definition int2Z (n : int) : BinNums.Z :=
  match n with
  | Posz O => Z0
  | Posz n => Z.pos (Pos.of_nat n)
  | Negz n => Z.neg (Pos.of_nat n.+1)
  end.

Lemma Z2R_int2Z_nat (n : nat) : Z2R (int2Z n) = n%:~R.
Proof.
elim: n => [//|n IHn].
rewrite -addn1 PoszD intrD -{}IHn /=.
rewrite addn1 -addn1 /= P2R_INR Nat2Pos.id ?addn1 // -addn1.
set zn := match n with O => Z0 | _ => Z.pos (Pos.of_nat n) end.
suff->: zn = Z.of_nat n by rewrite -INR_Z2R plus_INR.
clear; rewrite {}/zn /Z.of_nat.
case: n => // n.
by rewrite Pos.of_nat_succ.
Qed.

Lemma Z2R_int2Z n : Z2R (int2Z n) = n%:~R.
Proof.
elim/int_rec: n =>// n IHn.
{ exact: Z2R_int2Z_nat. }
by clear IHn; rewrite mulrNz /= -Z2R_int2Z_nat.
Qed.

Delimit Scope Z_scope with coq_Z. (* should be unnecessary *)
 
Lemma int2Z_le m n : (int2Z m <=? int2Z n)%coq_Z = (m <= n)%Ri.
Proof.
rewrite -(ler_int real_numDomainType) -!Z2R_int2Z; apply/idP/idP.
{ by move/Z.leb_le/Z2R_le/RleP. }
by move/RleP/le_Z2R/Z.leb_le.
Qed.

Definition rat2bigQ (q : rat) : bigQ :=
  let n := BigZ.of_Z (int2Z (numq q)) in
  let d := BigN.N_of_Z (int2Z (denq q)) in
  (n # d)%bigQ.

Definition bigQ2F' := snd \o bigQ2F.
Definition bigQ2FI := F2FI \o bigQ2F'.
Definition rat2FI := bigQ2FI \o rat2bigQ.

Definition FI2bigQ := F2bigQ \o FI_val.
Definition FI2rat := bigQ2rat \o FI2bigQ.

(* Erik: [toR] could be proved extenstionnaly equal to [F_val \o FI2F]. *)

Lemma F2FI_valE f :
  mantissa_bounded f ->
  F.toX (F2FI_val f) = F.toX f.
Proof.
case: f => [//|m e].
by move/signif_digits_correct; rewrite /F2FI_val =>->.
Qed.

Lemma BigZ_Pos_NofZ n : [BigZ.Pos (BigN.N_of_Z n)]%bigZ = if (0 <=? n)%coq_Z then n else Z0.
Proof. by rewrite -[RHS](BigZ.spec_of_Z); case: n. Qed.

Lemma rat2FI_correct r :
  @is_finite fs (rat2FI r) ->
  rat2R r <= F_val (@float_infnan_spec.FI2F fs (rat2FI r)).
Proof.
move => Hr; have := real_FtoX_toR _ Hr.
rewrite /rat2FI /bigQ2F /bigQ2FI /=.
rewrite F2FI_correct //=.
rewrite /rat2bigQ /ratr.
set n := numq r; set d := denq r.
Opaque F.div.
rewrite /bigQ2F' /=.
Transparent F.div.
rewrite F2FI_valE; last exact: fidiv_proof.
rewrite !F.div_correct /Xround.
case E: Xdiv =>[//|x] /= _.
set xq := (n%:~R / d%:~R)%Ri.
suff ->: x = xq.
{ rewrite /round /=.
  by have [_ [Hxq _]] := round_UP_pt radix2 (FLX_exp 53) xq. }
rewrite {}/xq.
move: E; set fn := Float _ _; set fd := Float _ _.
rewrite (@real_FtoX_toR fn erefl) (@real_FtoX_toR fd erefl) /=.
rewrite /Xdiv'.
case: is_zero_spec =>// H0 [] <-.
rewrite !toR_Float BigZ.spec_of_Z !Z2R_int2Z BigZ_Pos_NofZ ifT; last first.
by change Z0 with (int2Z 0%Ri); rewrite int2Z_le denq_ge0.
rewrite Z2R_int2Z !Rsimpl unfoldR' //.
by apply/eqP/negbT; rewrite intr_eq0 denq_eq0.
Qed.

(* TODO: move *)
Lemma Q2R_0 : Q2R 0%Qrat = 0%Re.
Proof. by rewrite /Q2R /= /Rdiv Rmult_0_l. Qed.

Lemma rat2R_FI2rat :
 forall x0 : float_infnan_spec.FI fs, rat2R (FI2rat x0) = F_val (FI2F x0).
Proof.
move=> x; rewrite -bigQ2R_rat /bigQ2R.
case: x => -[|m e] H /=.
{ case: H => H.
  by rewrite Q2R_0.
  by case: H => r H1 H2 /=; rewrite /F.toX /= in H1 *. }
rewrite /FI2bigQ /=.
case: H => H /=; first by rewrite real_FtoX_toR in H.
case: H => r H1 H2 /=.
rewrite real_FtoX_toR // in H1.
case: H1 =><-.
rewrite toR_Float.
rewrite -/(toR (Float m e)).
rewrite /Interval_xreal.proj_val.
by rewrite bigZZ2Q_correct.
Qed.

Instance : refines (eq ==> r_ratBigQ) FI2rat FI2bigQ.
Proof. by rewrite refinesE => ? ? ->. Qed.

Definition id1 {T} (x : T) := x.

Definition r_QbigQ := fun_hrel BigQ.to_Q.

Instance : refines (eq ==>  BigQ.eq) (rat2bigQ \o bigQ2rat) id.
Admitted.

Definition eqF (a b : F.type) := F.toX a = F.toX b.
Definition eqFI (a b : FI) := F.toX a = F.toX b.

Lemma FI_val_inj : injective FI_val.
move=> x y Hxy.
case: x Hxy => [vx px] Hxy.
case: y Hxy => [vy py] Hxy.
simpl in Hxy.
move: py; rewrite -Hxy => py; f_equal; clear Hxy vy.
case E: vx px py => [|m e] px py.
admit.
(* move/(ifft2 (FLX53_correct m e)) in px. *)
admit.
Admitted. (* proof irrelevance ?! *)

Instance : refines (eqF ==> eqFI) F2FI F2FI.
rewrite refinesE => f f' ref_f.
rewrite /F2FI /eqFI /=.
rewrite /eqF in ref_f.
rewrite !F2FI_valE //. (* lemma for NaN case missing *)
Admitted.

Instance : refines (BigQ.eq ==> eqF) bigQ2F' bigQ2F'. (* morphism! *)
Admitted.

Instance : refines (r_ratBigQ ==> eqFI) rat2FI bigQ2FI.
Proof.
rewrite /rat2FI .
rewrite refinesE => x x' ref_x /=.
rewrite -[x']/(id1 x') -ref_x.
rewrite -[bigQ2FI _]/(bigQ2FI ((rat2bigQ \o bigQ2rat) x')).
apply refinesP.
refines_apply1.
rewrite /bigQ2FI.
rewrite refinesE => y y' ref_y /=.
apply refinesP.
refines_apply1.
by refines_apply1; rewrite refinesE.
Qed.

(*
Instance : refines (r_ratBigQ ==> fun_hrel BigQ.to_Q) rat2bigQ 

Lemma 
rewrite /rat2FI /bigQ2FI.
do ![red in ref_x].
rewrite -ref_x; simpl.
rewrite /bigQ2F' /bigQ2F.
Opaque F.div.
simpl. case: x' {ref_x} =>//.
Transparent F.div.
 *)

Lemma max_l : forall x0 y0 : rat_comRing, rat2R x0 <= rat2R (Num.max x0 y0).
Proof.
Admitted.  (* Erik *)

Lemma max_r : forall x0 y0 : rat_comRing, rat2R y0 <= rat2R (Num.max x0 y0).
Proof.
Admitted.  (* Erik *)

(** ** Part 3: Parametricity *)

Section refinement_soscheck.

Variables (A : comRingType) (C : Type) (rAC : A -> C -> Type) (C2A : C -> A).
Hypothesis C2A_correct : forall c, rAC (C2A c) c.
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

Instance refines_check_base :
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
    { by apply refinesC_list_of_mpoly_eff. }
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
    refines_apply_tc; refines_apply_tc. }
  by move/S.mem_2=> H; apply S.mem_1, S.add_2. }
move/S.mem_2.
set mm := mul_monom_op _ _; case Em' : (m' == mm).
{ case eqP=>//= Hm HIn; apply S.mem_1.
  move: HIn; apply S.add_3=>_; apply /Hm /eqP.
  rewrite /is_true -Em'; apply Rseqmultinom_eq.
  { by rewrite refinesE. }
  refines_apply_tc; refines_apply_tc. }
move/S.add_3=>H; apply/orP; right; apply S.mem_1, H.
by move/mnmc_eq_seqP; rewrite eq_sym Em'.
Qed.

Context `{!max_of A}.
Context `{!max_of C}.
Context `{!refines (rAC ==> rAC ==> rAC) max_op max_op}.

(* TODO: move in CoqEAL_complement? *)
Global Instance refines_foldl
  (T T' : Type) (rT : T -> T' -> Type) (R R' : Type) (rR : R -> R' -> Type) :
  refines ((rR ==> rT ==> rR) ==> rR ==> list_R rT ==> rR)
    (@foldl T R) (@foldl T' R').
Proof.
rewrite refinesE=> f f' rf z z' rz s' s'' rs'.
elim: s' s'' rs' z z' rz=> [|h t IH] s'' rs' z z' rz.
{ case: s'' rs'=> [//|h' t'] rs'; inversion rs'. }
case: s'' rs'=> [|h' t'] rs' /=; [by inversion rs'|].
apply IH; [by inversion rs'|].
by apply refinesP; refines_apply_tc; rewrite refinesE; inversion rs'.
Qed.

Instance param_max_coeff :
  refines (ReffmpolyC (n:=n) rAC ==> rAC) max_coeff_ssr max_coeff_eff.
Proof.
rewrite refinesE=> p p' rp.
rewrite /max_coeff_ssr /max_coeff_eff /max_coeff.
apply refinesP; refines_apply1.
refines_apply1.
refines_apply1.
apply refines_abstr2 => m m' rm mc mc' rmc.
refines_apply1.
Qed.

Context {fs : Float_round_up_infnan_spec}.
Let F := float_infnan_spec.FI fs.
Context {F2A : F -> A}.  (* exact conversion for finite values *)
Context {A2F : A -> F}.  (* overapproximation *)
Context {F2C : F -> C}.  (* exact conversion for finite values *)
Context {C2F : C -> F}.  (* overapproximation *)
Context `{!refines (eq ==> rAC) F2A F2C}.
Context `{!refines (rAC ==> eq) A2F C2F}.
(*
Variable eqF : F -> F -> Prop. (* TODO: rather use [Type] *)
Context `{!refines (rAC ==> eqF) A2F C2F}.
 *)

(* TODO: move *)
Lemma list_Rxx T (rT : T -> T -> Type) l : (forall x, rT x x) -> list_R rT l l.
Proof.
move=> Hr; elim l=> [|h t IH]; [by apply list_R_nil_R|].
by apply list_R_cons_R.
Qed.

(* !! Fail Ltac fixme tac := tac || idtac. *)

(*****************************************************************************)
(** [head]: a tiny tactic suggested by JGross on Coq-Club *)
Ltac head x :=
  match x with
  | ?f _ => head f
  | _ => constr:x
  end.

(** Helper tactic that will fail if both functions [A] and [C]
    end with the same term *)
Ltac fail_heuristic :=
  match goal with
  | [ |- refines ?R (?A ?B) (?C ?D) ] =>
    match B with
    | D => fail 2
    | _ => idtac
    end
  | _ => idtac
  end.

(** Variant of [repeat] that only deals with the first subgoals *)
Ltac repeat1 tac :=
  tac; first try repeat1 tac.

(** Helper tactic that applies [refines_apply] several times and tries
to trigger [tc] at a relevant time (based on [fail_heuristic]) *)
Ltac refines_apply_tc0 :=
  (repeat1 ltac:(eapply refines_apply; fail_heuristic));
  first (try by tc).
  (* (try by rewrite refinesE); (try by tc). *)

(** Shortcut when the goal does not start with [refines] *)
Ltac refinesP_apply_tc0 :=
  eapply refinesP; refines_apply_tc0.
(*****************************************************************************)

Lemma param_soscheck :
  refines (ReffmpolyC rAC ==> RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (*(nat_R_S_R nat_R_O_R)*) (nat_Rxx 1) ==> Rseqmx (nat_Rxx s.+1) (nat_Rxx s.+1) ==> eq)
    (soscheck_ssr (s:=s) (F2T:=F2A) (T2F:=A2F))
    (soscheck_eff (n:=n) (s:=s) (F2T:=F2C) (T2F:=C2F)).
Proof.
rewrite refinesE=> p p' rp z z' rz Q Q' rQ.
rewrite /soscheck_ssr /soscheck_eff /soscheck.
apply f_equal2; [by apply refinesP; refines_apply_tc|].
eapply refinesP.
(* refines_apply_tc. *)
refines_apply_tc0.
(* refines_apply_tc. *)
refines_apply_tc0.
(* refines_apply_tc. *)
(* refines_apply_tc0. *)
eapply refines_apply. by tc.
eapply refines_apply. eapply refines_apply. by tc.
by tc.
eapply refines_apply. eapply refines_apply. eapply refines_apply. by tc.
eapply refines_apply; [eapply refines_apply|].
{ apply refine_mul_seqmx; [by tc| |].
  { apply ReffmpolyC_mpoly_add_eff; by tc. }
  apply ReffmpolyC_mpoly_mul_eff; by tc. }
eapply refines_apply; [eapply refines_apply|].
{ apply refine_mul_seqmx; [by tc| |].
  { apply ReffmpolyC_mpoly_add_eff; by tc. }
  apply ReffmpolyC_mpoly_mul_eff; by tc. }
{ refines_apply_tc. }
{ refines_apply_tc.
  { apply refines_abstr=> c c' rc /=; refines_apply_tc. }
  rewrite refinesE; exists Q'; split=>//.
  by apply list_Rxx=> x; apply list_Rxx. }
refines_apply_tc.
by rewrite refinesE.
by rewrite refinesE.
Qed.

End refinement_soscheck.

Section refinement_interp_poly.

Global Instance param_ratBigQ_zero : refines r_ratBigQ 0%R 0%C.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_one : refines r_ratBigQ 1%R 1%C.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_opp : refines (r_ratBigQ ==> r_ratBigQ) -%R -%C.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_add :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) +%R +%C.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_sub :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) (fun x y => x - y)%R sub_op.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_mul :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) *%R *%C.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_eq :
  refines (r_ratBigQ ==> r_ratBigQ ==> eq) eqtype.eq_op eq_op.
Admitted.  (* Erik *)

Global Instance param_ratBigQ_max :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) Num.max max_op.
Admitted.  (* Erik *)

Lemma param_interp_poly n ap : vars_ltn n.+1 ap ->
  refines (ReffmpolyC r_ratBigQ) (interp_poly_ssr n ap) (interp_poly_eff n ap).
Proof.
elim: ap.
{ move=> c /= _; eapply refines_apply; [eapply ReffmpolyC_mpolyC_eff; try by tc|].
  by rewrite refinesE. }
{ move=> i /= Hn.
  rewrite -(GRing.scale1r (mpolyX _ _)) -/(mpvar 1 1 (inord i)).
  eapply refines_apply; first eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpvar_eff. }
  { tc. }
  { by rewrite refinesE. }
  by rewrite refinesE /Rord0 -bin_of_natE bin_of_natK inordK. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  rewrite /GRing.add /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_add_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  set p' := _ _ p; set q' := _ _ q.
  rewrite -[(_ - _)%R]/(mpoly_sub p' q').
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_sub_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  rewrite /GRing.mul /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply ReffmpolyC_mpoly_mul_eff; tc. }
  { by apply Hp. }
  by apply Hq. }
move=> p Hp m /= Hlp.
eapply refines_apply; first eapply refines_apply.
{ by apply ReffmpolyC_mpoly_exp_eff; tc. }
{ by apply Hp. }
by rewrite refinesE.
Qed.

End refinement_interp_poly.

(** ** Part 4: The final tactic *)

(*
Definition notnil (vm : seq R) :=
  if vm is [::] then false else true.
 *)

Definition soscheck_eff_wrapup (vm : seq R) (pap : p_abstr_poly)
  (zQ : seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ))) :=
  let n := size vm in
  let n' := n.-1 in
  let ap := abstr_poly_of_p_abstr_poly pap in
  let bp := interp_poly_eff n' ap in
  let z := map (fun x => [:: x]) zQ.1 in
  let s := size zQ.1 in
  let Q := map (map F2FI) zQ.2 in
  [&& (n != 0%N),
   (all (fun m => size m == n) zQ.1),
   (s != 0%N),
   (size Q == s),
   (all (fun e => size e == s) Q),
   vars_ltn n ap &
   soscheck_eff
     (n := n) (s := s.-1)
     (fs := coqinterval_infnan.coqinterval_round_up_infnan)
     (F2T := F2bigQ \o (*FI2F*) coqinterval_infnan.FI_val)
     (T2F := F2FI \o bigQ2F')
     bp z Q].

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
apply refinesP, refines_multinom_of_seqmultinom_val.
move /all_nthP in H.
rewrite /za (nth_map [::]) //.
suff -> : j = 0%N by simpl; apply H.
move: Hj; rewrite /za (nth_map [::]) //=.
by rewrite ltnS leqn0; move/eqP->.
Qed.

Theorem soscheck_eff_wrapup_correct
  (vm : seq R) (pap : p_abstr_poly)
  (zQ : seq (seq BinNums.N) * seq (seq (s_float bigZ bigZ))) :
  soscheck_eff_wrapup vm pap zQ ->
  (0 <= interp_p_abstr_poly vm pap)%Re.
Proof.
rewrite /soscheck_eff_wrapup.
case/and5P => Hn Hz Hs HzQ /and3P [HzQ' Hltn Hsos].
pose n := size vm.
pose n' := n.-1.
set ap := abstr_poly_of_p_abstr_poly pap in Hsos *.
rewrite (_: size vm = n'.+1) in Hsos; last by rewrite prednK // lt0n Hn.
set bp := interp_poly_eff n' ap in Hsos *.
set za := (map (fun x => [:: x]) zQ.1) in Hsos *.
set Qa := map (map F2FI) zQ.2 in Hsos *.
pose s := (size zQ.1).-1.
pose zb := @spec_seqmx _ (@mnm0 n'.+1) _ (@multinom_of_seqmultinom_val n'.+1) s.+1 1 za.
pose Qb := @spec_seqmx _ (float_infnan_spec.FI0 fs) _ (id) s.+1 s.+1 Qa.
rewrite interp_correct; last by rewrite ?lt0n.
apply soscheck_correct with
  (1 := GRing.RMorphism.base (ratr_is_rmorphism _))
  (2 := rat2FI_correct)
  (3 := rat2R_FI2rat)
  (4 := max_l)
  (5 := max_r)
  (z := zb)
  (Q := Qb).
apply: (etrans (y := @soscheck_eff n'.+1 _
  zero_bigQ one_bigQ opp_bigQ add_bigQ sub_bigQ mul_bigQ eq_bigQ max_bigQ s fs
  (F2bigQ \o FI_val) (F2FI \o bigQ2F') bp za Qa)); last first.
{ by rewrite -/n' /n in Hsos; apply Hsos. }
apply refines_eq.
refines_apply1; first refines_apply1; first refines_apply1.
{ apply param_soscheck; tc. admit. }
{ by apply param_interp_poly; rewrite prednK ?lt0n. }
{ rewrite refinesE; eapply RseqmxC_spec_seqmx.
  { rewrite prednK ?lt0n // size_map eqxx /= /za.
    by apply/allP => x /mapP [y Hy] ->. }
  apply: listR_seqmultinom_map.
  by rewrite prednK ?lt0n // size_map eqxx /= /za. }
rewrite refinesE; eapply Rseqmx_spec_seqmx.
{ rewrite !size_map in HzQ.
  by rewrite prednK ?lt0n // !size_map HzQ. }
by rewrite lt0n.
Admitted.

Lemma Rle_minus_le r1 r2 : (0 <= r2 - r1)%Re -> (r1 <= r2)%Re.
Proof. now intros H0; apply Rge_le, Rminus_ge, Rle_ge. Qed.

Ltac do_sdp :=
  match goal with
  | [ |- (0 <= ?r)%Re ] =>
    match get_poly r (@Datatypes.nil R) with
      (?pap, ?vm) =>
      abstract (
        let n' := constr:((size vm).-1) in
        let ap := constr:(abstr_poly_of_p_abstr_poly pap) in
        let bp := constr:(interp_poly_eff n' ap) in
        let l := eval vm_compute in (M.elements bp) in
        let zQ := fresh "zQ" in
        soswitness of l as zQ;
        apply (@soscheck_eff_wrapup_correct vm pap zQ);
        (vm_cast_no_check (erefl true))
      )
    end
  | [ |- (?a <= ?b)%Re ] =>
    match a with
    | R0 => fail 100 "do_sdp fails to conclude."
    | _ => apply Rle_minus_le; do_sdp
    end
  | [ |- (?a >= ?b)%Re ] =>
    apply Rle_ge; do_sdp
  end.

Lemma test_do_sdp (x : R) : (2 * x >= 0)%Re.
(* Fail do_sdp.
" ** On entry to DGEMM parameter number  8 had an illegal value"
*)
Abort.

Lemma test_do_sdp (x y : R) : (2 / 3 * x ^ 2 + y ^ 2 >= 0)%Re.
Time do_sdp.
Time Qed.

Let sigma x0 x1 x2 : R := 6444365281246187/9007199254740992
         + 6312265263179769/576460752303423488 * x0
         + 6621776382116655/144115188075855872 * x1
         + -185496562805861/4503599627370496 * x2
         + 2416248187670441/4503599627370496 * x0^2
         + 5492430780988505/2305843009213693952 * x0 * x1
         + 5399350334336355/9007199254740992 * x1^2
         + 2775867384476511/72057594037927936 * x0 * x2
         + 6483681914198991/576460752303423488 * x1 * x2
         + 2659792549913679/4503599627370496 * x2^2
         + 2117156699109693/18014398509481984 * x0^3
         + 7324243373258689/72057594037927936 * x0^2 * x1
         + 5102009265014683/36028797018963968 * x0 * x1^2
         + 3559734688910025/36028797018963968 * x1^3
         + -5679254056549573/72057594037927936 * x0^2 * x2
         + -1770164427185237/36028797018963968 * x0 * x1 * x2
         + -2562963200769027/72057594037927936 * x1^2 * x2
         + 5769433788981365/36028797018963968 * x0 * x2^2
         + 7548762259869971/72057594037927936 * x1 * x2^2
         + -3538613895383109/72057594037927936 * x2^3
         + 1328789540631521/1125899906842624 * x0^4
         + -1855173755015043/9007199254740992 * x0^3 * x1
         + 2557767583672237/2251799813685248 * x0^2 * x1^2
         + -3462699602642395/9007199254740992 * x0 * x1^3
         + 7284044249240483/4503599627370496 * x1^4
         + 5263524722980771/36028797018963968 * x0^3 * x2
         + 144788199285567/18014398509481984 * x0^2 * x1 * x2
         + 1831673356681769/18014398509481984 * x0 * x1^2 * x2
         + 3484693834948841/36028797018963968 * x1^3 * x2
         + 4245018932645721/4503599627370496 * x0^2 * x2^2
         + -353526205012855/2251799813685248 * x0 * x1 * x2^2
         + 2324174681675653/2251799813685248 * x1^2 * x2^2
         + 3833151841760419/18014398509481984 * x0 * x2^3
         + 2941798320053223/72057594037927936 * x1 * x2^3
         + 1944708727800615/1125899906842624 * x2^4.

Let sigma1 x0 x1 x2 : R := 2238448784199197/4503599627370496
         + -7081956584605647/72057594037927936 * x0
         + -8095256989233253/288230376151711744 * x1
         + -5081574377800643/576460752303423488 * x2
         + 6018099001714223/18014398509481984 * x0^2
         + -30139342649847/1125899906842624 * x0 * x1
         + 8383324917719011/18014398509481984 * x1^2
         + -5487532759550775/288230376151711744 * x0 * x2
         + 5995950258377873/2305843009213693952 * x1 * x2
         + 8282785251080307/18014398509481984 * x2^2
         + -541778131690975/9007199254740992 * x0^3
         + -7290596405711811/576460752303423488 * x0^2 * x1
         + 3678758018224447/288230376151711744 * x0 * x1^2
         + 2513546562261607/288230376151711744 * x1^3
         + -717353212593637/36028797018963968 * x0^2 * x2
         + -6468496630616151/2305843009213693952 * x0 * x1 * x2
         + -4253168427456647/1152921504606846976 * x1^2 * x2
         + 2838432209735679/288230376151711744 * x0 * x2^2
         + 6398208700392841/576460752303423488 * x1 * x2^2
         + -3686553544012965/288230376151711744 * x2^3
         + 2832741523587629/4503599627370496 * x0^4
         + -820673162760289/18014398509481984 * x0^3 * x1
         + 36970644880265/70368744177664 * x0^2 * x1^2
         + -7091093352421131/144115188075855872 * x0 * x1^3
         + 222479320665527/281474976710656 * x1^4
         + -5920263192513033/288230376151711744 * x0^3 * x2
         + 86019135108721/4503599627370496 * x0^2 * x1 * x2
         + -3581037718886157/9223372036854775808 * x0 * x1^2 * x2
         + 541587445016049/36028797018963968 * x1^3 * x2
         + 2306452544747269/4503599627370496 * x0^2 * x2^2
         + -2885589273342991/72057594037927936 * x0 * x1 * x2^2
         + 4958911087255367/9007199254740992 * x1^2 * x2^2
         + 3714775807673741/576460752303423488 * x0 * x2^3
         + 4558527826146687/288230376151711744 * x1 * x2^3
         + 1751295812746853/2251799813685248 * x2^4
         + -8298022908743093/72057594037927936 * x0^5
         + -6995141011474289/72057594037927936 * x0^4 * x1
         + -906911613956325/9007199254740992 * x0^3 * x1^2
         + -4516111377899479/72057594037927936 * x0^2 * x1^3
         + -628700413433465/4503599627370496 * x0 * x1^4
         + -7914662856350805/144115188075855872 * x1^5
         + 2004387752491777/36028797018963968 * x0^4 * x2
         + 293684893385199/4503599627370496 * x0^3 * x1 * x2
         + 6643594431463215/288230376151711744 * x0^2 * x1^2 * x2
         + 5628209625281181/72057594037927936 * x0 * x1^3 * x2
         + 2038641075471393/144115188075855872 * x1^4 * x2
         + -311007039610149/2251799813685248 * x0^3 * x2^2
         + -8771543598063923/144115188075855872 * x0^2 * x1 * x2^2
         + -4640037065113525/36028797018963968 * x0 * x1^2 * x2^2
         + -4806722763336115/72057594037927936 * x1^3 * x2^2
         + 4375085894604395/144115188075855872 * x0^2 * x2^3
         + 4729553562804721/72057594037927936 * x0 * x1 * x2^3
         + 7939122053219573/576460752303423488 * x1^2 * x2^3
         + -7015044277992411/36028797018963968 * x0 * x2^4
         + -7613398074203915/72057594037927936 * x1 * x2^4
         + 1195520686271805/288230376151711744 * x2^5
         + 7154056313052153/144115188075855872 * x0^6
         + 4511872077787229/72057594037927936 * x0^5 * x1
         + 4655591819919163/72057594037927936 * x0^4 * x1^2
         + 4608448381322171/72057594037927936 * x0^3 * x1^3
         + 7553102807877403/144115188075855872 * x0^2 * x1^4
         + 1414408159002659/36028797018963968 * x0 * x1^5
         + 4147770253630557/288230376151711744 * x1^6
         + -4956636040779497/144115188075855872 * x0^5 * x2
         + -5861766429081453/144115188075855872 * x0^4 * x1 * x2
         + -5385581057667679/144115188075855872 * x0^3 * x1^2 * x2
         + -7214734708951869/144115188075855872 * x0^2 * x1^3 * x2
         + -1133047824711617/36028797018963968 * x0 * x1^4 * x2
         + -8929442930261787/1152921504606846976 * x1^5 * x2
         + 4625068670240235/72057594037927936 * x0^4 * x2^2
         + 8498398020785319/144115188075855872 * x0^3 * x1 * x2^2
         + 7796742623941989/144115188075855872 * x0^2 * x1^2 * x2^2
         + 6805340246135981/144115188075855872 * x0 * x1^3 * x2^2
         + 2487188163897569/144115188075855872 * x1^4 * x2^2
         + -2282908947939141/72057594037927936 * x0^3 * x2^3
         + -6389150420567317/144115188075855872 * x0^2 * x1 * x2^3
         + -1849144206170525/72057594037927936 * x0 * x1^2 * x2^3
         + -3362503951811703/576460752303423488 * x1^3 * x2^3
         + 8177541134906045/144115188075855872 * x0^2 * x2^4
         + 8078528346835259/144115188075855872 * x0 * x1 * x2^4
         + 1195325563618785/72057594037927936 * x1^2 * x2^4
         + -111546168491751/18014398509481984 * x0 * x2^5
         + -5156218193544123/2305843009213693952 * x1 * x2^5
         + 2931994166378865/2305843009213693952 * x2^6.

Let p x0 x1 x2 : R :=
     376932522065681012931/295147905179352825856
    + 8509962722502765/295147905179352825856 * x0
    + 4810786678983139/147573952589676412928 * x1
    + 8195275705635465/1180591620717411303424 * x2
    + -5286590888873701/4503599627370496 * x0^2
    + 3142771579399875/36028797018963968 * x0 * x1
    + -591108560874675/281474976710656 * x1^2
    + 1261458973270647/2251799813685248 * x0 * x2
    + 5929053759940775/72057594037927936 * x1 * x2
    + -1259727915632095/562949953421312 * x2^2
    + 1149275400895391/4503599627370496 * x0^3
    + 7285847311712275/18014398509481984 * x0^2 * x1
    + 8440266932050133/18014398509481984 * x0 * x1^2
    + 4371217067606495/36028797018963968 * x1^3
    + -458360830646393/1125899906842624 * x0^2 * x2
    + -2813070140505775/4503599627370496 * x0 * x1 * x2
    + -8737122075031031/72057594037927936 * x1^2 * x2
    + 3341105181056463/4503599627370496 * x0 * x2^2
    + 7431847970290251/18014398509481984 * x1 * x2^2
    + -7134326653543871/288230376151711744 * x2^3
    + -4419035466710003/36028797018963968 * x0^4
    + -3191026702181451/18014398509481984 * x0^3 * x1
    + -8852489850214139/72057594037927936 * x0^2 * x1^2
    + -2762344079633701/36028797018963968 * x0 * x1^3
    + -974190988861453/36028797018963968 * x1^4
    + 4592531851313069/36028797018963968 * x0^3 * x2
    + 1897745899402969/9007199254740992 * x0^2 * x1 * x2
    + 3929173054132589/36028797018963968 * x0 * x1^2 * x2
    + 5952875244748005/288230376151711744 * x1^3 * x2
    + -5462054773810051/36028797018963968 * x0^2 * x2^2
    + -5346287477580991/36028797018963968 * x0 * x1 * x2^2
    + -92562462037723/2251799813685248 * x1^2 * x2^2
    + 8810307269401287/576460752303423488 * x0 * x2^3
    + 3135835432654057/576460752303423488 * x1 * x2^3
    + -569947876840979/288230376151711744 * x2^4.

Lemma sigma_pos (x0 x1 x2 : R) : (sigma x0 x1 x2 >= 0)%Re.
(* Fail do_sdp. *)
rewrite /sigma.
Time do_sdp. (* 0.9 s on Erik's laptop *)
Time Qed. (* 0.25 s *)

(*
match goal with
| [ |- 0 <= (map_mpoly _ (interp_poly_ssr ?qn ?qap)).@[_] ] =>
  set n := qn;
  set ap := qap
end.
compute in n.
pose bqp := interp_poly_eff n ap.
Time let l := eval vm_compute in (M.elements bqp) in
let zQ := fresh "zQ" in soswitness of l as zQ.  (* 0.27 s *)
pose s := (size zQ.1).-1.
compute in s.
pose z' := (map (fun x => [:: x]) zQ.1).
pose Qf := map (map F2FI) zQ.2.
pose za := @spec_seqmx _ (@mnm0 n.+1) _ (@multinom_of_seqmultinom_val n.+1) s.+1 1 z'.
pose Qa := @spec_seqmx _ (FI0 fs) _ (id) s.+1 s.+1 Qf.
apply soscheck_correct with
        (1 := rat2R_additive)
        (2 := rat2F_correct)
        (3 := rat2R_F2rat)
        (4 := max_l)
        (5 := max_r)
        (z := za)
        (Q := Qa).
apply (etrans (y:=@soscheck_eff n.+1 _ zero_bigQ one_bigQ opp_bigQ add_bigQ sub_bigQ mul_bigQ eq_bigQ max_bigQ s fs FI2bigQ bigQ2FI (interp_poly_eff n ap) z' Qf)); last first.
Time by vm_compute.  (* 0.06 s *)
apply refines_eq.
eapply refines_apply; first eapply refines_apply; first eapply refines_apply.
{ by apply param_soscheck; tc. }
{ by apply param_interp_poly; vm_compute.  (* ça aussi, c'est calculé deux fois *) }
rewrite refinesE (*!*) /za /z'.
eapply RseqmxC_spec_seqmx.
{ done. (* size check *) }
{ rewrite {2}[[seq [:: x0] | x0 <- zQ.1]](_: ?[x] = map_seqmx id ?x) //.
  eapply (map_seqmx_R (A_R := fun m m' => m = m' /\ size m' = n.+1)); last first.
  fold z'.
  have : all (all (fun s => size s == n.+1)%B) z' by compute.
  clear; elim: z'  =>[//|a l IHl] Hsz /=.
  constructor 2 =>//.
  elim: a Hsz =>[//|b r IHr] /= Hsz.
  constructor 2 =>//.
  split=>//.
  by move: Hsz=>/andP[]/andP[]/eqP.
  apply: IHr.
  by move: Hsz=>/andP[]/andP[]/= _ -> ->.
  apply: IHl.
  by move: Hsz=>/=/andP[].
  (* ...we should move all this to a separate lemma... *)
  move=> m m' Hm; rewrite /spec /spec_id (proj1 Hm).
  apply refinesP.
  eapply refines_multinom_of_seqmultinom_val (* to rename! *).
  by rewrite (proj2 Hm).
}
by rewrite refinesE; eapply Rseqmx_spec_seqmx.
*)

Lemma sigma1_pos (x0 x1 x2 : R) : (sigma1 x0 x1 x2 >= 0)%Re.
rewrite /sigma1.
Time do_sdp. (* now: 1.78 s on Erik's laptop *)
Time Qed. (* 0.5 s *)

Lemma p_ind (x0 x1 x2 : R) : ((p (1/4
                                                      * (4/5 * x0
                                                         + 2/5 * (x1)^2))
                                                      (1/4
                                                      * (-3/5 * (x1)^2
                                                         + 3/10 * (x2)^2))
                                                      (1/4
                                                      * (1/2 * x2
                                                         + 2/5 * (x0)^2)))
       - (sigma x0 x1 x2)
         * (p x0 x1 x2)
       - (sigma1 x0 x1 x2) * ((x0)^2 + (x1)^2 + (x2)^2 - 1) >= 0)%Re.
rewrite /p /sigma /sigma1.
Time do_sdp. (* 4.2 s *)
Time Qed. (* 1.33 s *)

(* Time for the three lemmas above in OCaml : 0.17 s *)

Let sigma' x0 x1 := 6964204482325329/36028797018963968
    + 1918630498963825/144115188075855872 * x0
    + 1161234483464059/18014398509481984 * x1
    + 5444789216768803/36028797018963968 * x0^2
    + -7368710116162005/72057594037927936 * x0 * x1
    + 3097966790705159/18014398509481984 * x1^2
    + -178544179198253/4503599627370496 * x0^3
    + 3101825558039409/4611686018427387904 * x0^2 * x1
    + 3315754411930185/72057594037927936 * x0 * x1^2
    + -6226995629492937/144115188075855872 * x1^3
    + 7186804024588437/72057594037927936 * x0^4
    + -2701511384044589/36028797018963968 * x0^3 * x1
    + 1167350336098957/9007199254740992 * x0^2 * x1^2
    + -2475318548636101/72057594037927936 * x0 * x1^3
    + 7366564558001923/72057594037927936 * x1^4
    + -1501622110003261/144115188075855872 * x0^5
    + 7447960993428065/576460752303423488 * x0^4 * x1
    + 191863095256513/72057594037927936 * x0^3 * x1^2
    + -1684261967250991/36028797018963968 * x0^2 * x1^3
    + -8749567477280855/288230376151711744 * x0 * x1^4
    + -4874908393769803/288230376151711744 * x1^5
    + 7106979177940903/144115188075855872 * x0^6
    + -4145351089949037/288230376151711744 * x0^5 * x1
    + 6256252062099433/72057594037927936 * x0^4 * x1^2
    + -5174058135541473/72057594037927936 * x0^3 * x1^3
    + 5313235705808127/144115188075855872 * x0^2 * x1^4
    + -7799338135889971/144115188075855872 * x0 * x1^5
    + 8466357818981829/72057594037927936 * x1^6
    + -1852918639969545/36028797018963968 * x0^7
    + -5732179791659571/288230376151711744 * x0^6 * x1
    + -283041983368423/9007199254740992 * x0^5 * x1^2
    + -7408978672352703/144115188075855872 * x0^4 * x1^3
    + -6136659106457763/1152921504606846976 * x0^3 * x1^4
    + -2638113556019889/36028797018963968 * x0^2 * x1^5
    + -5558683972024799/144115188075855872 * x0 * x1^6
    + -1214463852862025/144115188075855872 * x1^7
    + -3690341441686655/288230376151711744 * x0^8
    + -2550675337117495/72057594037927936 * x0^7 * x1
    + 5359752868982073/72057594037927936 * x0^6 * x1^2
    + -2635340664350455/36028797018963968 * x0^5 * x1^3
    + 6908377399784323/144115188075855872 * x0^4 * x1^4
    + -7772424614757095/144115188075855872 * x0^3 * x1^5
    + 6987915226642825/144115188075855872 * x0^2 * x1^6
    + -1382612312810233/18014398509481984 * x0 * x1^7
    + 3257804240191977/36028797018963968 * x1^8
    + -7567984617085083/72057594037927936 * x0^9
    + -8361486027493781/288230376151711744 * x0^8 * x1
    + 8947317373017657/2305843009213693952 * x0^7 * x1^2
    + -8251056054653583/144115188075855872 * x0^6 * x1^3
    + -5392620823262423/288230376151711744 * x0^5 * x1^4
    + -1156149488409991/18014398509481984 * x0^4 * x1^5
    + -2999899898811619/72057594037927936 * x0^3 * x1^6
    + -1181932407855867/18014398509481984 * x0^2 * x1^7
    + -354657868322159/9007199254740992 * x0 * x1^8
    + -5718473475737139/288230376151711744 * x1^9
    + -3172920178540457/72057594037927936 * x0^10
    + -5592422349155669/144115188075855872 * x0^9 * x1
    + 3009076203950561/36028797018963968 * x0^8 * x1^2
    + -7219438121239939/144115188075855872 * x0^7 * x1^3
    + 7363087620169243/144115188075855872 * x0^6 * x1^4
    + -2338447608432075/36028797018963968 * x0^5 * x1^5
    + 1425066781920759/72057594037927936 * x0^4 * x1^6
    + -8798697236366617/144115188075855872 * x0^3 * x1^7
    + 3166669079964367/72057594037927936 * x0^2 * x1^8
    + -5391763613470809/72057594037927936 * x0 * x1^9
    + 1589003630145765/18014398509481984 * x1^10
    + -5230540152250557/36028797018963968 * x0^11
    + -3027386649451951/144115188075855872 * x0^10 * x1
    + 2257065558520631/144115188075855872 * x0^9 * x1^2
    + -18098393711413/281474976710656 * x0^8 * x1^3
    + -4631345148857263/144115188075855872 * x0^7 * x1^4
    + -597124797820569/9007199254740992 * x0^6 * x1^5
    + -5699620977412713/144115188075855872 * x0^5 * x1^6
    + -5690634790620097/72057594037927936 * x0^4 * x1^7
    + -3693649148627085/72057594037927936 * x0^3 * x1^8
    + -5579802335934167/72057594037927936 * x0^2 * x1^9
    + -3487424386557101/72057594037927936 * x0 * x1^10
    + -4605928037726749/288230376151711744 * x1^11
    + -2751023638722355/36028797018963968 * x0^12
    + -88128855612315/2251799813685248 * x0^11 * x1
    + 6524237232558641/72057594037927936 * x0^10 * x1^2
    + -7922476392385565/144115188075855872 * x0^9 * x1^3
    + 4287678362894893/72057594037927936 * x0^8 * x1^4
    + -584192092002987/9007199254740992 * x0^7 * x1^5
    + 5018053940032671/144115188075855872 * x0^6 * x1^6
    + -8605043418676655/144115188075855872 * x0^5 * x1^7
    + 2602985443672709/72057594037927936 * x0^4 * x1^8
    + -2389241271808361/36028797018963968 * x0^3 * x1^9
    + 4679904379066171/72057594037927936 * x0^2 * x1^10
    + -4521449936058659/72057594037927936 * x0 * x1^11
    + 8369596258787681/72057594037927936 * x1^12
    + -2832292292004677/18014398509481984 * x0^13
    + -1826275729832711/72057594037927936 * x0^12 * x1
    + 700536321302843/36028797018963968 * x0^11 * x1^2
    + -4977103204050875/72057594037927936 * x0^10 * x1^3
    + -4829848038529193/576460752303423488 * x0^9 * x1^4
    + -8932081551607123/144115188075855872 * x0^8 * x1^5
    + -4750424671035683/144115188075855872 * x0^7 * x1^6
    + -2564218165311417/36028797018963968 * x0^6 * x1^7
    + -1562985946414991/36028797018963968 * x0^5 * x1^8
    + -2358189472604843/36028797018963968 * x0^4 * x1^9
    + -745518195744731/18014398509481984 * x0^3 * x1^10
    + -8700772169109923/144115188075855872 * x0^2 * x1^11
    + -2046695141055575/72057594037927936 * x0 * x1^12
    + 5064802475379261/288230376151711744 * x1^13
    + 2939334698596107/72057594037927936 * x0^14
    + -642109884803047/9007199254740992 * x0^13 * x1
    + 1588542347502125/9007199254740992 * x0^12 * x1^2
    + -7359860772822339/144115188075855872 * x0^11 * x1^3
    + 8725971067800445/72057594037927936 * x0^10 * x1^4
    + -235460695149107/4503599627370496 * x0^9 * x1^5
    + 790669371246759/9007199254740992 * x0^8 * x1^6
    + -1836319913240623/36028797018963968 * x0^7 * x1^7
    + 1405692132970795/18014398509481984 * x0^6 * x1^8
    + -6696423599574075/144115188075855872 * x0^5 * x1^9
    + 221847881556747/2251799813685248 * x0^4 * x1^10
    + -8004793190321167/144115188075855872 * x0^3 * x1^11
    + 1293987845752943/9007199254740992 * x0^2 * x1^12
    + -1783424089532015/36028797018963968 * x0 * x1^13
    + 7573842062969713/36028797018963968 * x1^14
    + 5550247441751591/72057594037927936 * x0^15
    + -3741787957035009/36028797018963968 * x0^14 * x1
    + 1458251207983373/9007199254740992 * x0^13 * x1^2
    + -2844013754029037/36028797018963968 * x0^12 * x1^3
    + 5036467503367761/72057594037927936 * x0^11 * x1^4
    + -6319401850367007/144115188075855872 * x0^10 * x1^5
    + 6324393986725989/288230376151711744 * x0^9 * x1^6
    + -5688866488089723/144115188075855872 * x0^8 * x1^7
    + 1073371563255513/72057594037927936 * x0^7 * x1^8
    + -2464151333590959/72057594037927936 * x0^6 * x1^9
    + 8543164198337889/2305843009213693952 * x0^5 * x1^10
    + -6977584505728899/288230376151711744 * x0^4 * x1^11
    + 2429750064654207/144115188075855872 * x0^3 * x1^12
    + -5246731368455737/144115188075855872 * x0^2 * x1^13
    + 4197777311792857/144115188075855872 * x0 * x1^14
    + 8192522920943453/144115188075855872 * x1^15
    + 8014096465430573/18014398509481984 * x0^16
    + -2480705005581427/9007199254740992 * x0^15 * x1
    + 1909349818403803/4503599627370496 * x0^14 * x1^2
    + -9003921729746775/72057594037927936 * x0^13 * x1^3
    + 2328419508494811/9007199254740992 * x0^12 * x1^4
    + -5758622995864813/72057594037927936 * x0^11 * x1^5
    + 1709120060932403/9007199254740992 * x0^10 * x1^6
    + -1265157424474303/18014398509481984 * x0^9 * x1^7
    + 6133524655869833/36028797018963968 * x0^8 * x1^8
    + -5273986281717753/72057594037927936 * x0^7 * x1^9
    + 1453709284633873/9007199254740992 * x0^6 * x1^10
    + -718876659532749/9007199254740992 * x0^5 * x1^11
    + 3054405824197293/18014398509481984 * x0^4 * x1^12
    + -6295574908459263/72057594037927936 * x0^3 * x1^13
    + 7718561023688201/36028797018963968 * x0^2 * x1^14
    + -8348202004569801/72057594037927936 * x0 * x1^15
    + 8058594338290843/36028797018963968 * x1^16.

Let sigma1' x0 x1 :=  6994069049404239/36028797018963968
    + -1330594597357463/18014398509481984 * x0
    + -1578566276159533/72057594037927936 * x1
    + 2129511623555293/18014398509481984 * x0^2
    + -4755600070602481/144115188075855872 * x0 * x1
    + 4535507820551899/36028797018963968 * x1^2
    + -1163865731132155/18014398509481984 * x0^3
    + -1664574816182589/144115188075855872 * x0^2 * x1
    + -4233103609603199/72057594037927936 * x0 * x1^2
    + -5908463482616691/288230376151711744 * x1^3
    + 2975013809391853/36028797018963968 * x0^4
    + -2591244966328979/288230376151711744 * x0^3 * x1
    + 5187652640397495/144115188075855872 * x0^2 * x1^2
    + -6726448832398477/288230376151711744 * x0 * x1^3
    + 3920231445950003/36028797018963968 * x1^4
    + -4615015149040191/72057594037927936 * x0^5
    + -2564099793515129/1152921504606846976 * x0^4 * x1
    + -5181046432950401/144115188075855872 * x0^3 * x1^2
    + -3393947632034549/144115188075855872 * x0^2 * x1^3
    + -8586790284743165/144115188075855872 * x0 * x1^4
    + -6301636969116333/288230376151711744 * x1^5
    + 4621318683274873/72057594037927936 * x0^6
    + 2207633022259919/576460752303423488 * x0^5 * x1
    + 5502761874451383/144115188075855872 * x0^4 * x1^2
    + -886666076965065/72057594037927936 * x0^3 * x1^3
    + 1842633859415363/72057594037927936 * x0^2 * x1^4
    + -8682919780160621/288230376151711744 * x0 * x1^5
    + 43506220545211/562949953421312 * x1^6
    + -4671917375535847/72057594037927936 * x0^7
    + 6656365650243409/1152921504606846976 * x0^6 * x1
    + -5222592368843433/288230376151711744 * x0^5 * x1^2
    + -4489365274887805/1152921504606846976 * x0^4 * x1^3
    + -7508053661331995/144115188075855872 * x0^3 * x1^4
    + -4480283984658619/288230376151711744 * x0^2 * x1^5
    + -3364027720328997/72057594037927936 * x0 * x1^6
    + -1256989256718995/72057594037927936 * x1^7
    + 846869062952529/18014398509481984 * x0^8
    + 1472711680467307/144115188075855872 * x0^7 * x1
    + 6159762705919591/144115188075855872 * x0^6 * x1^2
    + 6946844638021965/2305843009213693952 * x0^5 * x1^3
    + 7264832813263241/576460752303423488 * x0^4 * x1^4
    + -731230058048897/72057594037927936 * x0^3 * x1^5
    + 5984586432557949/288230376151711744 * x0^2 * x1^6
    + -5984488349686465/288230376151711744 * x0 * x1^7
    + 5785042605553147/72057594037927936 * x1^8
    + -5222968189292661/72057594037927936 * x0^9
    + 8054990833861379/1152921504606846976 * x0^8 * x1
    + -896878270097645/72057594037927936 * x0^7 * x1^2
    + 3004086915607789/576460752303423488 * x0^6 * x1^3
    + -1240606469404597/36028797018963968 * x0^5 * x1^4
    + -4775235695989241/1152921504606846976 * x0^4 * x1^5
    + -2336305045952721/72057594037927936 * x0^3 * x1^6
    + -4042441491249973/288230376151711744 * x0^2 * x1^7
    + -5519959300902073/144115188075855872 * x0 * x1^8
    + -4930448486115537/288230376151711744 * x1^9
    + 1293015088732623/36028797018963968 * x0^10
    + 3871504118763639/576460752303423488 * x0^9 * x1
    + 1868453525628543/36028797018963968 * x0^8 * x1^2
    + 2444989761660627/288230376151711744 * x0^7 * x1^3
    + 5360314190496983/288230376151711744 * x0^6 * x1^4
    + 743438374212051/1152921504606846976 * x0^5 * x1^5
    + 2857473219756297/144115188075855872 * x0^4 * x1^6
    + -54790165207693/9007199254740992 * x0^3 * x1^7
    + 7009447214171655/288230376151711744 * x0^2 * x1^8
    + -5913344526774653/288230376151711744 * x0 * x1^9
    + 5709270385809151/72057594037927936 * x1^10
    + -726672791152667/9007199254740992 * x0^11
    + -3668428850502309/1152921504606846976 * x0^10 * x1
    + -7928543642624267/2305843009213693952 * x0^9 * x1^2
    + 976395670101803/144115188075855872 * x0^8 * x1^3
    + -3498703283525995/144115188075855872 * x0^7 * x1^4
    + 8980737175785651/4611686018427387904 * x0^6 * x1^5
    + -3559291630151885/144115188075855872 * x0^5 * x1^6
    + -1263062165588027/2305843009213693952 * x0^4 * x1^7
    + -7618469909582017/288230376151711744 * x0^3 * x1^8
    + -1886803110011793/144115188075855872 * x0^2 * x1^9
    + -1310936715287541/36028797018963968 * x0 * x1^10
    + -2935478227799507/144115188075855872 * x1^11
    + 5585699812279693/144115188075855872 * x0^12
    + -3595465301571071/576460752303423488 * x0^11 * x1
    + 8837457830670761/144115188075855872 * x0^10 * x1^2
    + 1253071521797421/144115188075855872 * x0^9 * x1^3
    + 5805099825345673/288230376151711744 * x0^8 * x1^4
    + 6325456838598407/1152921504606846976 * x0^7 * x1^5
    + 5692098436344329/288230376151711744 * x0^6 * x1^6
    + 5655468004383923/1152921504606846976 * x0^5 * x1^7
    + 3396529628060355/144115188075855872 * x0^4 * x1^8
    + -1540353258876637/288230376151711744 * x0^3 * x1^9
    + 3922290814114791/144115188075855872 * x0^2 * x1^10
    + -3385351687755569/144115188075855872 * x0 * x1^11
    + 2906168629572577/36028797018963968 * x1^12
    + -2980264605171405/36028797018963968 * x0^13
    + -6540076195466423/288230376151711744 * x0^12 * x1
    + -3762536312151417/4611686018427387904 * x0^11 * x1^2
    + 6502206350887779/2305843009213693952 * x0^10 * x1^3
    + -8201658932594855/288230376151711744 * x0^9 * x1^4
    + 679666366405259/288230376151711744 * x0^8 * x1^5
    + -6412119597994553/288230376151711744 * x0^7 * x1^6
    + 6739034653913133/1152921504606846976 * x0^6 * x1^7
    + -2511797403415181/144115188075855872 * x0^5 * x1^8
    + -4116724783323913/4611686018427387904 * x0^4 * x1^9
    + -7247325297871677/288230376151711744 * x0^3 * x1^10
    + -2355639634113663/144115188075855872 * x0^2 * x1^11
    + -2759896290142377/72057594037927936 * x0 * x1^12
    + -7281070048203203/288230376151711744 * x1^13
    + 4109068498222267/72057594037927936 * x0^14
    + -3339146718240805/144115188075855872 * x0^13 * x1
    + 2444556991064691/36028797018963968 * x0^12 * x1^2
    + 1357180426838481/288230376151711744 * x0^11 * x1^3
    + 2621024012645247/144115188075855872 * x0^10 * x1^4
    + 2926032645880201/1152921504606846976 * x0^9 * x1^5
    + 5419315741146273/288230376151711744 * x0^8 * x1^6
    + 267015293554425/36028797018963968 * x0^7 * x1^7
    + 3617761873316907/144115188075855872 * x0^6 * x1^8
    + 8759259141837143/2305843009213693952 * x0^5 * x1^9
    + 928609795502377/36028797018963968 * x0^4 * x1^10
    + -5757094348074233/576460752303423488 * x0^3 * x1^11
    + 3791469451051197/144115188075855872 * x0^2 * x1^12
    + -1075232590042739/36028797018963968 * x0 * x1^13
    + 1446191915696769/18014398509481984 * x1^14
    + -5425647228556787/72057594037927936 * x0^15
    + -7084987830340137/144115188075855872 * x0^14 * x1
    + -1228601878317851/288230376151711744 * x0^13 * x1^2
    + -4990357239736807/576460752303423488 * x0^12 * x1^3
    + -658738232016619/18014398509481984 * x0^11 * x1^4
    + -6377737270990259/1152921504606846976 * x0^10 * x1^5
    + -1902944060820779/72057594037927936 * x0^9 * x1^6
    + 4771338056341125/1152921504606846976 * x0^8 * x1^7
    + -2386573798821861/144115188075855872 * x0^7 * x1^8
    + 1580063974254829/288230376151711744 * x0^6 * x1^9
    + -4751052157352059/288230376151711744 * x0^5 * x1^10
    + -4988538727347701/1152921504606846976 * x0^4 * x1^11
    + -8237199400825845/288230376151711744 * x0^3 * x1^12
    + -3439744640598407/144115188075855872 * x0^2 * x1^13
    + -6646822603322199/144115188075855872 * x0 * x1^14
    + -4835578728903227/144115188075855872 * x1^15
    + 6989608398294747/72057594037927936 * x0^16
    + -6042056729343083/144115188075855872 * x0^15 * x1
    + 2756729324731179/36028797018963968 * x0^14 * x1^2
    + -974844751712803/288230376151711744 * x0^13 * x1^3
    + 2534167580898473/144115188075855872 * x0^12 * x1^4
    + -3347223356328753/576460752303423488 * x0^11 * x1^5
    + 267984658324383/18014398509481984 * x0^10 * x1^6
    + 7978122977517655/2305843009213693952 * x0^9 * x1^7
    + 6930644629757903/288230376151711744 * x0^8 * x1^8
    + 1777163242951485/288230376151711744 * x0^7 * x1^9
    + 8070782894942879/288230376151711744 * x0^6 * x1^10
    + -3987729805506691/2305843009213693952 * x0^5 * x1^11
    + 7213326806317495/288230376151711744 * x0^4 * x1^12
    + -714627985845631/36028797018963968 * x0^3 * x1^13
    + 1647385614967109/72057594037927936 * x0^2 * x1^14
    + -6026029954816209/144115188075855872 * x0 * x1^15
    + 6069473516564661/72057594037927936 * x1^16
    + -7939575375349659/72057594037927936 * x0^17
    + -1803476890008321/36028797018963968 * x0^16 * x1
    + -5141932552076579/144115188075855872 * x0^15 * x1^2
    + -6481131795609619/576460752303423488 * x0^14 * x1^3
    + -4116322488139435/72057594037927936 * x0^13 * x1^4
    + -2087299814790153/144115188075855872 * x0^12 * x1^5
    + -6084465094042891/144115188075855872 * x0^11 * x1^6
    + -610908611797899/288230376151711744 * x0^10 * x1^7
    + -3441217700515557/144115188075855872 * x0^9 * x1^8
    + 6383465751256621/1152921504606846976 * x0^8 * x1^9
    + -4528895618799375/288230376151711744 * x0^7 * x1^10
    + 6127681514910021/2305843009213693952 * x0^6 * x1^11
    + -6067582300874965/288230376151711744 * x0^5 * x1^12
    + -355881624690015/36028797018963968 * x0^4 * x1^13
    + -5188307300128963/144115188075855872 * x0^3 * x1^14
    + -8649895050422315/288230376151711744 * x0^2 * x1^15
    + -7862524279157063/144115188075855872 * x0 * x1^16
    + -5647793681872099/144115188075855872 * x1^17
    + 723575939311751/9007199254740992 * x0^18
    + -1612595028497075/72057594037927936 * x0^17 * x1
    + 5187880563982105/72057594037927936 * x0^16 * x1^2
    + 7671427191712289/2305843009213693952 * x0^15 * x1^3
    + 8367488611269815/576460752303423488 * x0^14 * x1^4
    + -6833973591160043/576460752303423488 * x0^13 * x1^5
    + 5916699148561267/576460752303423488 * x0^12 * x1^6
    + -8446732988879321/2305843009213693952 * x0^11 * x1^7
    + 1544577917492627/72057594037927936 * x0^10 * x1^8
    + 2111224834680101/576460752303423488 * x0^9 * x1^9
    + 4229586734125793/144115188075855872 * x0^8 * x1^10
    + 1734548924051637/576460752303423488 * x0^7 * x1^11
    + 4068009988454311/144115188075855872 * x0^6 * x1^12
    + -4564152278934221/576460752303423488 * x0^5 * x1^13
    + 5698333609119795/288230376151711744 * x0^4 * x1^14
    + -7339646275568263/288230376151711744 * x0^3 * x1^15
    + 2504847013224205/144115188075855872 * x0^2 * x1^16
    + -6043402987561347/144115188075855872 * x0 * x1^17
    + 6545897439387275/72057594037927936 * x1^18
    + -622289295783755/9007199254740992 * x0^19
    + 8533336607094337/144115188075855872 * x0^18 * x1
    + -6918327293504909/9223372036854775808 * x0^17 * x1^2
    + 7854610042057015/1152921504606846976 * x0^16 * x1^3
    + -5692390980959085/144115188075855872 * x0^15 * x1^4
    + -7527208943892631/288230376151711744 * x0^14 * x1^5
    + -6404935949709351/144115188075855872 * x0^13 * x1^6
    + -1205609167552887/72057594037927936 * x0^12 * x1^7
    + -4180853642871455/144115188075855872 * x0^11 * x1^8
    + -191394318707183/36028797018963968 * x0^10 * x1^9
    + -1187916287974237/72057594037927936 * x0^9 * x1^10
    + -3276873418655027/2305843009213693952 * x0^8 * x1^11
    + -8433007804888411/576460752303423488 * x0^7 * x1^12
    + -4073135498416311/576460752303423488 * x0^6 * x1^13
    + -3347801309033889/144115188075855872 * x0^5 * x1^14
    + -6980770958455757/288230376151711744 * x0^4 * x1^15
    + -5954880586606559/144115188075855872 * x0^3 * x1^16
    + -375214714738567/9007199254740992 * x0^2 * x1^17
    + -2092525552322805/36028797018963968 * x0 * x1^18
    + -1189832578674857/36028797018963968 * x1^19
    + 2739498521393715/36028797018963968 * x0^20
    + -3434902729420567/288230376151711744 * x0^19 * x1
    + -4628445398101699/144115188075855872 * x0^18 * x1^2
    + -2172428253294599/36028797018963968 * x0^17 * x1^3
    + -7840475501584147/2305843009213693952 * x0^16 * x1^4
    + -8854032993897295/144115188075855872 * x0^15 * x1^5
    + 3240023796790523/576460752303423488 * x0^14 * x1^6
    + -4595419077440965/144115188075855872 * x0^13 * x1^7
    + 911950188268073/36028797018963968 * x0^12 * x1^8
    + -7472530459020833/576460752303423488 * x0^11 * x1^9
    + 5515059751212095/144115188075855872 * x0^10 * x1^10
    + -6776411388363007/1152921504606846976 * x0^9 * x1^11
    + 3018744997935621/72057594037927936 * x0^8 * x1^12
    + -5320274338631385/576460752303423488 * x0^7 * x1^13
    + 5241946330251767/144115188075855872 * x0^6 * x1^14
    + -3258123299795441/144115188075855872 * x0^5 * x1^15
    + 8423703242683073/288230376151711744 * x0^4 * x1^16
    + -3388349510972689/72057594037927936 * x0^3 * x1^17
    + 1258471180699125/36028797018963968 * x0^2 * x1^18
    + -4692708590550603/72057594037927936 * x0 * x1^19
    + 1261963007473071/9007199254740992 * x1^20
    + -5089379953621075/576460752303423488 * x0^21
    + 5010571512568475/144115188075855872 * x0^20 * x1
    + 6078580638174729/144115188075855872 * x0^19 * x1^2
    + 2902004875037769/36028797018963968 * x0^18 * x1^3
    + 5022319136498079/2305843009213693952 * x0^17 * x1^4
    + 492325635105487/36028797018963968 * x0^16 * x1^5
    + -4334607197157891/72057594037927936 * x0^15 * x1^6
    + 3068347178311573/576460752303423488 * x0^14 * x1^7
    + -8042670491254309/144115188075855872 * x0^13 * x1^8
    + -1397932927966777/4611686018427387904 * x0^12 * x1^9
    + -3036450538072303/72057594037927936 * x0^11 * x1^10
    + -810152758456515/2305843009213693952 * x0^10 * x1^11
    + -2467513157002115/72057594037927936 * x0^9 * x1^12
    + -3924034944282949/1152921504606846976 * x0^8 * x1^13
    + -168954301485263/4503599627370496 * x0^7 * x1^14
    + -3691800604979293/288230376151711744 * x0^6 * x1^15
    + -7779335097167179/144115188075855872 * x0^5 * x1^16
    + -7700666330651289/288230376151711744 * x0^4 * x1^17
    + -698816950573755/9007199254740992 * x0^3 * x1^18
    + -3217072209946563/72057594037927936 * x0^2 * x1^19
    + -6698991731374633/72057594037927936 * x0 * x1^20
    + -2772109814923863/72057594037927936 * x1^21
    + 4907444025533963/9223372036854775808 * x0^22
    + -3623249174451815/2305843009213693952 * x0^21 * x1
    + 6721343914246905/1152921504606846976 * x0^20 * x1^2
    + 4331637210394991/288230376151711744 * x0^19 * x1^3
    + 679652321982527/36028797018963968 * x0^18 * x1^4
    + -7140350326660877/144115188075855872 * x0^17 * x1^5
    + 1536565775937787/72057594037927936 * x0^16 * x1^6
    + 6422922827940817/144115188075855872 * x0^15 * x1^7
    + 379230731992147/9007199254740992 * x0^14 * x1^8
    + 2954061275617585/72057594037927936 * x0^13 * x1^9
    + 2491854673341953/36028797018963968 * x0^12 * x1^10
    + 7875775192745143/288230376151711744 * x0^11 * x1^11
    + 5820686947690153/72057594037927936 * x0^10 * x1^12
    + 582263738217759/36028797018963968 * x0^9 * x1^13
    + 719895384368999/9007199254740992 * x0^8 * x1^14
    + 192020988847769/18014398509481984 * x0^7 * x1^15
    + 5100261742442087/72057594037927936 * x0^6 * x1^16
    + 5230914446631719/1152921504606846976 * x0^5 * x1^17
    + 4744957067463137/72057594037927936 * x0^4 * x1^18
    + 7702751968293449/2305843009213693952 * x0^3 * x1^19
    + 5771996305111039/72057594037927936 * x0^2 * x1^20
    + 7442128151016039/576460752303423488 * x0 * x1^21
    + 6022360071315081/36028797018963968 * x1^22.

Let p' x1 x2 := 161665552462085691/72057594037927936
    + 5894209604283881/576460752303423488 * x1
    + 4026839744894797/1152921504606846976 * x2
    + -570763263822683/70368744177664 * x1^2
    + -3276759790410289/562949953421312 * x1 * x2
    + -8583394086252111/1125899906842624 * x2^2
    + 6371928205597611/562949953421312 * x1^3
    + 2990885910233667/281474976710656 * x1^2 * x2
    + 1643973001149963/140737488355328 * x1 * x2^2
    + 1542089506080425/281474976710656 * x2^3
    + -4799251149104555/562949953421312 * x1^4
    + -5658382378280923/1125899906842624 * x1^3 * x2
    + 7749818766026805/2251799813685248 * x1^2 * x2^2
    + 1281182822772917/2251799813685248 * x1 * x2^3
    + 96115315873591/17592186044416 * x2^4
    + 6194375225294295/1125899906842624 * x1^5
    + 216753755181017/70368744177664 * x1^4 * x2
    + -420813637474157/35184372088832 * x1^3 * x2^2
    + -7884809520285811/562949953421312 * x1^2 * x2^3
    + -3590702668670401/281474976710656 * x1 * x2^4
    + -2607751962589009/562949953421312 * x2^5
    + -1386973484500641/562949953421312 * x1^6
    + -4760860470479713/2251799813685248 * x1^5 * x2
    + 7441625272809979/1125899906842624 * x1^4 * x2^2
    + 1414455816956327/140737488355328 * x1^3 * x2^3
    + 6326806100507715/1125899906842624 * x1^2 * x2^4
    + 5242312748125127/4503599627370496 * x1 * x2^5
    + -6753693085396311/2251799813685248 * x2^6
    + 2310408309450379/9007199254740992 * x1^7
    + -1282633630135753/4503599627370496 * x1^6 * x2
    + -3873229099985911/2251799813685248 * x1^5 * x2^2
    + -5645906880002219/2251799813685248 * x1^4 * x2^3
    + -6242468220524711/2251799813685248 * x1^3 * x2^4
    + 5687521358113993/2251799813685248 * x1^2 * x2^5
    + 1674758640227347/140737488355328 * x1 * x2^6
    + 6291148553230949/1125899906842624 * x2^7
    + -5252213773793345/576460752303423488 * x1^8
    + 7348633685485539/288230376151711744 * x1^7 * x2
    + -2047870194208245/144115188075855872 * x1^6 * x2^2
    + -2879854488063785/9007199254740992 * x1^5 * x2^3
    + -5649078646047861/36028797018963968 * x1^4 * x2^4
    + 1694311663061067/1125899906842624 * x1^3 * x2^5
    + -6411409407138369/72057594037927936 * x1^2 * x2^6
    + -1516261991165219/281474976710656 * x1 * x2^7
    + -2878544359045033/562949953421312 * x2^8.

Lemma sigma_pos' (x0 x1 : R) : (sigma' x0 x1 >= 0)%Re.
rewrite /sigma'.
Time do_sdp. (* 5 s on Erik's laptop 7.3 *)
Time Qed. (* 1.5 s 2.4 *)

Lemma sigma1_pos' (x0 x1 : R) : (sigma1' x0 x1 >= 0)%Re.
rewrite /sigma1'.
Time do_sdp. (* 14.2 s on Erik's laptop 21 *)
Time Qed. (* 3.5 s 6 *)

Lemma p_ind' (x0 x1 : R) : ((p' (1/2 * (x0)^3 + 2/5 * (x1)^2)
                                (-3/5 * (x0)^2 + 3/10 * (x1)^2))
       - (sigma' x0 x1)
         * (p' x0 x1)
       - (sigma1' x0 x1) * ((x0)^2 + (x1)^2 - 1) >= 0)%Re.
rewrite /p' /sigma' /sigma1'.
Time do_sdp. (* 24 s on Erik's laptop *)
Time Qed. (* 5.5 s *)
