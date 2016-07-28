From Flocq Require Import Fcore.
From CoqEAL.theory Require Import hrel.
From CoqEAL.refinements Require Import refinements param (*seqmx*) binint rational.
Require Import seqmx.
Require Import Reals Flocq.Core.Fcore_Raux QArith BigZ BigQ Psatz FSetAVL.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype matrix ssralg bigop.
From mathcomp Require Import ssrnum ssrint rat.
From SsrMultinomials Require Import mpoly (* freeg *).
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
Import Refinements.Op.
Require Import cholesky_prog multipoly.
(* Require Import Quote. *)
Require Import soswitness.soswitness.
Require Import seqmx_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Ltac get_rational t :=
  let get_positive t :=
    let rec aux t :=
      match t with
      | 1%Re => xH
      | 2%Re => constr:(xO xH)
      | 3%Re => constr:(xI xH)
      | (2 * ?v)%Re =>
        let w := aux v in constr:(xO w)
      | (1 + 2 * ?v)%Re =>
        let w := aux v in constr:(xI w)
      end in
    aux t in
  let get_rational_aux s n d :=
    let nn := get_positive n in
    let dd := get_positive d in
    eval vm_compute in (BigQ.of_Q (Qmake ((if s then Z.neg else Z.pos) nn) dd)) in
  let get_integer s n :=
    let nn := get_positive n in
    eval vm_compute in (BigQ.of_Q (inject_Z ((if s then Z.neg else Z.pos) nn))) in
  match t with
  | 0%Re => constr:(0%bigQ)
  | (-?n * /?d)%Re => get_rational_aux true n d
  | (?n * /?d)%Re => get_rational_aux false n d
  | (-?n / ?d)%Re => get_rational_aux true n d
  | (?n / ?d)%Re => get_rational_aux false n d
  | (-?n)%Re => get_integer true n
  | ?n => get_integer false n
  | _ => false
  end.

Lemma test_get_rational : (-1234 / 5678 >= 0)%Re.
match goal with
[ |- (?r >= 0)%Re ] => let t := get_rational r in idtac t
end.
Abort.

(* TODO: Move to misc *)

(* We do not use [RMicromega.IQR], which relies on [IZR] instead of [Z2R]... *)
Definition Q2R (x : Q) : R :=
  (Z2R (Qnum x) / Z2R (Z.pos (Qden x)))%Re.
Local Coercion Q2R : Q >-> R.
Local Coercion BigQ.to_Q : bigQ >-> Q.

Inductive abstr_poly :=
  (* | Const of Poly.t *)
  (* | Mult_scalar of Poly.Coeff.t * abstr_poly *)
  | Const of bigQ
  | Var of nat
  | Add of abstr_poly & abstr_poly
  | Sub of abstr_poly & abstr_poly
  | Mul of abstr_poly & abstr_poly
  | Pow of abstr_poly & binnat.N
  (* | Compose of abstr_poly * abstr_poly list *).

Fixpoint interp_real (vm : seq R) (ap : abstr_poly) {struct ap} : R :=
  match ap with
  | Const c => Q2R (BigQ.to_Q c)
  | Add p q => Rplus (interp_real vm p) (interp_real vm q)
  | Sub p q => Rminus (interp_real vm p) (interp_real vm q)
  | Mul p q => Rmult (interp_real vm p) (interp_real vm q)
  | Pow p n => powerRZ (interp_real vm p) (Z.of_N n)
  | Var i => seq.nth R0 vm i
  end.

Global Instance zero_bigQ : zero_of bigQ := 0%bigQ.
Global Instance one_bigQ : one_of bigQ := 1%bigQ.
Global Instance opp_bigQ : opp_of bigQ := BigQ.opp.
Global Instance add_bigQ : add_of bigQ := BigQ.add.
Global Instance sub_bigQ : sub_of bigQ := BigQ.sub.
Global Instance mul_bigQ : mul_of bigQ := BigQ.mul.
Global Instance eq_bigQ : eq_of bigQ := BigQ.eq_bool.

Definition Z2int (z : BinNums.Z) :=
  match z with
  | Z0 => 0%:Z
  | Z.pos p => (Pos.to_nat p)%:Z
  | Z.neg n => (- (Pos.to_nat n)%:Z)%R
  end.

Program Definition BigQ2rat (bq : bigQ) :=
  let q := Qred [bq]%bigQ in
  @Rat (Z2int (Qnum q), Z2int (Z.pos (Qden q))) _.
Next Obligation.
Admitted. (* Erik *)

Definition interp_poly_ssr n (ap : abstr_poly) : {mpoly rat[n.+1]} :=
  let fix aux ap :=
      match ap with
      | Const c => (BigQ2rat c)%:MP_[n.+1]
      | Var i => 'X_(inord i)
      | Add p q => (aux p + aux q)%R
      | Sub p q => (aux p - aux q)%R
      | Mul p q => (aux p * aux q)%R
      | Pow p m => mpoly_exp (aux p) m
      end
  in aux ap.

Definition interp_poly_eff n (ap : abstr_poly) : effmpoly bigQ :=
  let fix aux ap :=
      match ap with
      | Const c => @mpolyC_eff bigQ n.+1 c
      | Var i => @mpvar_eff bigQ n.+1 1%bigQ 1 (N.of_nat i) (* should be "i" *)
      | Add p q => mpoly_add_eff (aux p) (aux q)
      | Sub p q => mpoly_sub_eff (aux p) (aux q)
      | Mul p q => mpoly_mul_eff (aux p) (aux q)
      | Pow p m => mpoly_exp_eff (n := n.+1) (aux p) m
      end
  in aux ap.

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
    match get_rational t with
    | false =>
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
      | Ropp ?a => aux_u (Sub (Const 0%bigQ)) a
      | Rsqr ?a => aux (Rmult a a) l
   (* | powerRZ ?a 0%Z => constr:(R1) [unwise to simplify here!] *)
      | powerRZ ?a ?b =>
        let bb := eval vm_compute in (Z.abs_N b) in aux_u' Pow a bb
      | pow ?a ?b =>
        let bb := eval vm_compute in (N.of_nat b) in aux_u' Pow a bb
      | Rplus ?a ?b => aux_b Add a b
      | Rminus ?a ?b => aux_b Sub a b
      | Rplus ?a (Ropp ?b) => aux_b Sub a b
      | Rmult ?a ?b => aux_b Mul a b
      | _ =>
        match list_add t l with
        | (?n, ?l) => constr:(Var n, l)
        end
      end
    | ?c =>
      constr:(Const c, l)
    end in
  aux t l.

Lemma test_get_poly x y : (2/3 * x ^ 2 + x * y >= 0)%Re.
match goal with
| [ |- (?r >= 0)%Re ] => let p := get_poly r (@Datatypes.nil R) in idtac p
end.
Abort.

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
Let F := FI fs.
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
       * grandeur que la décomposition de Cholesky) *)
      fun_of_op p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    max_coeff pmp' in
  posdef_check_itv (@fieps fs) (@fieta fs) (@is_finite fs) Q (T2F r).

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
Let F := FI fs.
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
Let F := FI fs.
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
Hypothesis T2F_correct : forall x, is_finite (T2F x) -> T2R x <= FI2F (T2F x).
Hypothesis T2R_F2T : forall x, T2R (F2T x) = FI2F x.
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

(* seemingly missing in mpoly *)
Lemma map_mpolyC (R S : ringType) (f : R -> S) (Hf0 : f 0%R = 0%R) n' c :
  map_mpoly f c%:MP_[n'] = (f c)%:MP_[n'].
Proof.
rewrite /map_mpoly /mmap msuppC.
case_eq (c == 0%R); [by move/eqP ->; rewrite big_nil Hf0 mpolyC0|].
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

Require Import bigop_tactics.

Tactic Notation "underbigs" simple_intropattern(x) simple_intropattern(Hx)
  tactic(tac) := underbig (bigop _ _ _) x Hx tac.

Lemma soscheck_correct p z Q : soscheck_ssr p z Q ->
  forall x, 0 <= (map_mpoly T2R p).@[x].
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
  have Pr := max_coeff_pos _ : 0 <= T2R r.
  split.
  { move=> i j; rewrite !mxE Rabs_mult.
    have NZnbij : INR (nbij i j) <> 0.
    { by change 0 with (INR 0); move/INR_eq; move: (Pnbij i j); case nbij. }
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
  underbigs ? _ rewrite mxE big_distrl /=; underbigs ? _ rewrite mxE.
  rewrite pair_bigA /= (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  have -> : M = map_mpolyC_R (matrix.map_mx (T2R \o F2T) Q + E)%R.
  { apply/matrixP=> i j; rewrite /map_mpolyC_R /mpolyC_R.
    by rewrite !mxE mpolyCD (map_mpolyC (GRing.raddf0 _)). }
  move {M}; set M := map_mpolyC_R _.
  underbigs ? _ rewrite (GRing.mulrC (zpr _ _)) -GRing.mulrA mxE mcoeffCM.
  underbigs ? _ rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX.
  rewrite (bigID (fun ij => zij ij.2 ij.1 == m)) /= GRing.addrC.
  rewrite big1 ?GRing.add0r; last first.
  { by move=> ij; move/negbTE=> ->; rewrite GRing.mul0r. }
  underbigs ? Hi rewrite Hi GRing.mul1r 2!mxE.
  rewrite big_split /= GRing.addrC.
  pose nbm := size [seq ij <- index_enum I_sp1_2 | zij ij.2 ij.1 == m].
  underbigs ? Hi
    (move/eqP in Hi; rewrite mxE /nbij Hi -/nbm mcoeffB GRing.raddfB /=).
  rewrite misc.big_sum_pred_const -/nbm -[_ / _]/(_ * / _)%R.
  rewrite GRing.mulrDl GRing.mulrDr -GRing.addrA.
  rewrite -{1}(GRing.addr0 (T2R _)); f_equal.
  { rewrite GRing.mulrC -GRing.mulrA; case_eq (m \in msupp p).
    { move=> Hm; move: (check_base_correct Hbase Hm).
      move=> [i [j {Hm}Hm]]; rewrite /GRing.mul /=; field.
      apply Rgt_not_eq, Rlt_gt; change R0 with (INR 0); apply lt_INR.
      rewrite /nbm filter_index_enum; rewrite <-cardE.
      by apply/ltP/card_gt0P; exists (j, i); rewrite /in_mem /=. }
    by rewrite mcoeff_msupp; move/eqP->; rewrite GRing.raddf0 GRing.mul0r. }
  rewrite /p' mxE.
  underbigs ? _ (rewrite mxE big_distrl /=; underbigs ? _ rewrite mxE).
  rewrite pair_bigA /= (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  underbigs ? _ rewrite (GRing.mulrC (zp _ _)) -GRing.mulrA mxE mcoeffCM.
  underbigs ? _ rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX.
  rewrite GRing.raddf_sum /= (bigID (fun ij => zij ij.2 ij.1 == m)) /=.
  underbigs ? Hi rewrite Hi GRing.mul1r.
  set b := bigop _ _ _; rewrite big1; last first; [|rewrite {}/b GRing.addr0].
  { by move=> ij; move/negbTE => ->; rewrite GRing.mul0r GRing.raddf0. }
  rewrite -big_filter /nbm /I_sp1_2; case [seq i <- _ | _].
  { by rewrite big_nil GRing.addr0 GRing.oppr0 GRing.mul0r. }
  move=> h t; rewrite GRing.mulrC -GRing.mulrA /GRing.mul /= Rinv_l.
  { by rewrite Rmult_1_r GRing.addNr. }
  case size; [exact R1_neq_R0|].
  by move=> n'; apply Rgt_not_eq, Rlt_gt; rewrite -S_INR; apply/lt_0_INR/ltP. }
move=> [E [HE ->]] x.
set M := _ *m _.
replace (meval _ _)
with ((matrix.map_mx (meval x) M) ord0 ord0); [|by rewrite mxE].
replace R0 with ((@matrix.const_mx _ 1 1 R0) ord0 ord0); [|by rewrite mxE].
rewrite /M !map_mxM -map_trmx map_mxD; apply /Mle_scalar /posdef_semipos.
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

Definition r_ratBigQ := fun_hrel BigQ2rat.

Definition rat2R (q : rat) : R := ratr q.

Lemma rat2R_additive : additive rat2R.
Proof.
Admitted. (* Erik *)

Canonical rat2R_additive_struct := Additive rat2R_additive.

Lemma rat2R_multiplicative : multiplicative rat2R.
Proof.
Admitted. (* Erik *)

Canonical rat2R_rmorphism_struct := AddRMorphism rat2R_multiplicative.

Lemma bigQ2R_same (c : bigQ) :
  Q2R (BigQ.to_Q c) = rat2R (BigQ2rat c).
Proof.
Admitted. (* Erik *)

Fixpoint vars_ltn n (ap : abstr_poly) : bool :=
  match ap with
  | Const _ => true
  | Var i => (i < n)%N
  | Add p q | Sub p q | Mul p q => vars_ltn n p && vars_ltn n q
  | Pow p _ => vars_ltn n p
  end.

Lemma interp_poly_correct (l : seq R) (ap : abstr_poly) :
  let n := size l in (0 < n)%N -> vars_ltn n ap ->
  let n' := n.-1 in
  let p := interp_poly_ssr n' ap in
  interp_real l ap = (map_mpoly rat2R p).@[fun i : 'I_n'.+1 => nth R0 l i].
Proof.
move=> n Pn Hvars n'; set env := fun _ => _.
have Hn : n = n'.+1; [by move: Pn => /ltP; apply S_pred|].
elim: ap Hvars.
{ by move=> c _ /=; rewrite map_mpolyC ?GRing.raddf0 // mevalC bigQ2R_same. }
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

(* TODO: move above *)
Delimit Scope Q_scope with Qrat.

Lemma ZZtoQ_correct :
( forall m e,
  BigQ.to_Q (ZZtoQ m e) =
  (Qmake (BigZ.to_Z m) 1) * (Qpower (Qmake 2 1) (BigZ.to_Z e)) )%Qrat.
Proof.
Admitted. (* Erik *)

Definition F2BigQ (q : coqinterval_infnan.F.type) : bigQ :=
  match q with
  | Interval_specific_ops.Float m e => ZZtoQ m e
  | Interval_specific_ops.Fnan => 0%bigQ
  end.

(* TODO LATER:
   Generalize the formalization w.r.t
   [Variable fs : Float_round_up_infnan_spec.]
*)

Let fs := coqinterval_infnan.coqinterval_round_up_infnan.

Definition BigQ2FI := F2FI \o snd \o BigQ2F.
Definition FI2BigQ := F2BigQ \o coqinterval_infnan.FI_val.

Definition int2Z (n : int) : BinNums.Z :=
  match n with
  | Posz O => Z0
  | Posz n => Z.pos (Pos.of_nat n)
  | Negz n => Z.neg (Pos.of_nat n)
  end.

Definition rat2BigQ (q : rat) : bigQ :=
  let n := BigZ.of_Z (int2Z (numq q)) in
  let d := BigN.N_of_Z (int2Z (denq q)) in
  (n # d)%bigQ.

Definition rat2F := BigQ2FI \o rat2BigQ.
Definition F2rat := BigQ2rat \o FI2BigQ.

Lemma rat2F_correct :
  forall x0 : rat_comRing,
  @is_finite fs (rat2F x0) ->
  rat2R x0 <= @FI2F fs (rat2F x0).
Proof.
Admitted.  (* Erik *)

Lemma rat2R_F2rat :
 forall x0 : FI fs, rat2R (F2rat x0) = FI2F x0.
Proof.
Admitted.  (* Erik *)

Lemma max_l : forall x0 y0 : rat_comRing, rat2R x0 <= rat2R (Num.max x0 y0).
Proof.
Admitted. (* Erik *)

Lemma max_r : forall x0 y0 : rat_comRing, rat2R y0 <= rat2R (Num.max x0 y0).
Proof.
Admitted. (* Erik *)

(** ** Part 3: Parametricity *)

Section refinement_soscheck.

Variables (A : comRingType) (C : Type) (rAC : A -> C -> Type) (C2A : C -> A).
Hypothesis C2A_correct : forall c, rAC (C2A c) c.
Context `{!zero_of C, !one_of C, !opp_of C, !add_of C, !sub_of C, !mul_of C, !eq_of C}.
Context {n s : nat}.

Context `{!refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) (fun x y => x + -y)%R sub_op}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.

Instance zero_instMnm : zero_of 'X_{1..n} := mnm0.

Lemma param_check_base :
  refines (ReffmpolyC rAC ==> RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (nat_R_S_R nat_R_O_R) ==> eq)
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
  have : list_R
        (fun (x : 'X_{1.. n} * A) (y : seqmultinom * C) =>
         (refines Rseqmultinom x.1 y.1 * rAC x.2 y.2)%type) l l'.
  { rewrite /l /l'; apply refinesP; eapply refines_apply.
    { apply (refinesC_list_of_mpoly_eff (C2A:=C2A)), C2A_correct. }
    by rewrite refinesE. }
  apply all_R=> mc mc' rmc.
  move: (H mc.1 mc'.1); rewrite /smem_ssr /smem_eff /smem=>H'.
  rewrite H'; [by apply bool_Rxx|].
  move: rmc; rewrite refinesE=> rmc'; exact rmc'.1. }
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
    refines_apply_tc.
    admit.
    admit. }
  by move/S.mem_2=> H; apply S.mem_1, S.add_2. }
move/S.mem_2.
set mm := mul_monom_op _ _; case Em' : (m' == mm).
{ admit. }
move/S.add_3=>H; apply/orP; right; apply S.mem_1, H.
by move/mnmc_eq_seqP; rewrite eq_sym Em'.
Admitted.  (* Pierre *)

Context `{!max_of A}.
Context `{!max_of C}.

Lemma param_max_coeff :
  refines (ReffmpolyC (n:=n) rAC ==> rAC) max_coeff_ssr max_coeff_eff.
Proof.
Admitted.  (* Pierre *)

Context {fs : Float_round_up_infnan_spec}.
Let F := FI fs.
Context {F2A : F -> A}.  (* exact conversion for finite values *)
Context {A2F : A -> F}.  (* overapproximation *)
Context {F2C : F -> C}.  (* exact conversion for finite values *)
Context {C2F : C -> F}.  (* overapproximation *)
(* probably more hypotheses about these ones *)

(* Typeclasses eauto := debug. *)

Lemma param_soscheck :
  refines (ReffmpolyC rAC ==> RseqmxC (@Rseqmultinom n) (nat_Rxx s.+1) (*(nat_R_S_R nat_R_O_R)*) (nat_Rxx 1) ==> Rseqmx (nat_Rxx s.+1) (nat_Rxx s.+1) ==> eq)
    (soscheck_ssr (s:=s) (F2T:=F2A) (T2F:=A2F))
    (soscheck_eff (n:=n) (s:=s) (F2T:=F2C) (T2F:=C2F)).
Proof.
Admitted.  (* Pierre *)

End refinement_soscheck.

Section refinement_interp_poly.

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
 refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ)  *%R *%C.
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
  admit.  (* Erik *) }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  rewrite /GRing.add /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply (ReffmpolyC_mpoly_add_eff (C2A:=BigQ2rat)). }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  set p' := _ _ p; set q' := _ _ q.
  rewrite -[(_ - _)%R]/(mpoly_sub p' q').
  eapply refines_apply; first eapply refines_apply.
  { by apply (ReffmpolyC_mpoly_sub_eff (C2A:=BigQ2rat)). }
  { by apply Hp. }
  by apply Hq. }
{ move=> p Hp q Hq /= /andP [] Hlp Hlq.
  rewrite /GRing.mul /=.
  eapply refines_apply; first eapply refines_apply.
  { by apply (ReffmpolyC_mpoly_mul_eff (C2A:=BigQ2rat)). }
  { by apply Hp. }
  by apply Hq. }
move=> p Hp m /= Hlp.
eapply refines_apply; first eapply refines_apply.
{ by apply (ReffmpolyC_mpoly_exp_eff (C2A:=BigQ2rat)). }
{ by apply Hp. }
by rewrite refinesE.
Admitted.  (* Erik *)

End refinement_interp_poly.

(** ** Part 4: The final tactic *)

Ltac do_sdp :=
  match goal with
  | [ |- (?r >= 0)%Re ] => apply: Rle_ge; do_sdp
  | [ |- (0 <= ?r)%Re ] =>
    match get_poly r (@Datatypes.nil R) with
      (?ap, ?l) =>
      rewrite !Interval_missing.pow_powerRZ ;
      (*TODO: don't use change*)
      change (0 <= interp_real l ap)%Re ;
      rewrite interp_poly_correct; [|by vm_compute|by vm_compute]
    end
  end.

Lemma test_do_sdp (x : R) : (2 * x >= 0)%Re.
(* TODO/Erik: fix the parsing of integer constants *)
Fail do_sdp.
Abort.

Lemma test_do_sdp (x y : R) : (2 / 3 * x ^ 2 + y ^ 2 >= 0)%Re.
do_sdp.
match goal with
| [ |- 0 <= (map_mpoly _ (interp_poly_ssr ?qn ?qap)).@[_] ] =>
  set n := qn;
  set ap := qap
end.
compute in n.
pose bqp := interp_poly_eff n ap.
let l := eval vm_compute in (@id (seq (seq binnat.N * BigQ.t_)) (M.elements bqp)) in
let zQ := fresh "zQ" in soswitness of l in zQ.
pose s := (size zQ.1).-1.
compute in s.
pose z' := (map (fun x => [:: x]) zQ.1).
pose Qf := map (map F2FI) zQ.2.
compute in Qf.
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
apply (etrans (y:=@soscheck_eff 2 _ zero_bigQ one_bigQ opp_bigQ add_bigQ sub_bigQ mul_bigQ eq_bigQ max_bigQ 1 fs FI2BigQ BigQ2FI (interp_poly_eff n ap) z' Qf)).
2: by vm_compute.  (* TODO: on recalcule une deuxième fois interp_poly_eff, à éviter avec un remember ou quelque chose *)
apply refines_eq.
eapply refines_apply; first eapply refines_apply; first eapply refines_apply.
{ apply (param_soscheck (rAC := r_ratBigQ) (C2A := BigQ2rat)); by tc. }
{ by apply param_interp_poly; vm_compute.  (* ça aussi, c'est calculé deux fois *) }
rewrite refinesE (*!*) /za /z'.
eapply RseqmxC_spec_seqmx.
{ done. (* size check *) }
{ rewrite {2}[[seq [:: x0] | x0 <- zQ.1]](_: ?[x] = map_seqmx id ?x) //.
  eapply (map_seqmx_R (A_R := fun m m' => m = m' /\ size m' = n.+1)); last first.
  fold z'.
  have : all (all (fun s => size s == n.+1)) z' by compute.
  clear; elim: z'  =>[//|a l IHl] Hsz /=.
  constructor 2 =>//.
  elim: a Hsz =>[//|b r IHr] Hsz.
  constructor 2 =>//.
  split=>//.
  move/(all_nthP [::])/(_ 0%N)/(_ erefl)/(all_nthP [::])/(_ 0%N)/(_ erefl): Hsz.
  by move/eqP.
  apply: IHr.
  simpl in Hsz |- *.
  have {Hsz}/andP[/andP [_ Hsz0 Hsz1] ] := Hsz.
  by rewrite Hsz0 Hsz1.
  apply: IHl.
  simpl in Hsz.
  by have {Hsz}/andP[_ ->] := Hsz.
  (* ...we should move all this to a separate lemma... *)
  move=> m m' Hm; rewrite /spec /spec_id (proj1 Hm).
  apply refinesP.
  eapply refines_multinom_of_seqmultinom_val (* to rename! *).
  by rewrite (proj2 Hm).
}
by rewrite refinesE; eapply Rseqmx_spec_seqmx.
Qed.
