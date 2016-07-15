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
    eval vm_compute in (BigQ.of_Q (Qmake ((if s then Zneg else Zpos) nn) dd)) in
  let get_integer s n :=
    let nn := get_positive n in
    eval vm_compute in (BigQ.of_Q (inject_Z ((if s then Zneg else Zpos) nn))) in
  match t with
  | 0%R => constr:(0%bigQ)
  | (-?n * /?d)%Re => get_rational_aux true n d
  | (?n * /?d)%Re => get_rational_aux false n d
  | (-?n / ?d)%Re => get_rational_aux true n d
  | (?n / ?d)%Re => get_rational_aux false n d
  | (-?n)%Re => get_integer true n
  | ?n => get_integer false n
  | _ => false
  end.

Lemma test_get_rational : (-1234 / 5678)%Re >= 0.
match goal with
[ |- (?r >= 0)%R ] => let t := get_rational r in idtac t
end.
Abort.

(* TODO: Move to misc *)
Local Coercion RMicromega.IQR : Q >-> R.
Local Coercion BigQ.to_Q : bigQ >-> Q.

Inductive abstr_poly :=
  (* | Const of Poly.t *)
  (* | Mult_scalar of Poly.Coeff.t * abstr_poly *)
  | Const of bigQ
  | Var of nat
  | Add of abstr_poly & abstr_poly
  | Sub of abstr_poly & abstr_poly
  | Mul of abstr_poly & abstr_poly
  | Pow of abstr_poly & positive
  (* | Compose of abstr_poly * abstr_poly list *).

Fixpoint eval_abstr_poly (vm : list R) (f : abstr_poly) {struct f} : R :=
  match f with
  | Const c => RMicromega.IQR (BigQ.to_Q c)
  | Add p q => Rplus (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Sub p q => Rminus (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Mul p q => Rmult (eval_abstr_poly vm p) (eval_abstr_poly vm q)
  | Pow p n => powerRZ (eval_abstr_poly vm p) (Z.pos n)
  | Var i => seq.nth R0 vm i
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
      | powerRZ ?a (Z.pos ?b) => aux_u' Pow a b
   (* | powerRZ ?a 0%Z => constr:(R1) [unwise to simplify here!] *)
      | pow ?a ?b =>
        let bb := eval vm_compute in (Pos.of_nat b) in aux_u' Pow a bb
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

Definition max_coeff (p : polyT) : T :=
  foldl (fun m mc => max m (max mc.2 (-mc.2)%C)) 0%C (list_of_poly p).

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
  check_base p z &&
  let r :=
    let p' :=
      let zp := map_mx polyX z in
      let Q' := map_mx (polyC \o F2T) Q in
      let p'm := (zp^T *m Q' *m zp)%HC in
      (* TODO: profiling pour voir si nécessaire d'améliorer la ligne
       * ci dessus (facteur 40 en Caml, mais peut être du même ordre de
       * grandeur que la décomposition de Cholesky) *)
      fun_of_matrix p'm I0 I0 in
    let pmp' := poly_sub_op p p' in
    max_coeff pmp' in
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

Definition max_coeff_eff : polyT -> T := max_coeff.

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

Context {n : nat} {T : comRingType}.

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

Definition max_coeff_ssr : polyT -> T := max_coeff.

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
Hypothesis T2R_additive : additive T2R.
Canonical T2R_additive_struct := Additive T2R_additive.
Hypothesis T2F_correct : forall x, is_finite (T2F x) -> T2R x <= FI2F (T2F x).
Hypothesis T2R_F2T : forall x, T2R (F2T x) = FI2F x.
Hypothesis max_l : forall x y, T2R x <= T2R (max x y).
Hypothesis max_r : forall x y, T2R y <= T2R (max x y).

Lemma check_base_correct (p : polyT) (z : 'cV_s.+1) : check_base p z ->
  forall m, m \in msupp p -> exists i j, (z i ord0 + z j ord0 == m)%MM.
Proof.
rewrite /check_base /list_of_poly /list_of_poly_ssr /sadd /sadd_ssr.
rewrite /smem /smem_ssr /sempty /sempty_ssr; set sm := iteri_ord _ _ _.
move/allP=> Hmem m Hsupp.
have : m \in sm.
{ apply (Hmem (m, p@_m)).
  by change (m, p@_m) with ((fun m => (m, p@_m)) m); apply map_f. }
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
rewrite /max_coeff /list_of_poly /list_of_poly_ssr.
have Hmax : forall x y, Rabs (T2R x) <= T2R (max y (max x (- x)%C)).
{ move=> x y; apply Rabs_le; split.
  { rewrite -(Ropp_involutive (T2R x)); apply Ropp_le_contravar.
    change (- (T2R x))%Re with (- (T2R x))%Ri.
    rewrite -GRing.raddfN /=.
    apply (Rle_trans _ _ _ (max_r _ _) (max_r _ _)). }
  apply (Rle_trans _ _ _ (max_l _ _) (max_r _ _)). }
generalize 0%C; elim (msupp _)=> [//|h t IH] z; move/orP; elim.
{ move/eqP-> => /=; set f := fun _ => _; set l := map _ _.
  move: (Hmax p@_h z); set z' := max z _; generalize z'.
  elim l => /= [//|h' l' IH' z'' Hz'']; apply IH'.
  apply (Rle_trans _ _ _ Hz''), max_l. }
by move=> Ht; apply IH.
Qed.

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
  forall x, 0 <= (map_mpoly T2R p).@[x].
Proof.
rewrite /soscheck_ssr /soscheck /fun_of_matrix /fun_of_ssr /map_mx /map_mx_ssr.
set zp := matrix.map_mx _ z.
set Q' := matrix.map_mx _ _.
set p' := _ (_ *m _) _ _.
set pmp' := poly_sub_op _ _.
set r := max_coeff _ .
pose zpr := matrix.map_mx [eta mpolyX real_ringType] z.
pose Q'r := matrix.map_mx (map_mpoly T2R) Q'.
pose map_mpolyC_R :=
  fun m : 'M_s.+1 => matrix.map_mx [eta mpolyC n (R:=real_ringType)] m.
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
  set M := Q'r + _.
  pose F2 := fun i : 'I_s.+1 =>
    \big[+%R/0]_(j < s.+1) (zpr j ord0 * M j i * zpr i ord0).
  rewrite (eq_bigr F2);
    [|by move=> i _; rewrite mxE /F2 big_distrl /=;
      apply eq_bigr=> j _; rewrite mxE].
  rewrite {F2} pair_bigA /=.
  have -> : M = matrix.map_mx [eta mpolyC n (R:=real_ringType)]
                  (matrix.map_mx (T2R \o F2T) Q + E).
  { apply/matrixP=> i j.
    by rewrite !mxE mpolyCD (map_mpolyC _ _ _ (GRing.raddf0 _)). }
  move {M}; set M := matrix.map_mx _ _.
  rewrite (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  set F2 := fun ij : 'I_s.+1 * 'I_s.+1 =>
              ((z ij.2 ord0 + z ij.1 ord0)%MM == m)%:R *
              (matrix.map_mx (T2R \o F2T) Q + E) ij.2 ij.1.
  rewrite (eq_bigr F2); last first.
  { move=> ij _.
    rewrite (GRing.mulrC (zpr _ _)) -GRing.mulrA mxE mcoeffCM.
    by rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX. }
  rewrite {}/F2 (bigID (fun ij => zij ij.2 ij.1 == m)) /= GRing.addrC.
  rewrite big1; last first.
  { by move=> ij; move/negbTE => ->; rewrite GRing.mul0r. }
  rewrite GRing.add0r.
  set F2 := fun i : 'I_s.+1 * 'I_s.+1 => T2R (F2T (Q i.2 i.1)) + E i.2 i.1.
  rewrite (eq_bigr F2); last first; [|rewrite {}/F2].
  { by move=> ij Hij; rewrite Hij GRing.mul1r 2!mxE. }
  rewrite big_split /= GRing.addrC.
  pose nbm := size [seq ij <- index_enum I_sp1_2 | zij ij.2 ij.1 == m].
  set F2 := fun i : 'I_s.+1 * 'I_s.+1 => (T2R p@_m - T2R p'@_m) * / INR nbm.
  rewrite (eq_bigr F2); last first; [|rewrite {}/F2].
  { move=> ij Hij; rewrite mxE /Rdiv; apply f_equal2.
    { by move: Hij; move/eqP => <-; rewrite mcoeffB GRing.raddfB /=. }
    by rewrite /nbij; move: Hij; move/eqP->. }
  rewrite misc.big_sum_pred_const -/nbm GRing.mulrDl GRing.mulrDr -GRing.addrA.
  rewrite -{1}(GRing.addr0 (T2R _)); f_equal.
  { rewrite GRing.mulrC -GRing.mulrA; case_eq (m \in msupp p).
    { move=> Hm; move: (check_base_correct _ _ Hbase _ Hm).
      move=> [i [j {Hm}Hm]]; rewrite /GRing.mul /=; field.
      apply Rgt_not_eq, Rlt_gt; change R0 with (INR 0); apply lt_INR.
      rewrite /nbm filter_index_enum; rewrite <-cardE.
      by apply/ltP/card_gt0P; exists (j, i); rewrite /in_mem /=. }
    by rewrite mcoeff_msupp; move/eqP->; rewrite GRing.raddf0 GRing.mul0r. }
  rewrite /p' mxE.
  pose F2 := fun i : 'I_s.+1 =>
    \big[+%R/0]_(j < s.+1) (zp j ord0 * Q' j i * zp i ord0).
  rewrite (eq_bigr F2);
    [|by move=> i _; rewrite mxE /F2 big_distrl /=;
      apply eq_bigr=> j _; rewrite mxE].
  rewrite {F2} pair_bigA /= (big_morph _ (GRing.raddfD _) (mcoeff0 _ _)) /=.
  set F2 := fun ij : 'I_s.+1 * 'I_s.+1 =>
              ((z ij.2 ord0 + z ij.1 ord0)%MM == m)%:R * F2T (Q ij.2 ij.1).
  rewrite (eq_bigr F2); last first; [|rewrite {}/F2].
  { move=> ij _.
    rewrite (GRing.mulrC (zp _ _)) -GRing.mulrA mxE mcoeffCM.
    by rewrite GRing.mulrC 2!mxE -mpolyXD mcoeffX. }
  rewrite GRing.raddf_sum /= (bigID (fun ij => zij ij.2 ij.1 == m)) /=.
  set F2 := fun ij : 'I_s.+1 * 'I_s.+1 => T2R (F2T (Q ij.2 ij.1)).
  rewrite (eq_bigr F2); [rewrite {}/F2|by move=> ij ->; rewrite GRing.mul1r].
  set F3 := bigop _ _ _; rewrite big1; last first; [|rewrite {}/F3 GRing.addr0].
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
    rewrite !mxE /= (map_mpolyC _ _ _ (GRing.raddf0 _)) mevalC].
apply (posdef_check_itv_correct Hpcheck).
apply Mle_trans with (Mabs E).
{ by right; rewrite !mxE /=; f_equal; rewrite T2R_F2T GRing.addrC GRing.addKr. }
apply (Mle_trans HE) => i j; rewrite !mxE.
by apply T2F_correct; move: Hpcheck; move/andP; elim.
Qed.

End theory_soscheck.

(** ** Part 3: Parametricity *)

Section refinement_soscheck.

Variables (A : comRingType) (C : Type) (rAC : A -> C -> Prop).
Context {n s : nat}.

Lemma param_check_base :
  param (ReffmpolyA rAC ==> RseqmxA (@Rseqmultinom n) ==> Logic.eq)
    (check_base_ssr (s:=s)) (check_base_eff (s:=s)).
Admitted.

Check max_coeff_ssr.

Context `{!max_class A}.
Context `{!zero C, !one C, !opp C, !add C, !sub C, !mul C}.
Context `{!max_class C}.

Lemma param_max_coeff :
  param (ReffmpolyA (n:=n) rAC ==> rAC) max_coeff_ssr max_coeff_eff.
Admitted.

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

Definition F2BigQ (q : coqinterval_infnan.F.type) : bigQ :=
  match q with
  | Interval_specific_ops.Float m e => ZZtoQ m e
  | Interval_specific_ops.Fnan => 0%bigQ
  end.
