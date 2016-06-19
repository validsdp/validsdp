Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import binary64_infnan.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import gamma fsum.
Require Import binary64_infnan.

Require Import ZArith.
Require Import Flocq.Core.Fcore Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.

Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Require Import BigZ.
(* Print Module F. *)
Local Open Scope bigZ_scope.

Require Import mathcomp.algebra.matrix.
Require Import CoqEAL_refinements.seqmatrix.
Require Import CoqEAL_refinements.refinements.

Require Import CoqEAL_theory.hrel.

Import Refinements.Op.

Require Import iteri_ord.

Require Import cholesky_prog.

(* Notation ord_instN := (fun _ : nat => nat) (only parsing). *)
Notation seqmatrix' := ((fun (A : Type) (_ _ : nat) => seqmatrix A)) (only parsing).

Section inst_seqmx.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !div T, !mul T, !sqrt T}.

Fixpoint stilde_seqmx k c a b :=
  match k, a, b with
    | O, _, _ => c
    | S k, [::], _ => c
    | S k, _, [::] => c
    | S k, a1 :: a2, b1 :: b2 => stilde_seqmx k (c + (- (a1 * b1)))%C a2 b2
  end.

Global Instance dotmulB0_seqmx : dotmulB0_class T ord_instN (seqmatrix' T) :=
  fun n k c a b => stilde_seqmx k c (head [::] a) (head [::] b).

Fixpoint store_aux T s k (v : T) :=
  match s, k with
    | [::], _ => [::]
    | _ :: t, O => v :: t
    | h :: t, S k => h :: store_aux t k v
  end.

Fixpoint store_seqmx0 T m i j (v : T) :=
  match m, i with
    | [::], _ => [::]
    | h :: t, O => store_aux h j v :: t
    | h :: t, S i => h :: store_seqmx0 t i j v
  end.

Global Instance store_seqmx : store_class T ord_instN (seqmatrix' T) :=
  fun (_ _ : nat) M i j v => store_seqmx0 M i j v.

Context {n : nat}.

Global Instance I0_instN : I0_class ord_instN n.+1 := O.
Global Instance succ0_instN : succ0_class ord_instN n.+1 := S.
Global Instance nat_of_instN : nat_of_class ord_instN n.+1 := id.

Global Instance succ0_spec_instN : succ0_spec ord_instN n.+1.
Proof. done. Qed.

Global Instance I0_spec_instN : I0_spec ord_instN n.+1.
Proof. done. Qed.

Definition ytilded_seqmx :
  ord_instN n.+1 -> T -> seqmatrix' T 1%N n.+1 -> seqmatrix' T 1%N n.+1 -> T -> T :=
  ytilded (T := T).

Definition ytildes_seqmx : ord_instN n.+1 -> T -> seqmatrix' T 1%N n.+1 -> T :=
  ytildes.

Definition cholesky_seqmx (M : seqmatrix T) : seqmatrix T :=
  cholesky (T := T) (ord := ord_instN) (mx := seqmatrix') M.

Definition outer_loop_seqmx :
  seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 :=
  outer_loop.

Definition inner_loop_seqmx :
  ord_instN n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 -> seqmatrix' T n.+1 n.+1 :=
  inner_loop.

Lemma size_store_seqmx0 :
  forall s i j x,
  seq.size (@store_seqmx0 T s j i x) = seq.size s.
Proof.
move=> s i j x.
elim: s j => [|a s IHs] j; first by case: j.
case: j IHs => [|j] IHs //=.
by rewrite -(IHs j).
Qed.

Lemma size_inner_loop_seqmx :
  forall A j R, (nat_of j <= n.+1)%N ->
  seq.size R = n.+1 -> seq.size (inner_loop_seqmx j A R) = n.+1.
Proof.
move=> A j R Hj H0; rewrite /inner_loop_seqmx /inner_loop.
by apply iteri_ord_ind => // i0 s Hs /=; rewrite size_store_seqmx0.
Qed.

Lemma size_outer_loop_seqmx :
  forall A R, seq.size R = n.+1 -> seq.size (outer_loop_seqmx A R) = n.+1.
Proof.
move=> A R HRs; rewrite /outer_loop_seqmx /outer_loop.
set P := fun (i : nat) (s : seqmatrix T) => seq.size s = n.+1.
rewrite -/(P n.+1 _).
apply iteri_ord_ind => // i s Hle Hs /=; rewrite /P size_store_seqmx0.
by apply size_inner_loop_seqmx => //; apply ltnW.
Qed.

Lemma size_cholesky_seqmx M : seq.size M = n.+1 -> seq.size (cholesky_seqmx M) = n.+1.
Proof. apply size_outer_loop_seqmx. Qed.

Lemma size_store_aux :
  forall s i x,
  seq.size (@store_aux T s i x) = seq.size s.
Proof.
move=> s i x.
elim: s i => [|a s IHs] i; first by case: i.
case: i IHs => [|i] IHs //=.
by rewrite -(IHs i).
Qed.

Lemma size_nth_store_seqmx0 :
  forall s i j k x,
  seq.size (nth [::] (@store_seqmx0 T s j i x) k) = seq.size (nth [::] s k).
Proof.
move=> s i j k x.
elim: s j k => [|a s IHs] j k; first by case: j.
case: j IHs => [|j] IHs //=; case: k IHs => [|k] IHs //=.
by rewrite size_store_aux.
Qed.

Lemma size_nth_inner_loop_seqmx :
  forall A j k R, (nat_of j <= n.+1)%N ->
  seq.size (nth [::] R k) = n.+1 ->
  seq.size (nth [::] (inner_loop_seqmx j A R) k) = n.+1.
Proof.
move=> A j k R Hj; rewrite /inner_loop_seqmx /inner_loop.
apply iteri_ord_ind => //.
by move=> i0 s Hle Hs; rewrite size_nth_store_seqmx0.
Qed.

Lemma size_nth_outer_loop_seqmx :
  forall A R (i : nat), (i < n.+1)%N ->
  seq.size (nth [::] R i) = n.+1 ->
  seq.size (nth [::] (outer_loop_seqmx A R) i) = n.+1.
Proof.
move=> A R i Hi HRs; rewrite /outer_loop_seqmx /outer_loop.
set P := fun (i : nat) (s : seqmatrix T) => seq.size (nth [::] s i) = n.+1.
rewrite -/(P _ _).
apply iteri_ord_ind => // i0 s Hle Hs; rewrite /P size_nth_store_seqmx0.
by apply size_nth_inner_loop_seqmx => //; apply ltnW.
Qed.

Lemma size_nth_cholesky_seqmx M :
  forall i : nat, (i < n.+1)%N ->
  seq.size (nth [::] M i) = n.+1 ->
  seq.size (nth [::] (cholesky_seqmx M) i) = n.+1.
Proof. by move=> *; apply: size_nth_outer_loop_seqmx. Qed.

Context `{!eq T}.

Global Instance eq_seqmx : @heq nat (seqmatrix' T) :=
  fun _ _ : nat => eq_seq (eq_seq eq_op).

Global Instance transpose_seqmx : transpose_class (seqmatrix' T) :=
  fun _ _ : nat => @trseqmx T.

Context `{!leq T, !lt T}.

(* arithmetic operations with directed rounding *)
Context `{!addup_class T, !mulup_class T, !divup_class T}.
Context `{!nat2Fup_class T, !subdn_class T}.

Variable feps feta : T.

Variable is_finite : T -> bool.

Definition posdef_check_seqmx (M : seqmatrix T) : bool :=
  posdef_check (T := T) (ordT := ord_instN) (mx := seqmatrix')
    feps feta is_finite M.

Definition posdef_check_itv_seqmx (M : seqmatrix T) (r : T) : bool :=
  posdef_check_itv (T := T) (ordT := ord_instN) (mx := seqmatrix')
    feps feta is_finite M r.

Global Instance map_mx_seqmx : map_mx_class seqmatrix' :=
  fun T T' m n f s => map (map f) s.

Variables (F : Type) (F2FI : F -> T) (zeroF : F).

Definition posdef_check_F_seqmx (M : seqmatrix F) : bool :=
  let m := seq.size M in
  posdef_check_F (T := T) (ordT := ord_instN) (mx := seqmatrix')
    feps feta is_finite F2FI M.

Definition posdef_check_itv_F_seqmx (M : seqmatrix F) (r : F) : bool :=
  posdef_check_itv_F (T := T) (ordT := ord_instN) (mx := seqmatrix')
    feps feta is_finite F2FI M r.

End inst_seqmx.

Section Rseqmx_aux.
(* Aim: refinement proofs using seqmatrix.v *)

Context {A : Type}. (* {ordC : nat -> Type} {mxC : nat -> nat -> Type}. *)
Context `{!zero A}.

(** Version of Rseqmx_fun_of_seqmx not assuming zmodType *)
Instance Rseqmx_fun_of_seqmx' m n :
  param (Rseqmx ==> @Rord m ==> @Rord n ==> Logic.eq) (@matrix.fun_of_matrix A m n) (@fun_of_seqmx A _ m n).
Proof.
rewrite paramE => x a rxa i p <- j q <-.
rewrite /fun_of_seqmx.
by rewrite refines_nth_def.
Qed.

(** Version of Rseqmx_rowseqmx not assuming zmodType *)
Instance Rseqmx_rowseqmx' A m n :
  param (@Rord m ==> Rseqmx ==> Rseqmx) (@matrix.row A m n) (@rowseqmx A m n).
Proof.
rewrite paramE=> i p rip x a rxa.
rewrite /rowseqmx.
apply refines_seqmxP=> //.
case=> //= _.
rewrite refines_nth_col_size //.
rewrite refines_row_size.
by rewrite -rip.
case. case=> //= ? j.
rewrite !mxE.
rewrite -rip.
by rewrite refines_nth.
Qed.

End Rseqmx_aux.

Section data_refinement.

(* Concrete types *)
Context {C : Type}.
Local Notation ordC := (fun _ : nat => nat) (only parsing).
Local Notation mxC := (fun _ _ : nat => seqmatrix C) (only parsing).
Context `{!zero C, !one C, !add C, !opp C, (* !sub C, *) !mul C, !div C, !sqrt C}.
Context {n : nat}.

Instance : nat_of_class (fun _ => nat) n.+1 := id.

Local Notation ordA := ordinal (only parsing).
Local Notation mx := matrix (only parsing).

Local Notation RmxC := Rseqmx (only parsing). (* from seqmatrix.v *)

Local Notation RordC := Rord (only parsing).
Arguments RordC {n} _ _.

Lemma foldl_iteri_ord T T' n' f x x' s :
  (seq.size s = n'.+1)%N ->
  @foldl T T' f x s =
  iteri_ord (ord := ordinal) (n := n'.+1)
    (seq.size s) (fun i x => f x (nth x' s i)) x.
Proof.
move=> Hsize.
rewrite -[in LHS](take_size s).
eapply iteri_ord_ind =>//; rewrite ?Hsize // ?take0 //.
move=> i s' Hi Hs'.
rewrite -{}Hs'.
rewrite (take_nth x').
rewrite -[RHS]Rcomplements.foldl_rcons.
f_equal.
by rewrite Hsize.
Qed.
Arguments foldl_iteri_ord [_ _ _ _ _ x' _] _.

Context `{!leq C}.

Lemma param_store_aux n' : param (RmxC ==> RordC ==> Logic.eq ==> RmxC)
  (fun M j v => @store_ssr C 1%N n' M ord0 j v)
  (fun M j v =>
     match M with
     | [::] => [::]
     | l :: _ => [:: @store_aux C l j v] end).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => j j' param_j.
apply param_abstr => v v' pv; rewrite -(param_eq pv) => {v' pv}.
move: (@refines_row_size _ _ _ _ _ param_M); case_eq M' => // l l' Hl _.
apply /trivial_param /refines_seqmxP => //.
{ move=> i Hi.
  have Hi' : i = 0%N by move: Hi; case i.
  rewrite Hi' /= size_store_aux.
  change l with (nth [::] (l :: l') 0); rewrite -Hl -Hi'.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite Hi' Hl. }
move=> i j''; rewrite (ord_1_0 i) => /= {i}.
move: n' j' M M' param_M j param_j l l' Hl j''.
elim=> [|n' Hn'] j' M M' param_M j param_j l l' Hl j''; [by case j''|].
rewrite /store_seqmx mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hl /=.
case_eq l => [|x t] Hxt; [by rewrite /store_aux nth_nil|].
have St : seq.size t = n'.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (x :: t)); rewrite -Hxt.
  change l with (nth [::] (l :: l') (@ord0 n'.+1)); rewrite -Hl.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hl. }
have Hj' : (j' = j :> nat); [by move: param_j; rewrite paramE|rewrite Hj'].
case_eq (fintype.nat_of_ord j'') => /= [|j'''] Hj'''.
{ by case (fintype.nat_of_ord j). }
case_eq (fintype.nat_of_ord j) => [|j''''] Hj''''.
{ by apply set_nth_default; rewrite -Hj''' -(leq_add2r 1) !addn1 St. }
set M'' := \row_j nth zero0 t j : 'rV_n'.
specialize (Hn' j'''' M'' [:: t]).
have Hlj''' : (j''' < n')%N by rewrite -Hj''' -(leq_add2r 1) !addn1.
have Hlj'''' : (j'''' < n')%N by rewrite -Hj'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((store_ssr M'' ord0 (Ordinal Hlj'''') v) ord0 (Ordinal Hlj''')).
{ replace j''' with (fintype.nat_of_ord (Ordinal Hlj''')) at 2.
  { apply Hn' with (l' := [::]) => //.
    { rewrite paramE; apply refines_seqmxP => //; [by case|move=> i0 j0].
      by rewrite /M'' mxE (ord_1_0 i0) /=; apply set_nth_default; rewrite St. }
    by rewrite paramE /Rord; move: Hlj''''; case j''''. }
  by move: Hlj'''; case j'''. }
rewrite /store_ssr /M'' !mxE /= -(addn1 j''') -(addn1 j'''') eqn_add2r.
by rewrite (@set_nth_default _ _ (M ord0 j'')) // St.
Qed.

Lemma param_store_seqmx0 m n' : param (RmxC ==> RordC ==> RordC ==> Logic.eq ==> RmxC)
  (@store_ssr C m n') (@store_seqmx0 C).
Proof.
apply param_abstr => M M' param_M.
apply param_abstr => i i' param_i.
apply param_abstr => j j' param_j.
apply param_abstr => v v' param_v; rewrite -(param_eq param_v).
apply /trivial_param /refines_seqmxP => //.
{ rewrite size_store_seqmx0; move: param_M; apply refines_row_size. }
{ move=> i'' Hi''; rewrite size_nth_store_seqmx0.
  apply (@refines_nth_col_size _ _ _ _ _ param_M).
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
move: m M M' param_M i i' param_i.
elim=> [|m Hm] M M' param_M i i' param_i; [by case|move=> i'' j''].
rewrite /store_ssr mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
case_eq M' => [|l t] Hlt; [by rewrite !nth_nil|].
have Sl : seq.size l = n'.
{ change l with (nth [::] (l :: t) 0); rewrite -Hlt.
  by rewrite (@refines_nth_col_size _ _ _ _ _ param_M) // Hlt. }
have St : seq.size t = m.
{ apply /eqP; rewrite -(eqn_add2r 1) !addn1.
  change ((_ t).+1) with (seq.size (l :: t)); rewrite -Hlt.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
have Hi' : (i' = i :> nat); [by move: param_i; rewrite paramE|rewrite Hi'].
case_eq (fintype.nat_of_ord i'') => /= [|i'''] Hi'''.
{ case (fintype.nat_of_ord i) => /= [|_].
  { set M'' := \row_j M ord0 j.
    have param_M'' : param Rseqmx M'' [:: l].
    { rewrite paramE; apply /refines_seqmxP => //; [by case|].
      move=> i0 j0; rewrite (ord_1_0 i0) /= /M'' mxE.
      rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
      by apply set_nth_default; rewrite Sl. }
    have H0 := param_apply (param_store_aux n') param_M''.
    have HM'' := param_apply (param_apply H0 param_j) param_v.
    rewrite -(param_eq param_v) in HM'' => {H0}.
    replace (if _ then _ else _) with ((store_ssr M'' ord0 j v) ord0 j'').
    { change (store_aux l j' v) with (nth [::] [:: store_aux l j' v] 0).
      by rewrite (@refines_nth _ _ _ _ _ _ _ HM''). }
    rewrite /store_ssr /M'' !mxE -(@refines_nth _ _ _ _ _ _ _ param_M).
    rewrite Hlt /=; case (_ == _)%B => //.
    by apply set_nth_default; rewrite Sl. }
  by apply set_nth_default; rewrite Sl. }
have Slt : forall i, (i < m)%N -> seq.size (nth [::] t i) = n'.
{ move=> i0 Hi0; change (nth _ _ _) with (nth [::] (l :: t) i0.+1).
  rewrite -Hlt (@refines_nth_col_size _ _ _ _ _ param_M) => //.
  by rewrite (@refines_row_size _ _ _ _ _ param_M). }
case_eq (fintype.nat_of_ord i) => [|i''''] Hi''''.
{ by apply set_nth_default; rewrite Slt // -Hi'''; move: (ltn_ord i''). }
set M'' := \matrix_(i, j) M (lift ord0 (i : 'I_m)) j.
specialize (Hm M'' t).
have Hli''' : (i''' < m)%N by rewrite -Hi''' -(leq_add2r 1) !addn1.
have Hli'''' : (i'''' < m)%N by rewrite -Hi'''' -(leq_add2r 1) !addn1.
replace (if _ then _ else _) with
  ((store_ssr M'' (Ordinal Hli'''') j v) (Ordinal Hli''') j'').
{ replace i''' with (fintype.nat_of_ord (Ordinal Hli''')) at 2.
  { apply Hm.
    { rewrite paramE; apply refines_seqmxP => // i0 j0.
      rewrite /M'' mxE -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt.
      by apply set_nth_default => /=; rewrite Slt. }
    by rewrite paramE; move: Hli''''; case. }
  by move: Hli'''; case. }
rewrite /store_ssr /M'' !mxE /= -(addn1 i''') -(addn1 i'''') eqn_add2r.
rewrite -(@refines_nth _ _ _ _ _ _ _ param_M) Hlt /=.
by rewrite (@set_nth_default _ _ (M i'' j'')) // Slt.
Qed.

Global Instance param_store_seqmx :
  param (RmxC ==> RordC ==> RordC ==> Logic.eq ==> RmxC)
    (@store_ssr C n.+1 n.+1) (@store_seqmx0 C).
Proof. apply param_store_seqmx0. Qed.

Global Instance param_dotmulB0 :
  param (RordC ==> Logic.eq ==> RmxC ==> RmxC ==> Logic.eq)
  (@dotmulB0_ssr _ _ _ _ n.+1) (@dotmulB0 C ordC _ _ n.+1).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
rewrite paramE in param_c; rewrite -{c'}param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
rewrite paramE /dotmulB0 /= /dotmulB0_seqmx.
case: k param_k => [k Hk] param_k.
rewrite paramE /Rord /= in param_k; rewrite -{k'}param_k.
have := @refines_row_size _ _ _ _ _ param_a.
case Ea' : a' => [//|a'0 a'1]; case: a'1 Ea' =>//= Ea' _.
have := @refines_row_size _ _ _ _ _ param_b.
case Eb' : b' => [//|b'0 b'1]; case: b'1 Eb' =>//= Eb' _.
elim: n k Hk a b c a' b' a'0 param_a Ea' b'0 param_b Eb'
  => [|n' IHn'] k Hk a b c a' b' a'0 param_a Ea' b'0 param_b Eb'.
{ by rewrite /fsum_l2r_rec /=; case: k Hk. }
have := @refines_nth_col_size _ _ _ _ _ param_a 0.
rewrite refines_row_size Ea'; move/(_ erefl) => /=.
case Ea'0 : a'0 => [//|a'00 a'01] Ha'0; simpl in Ha'0.
have := @refines_nth_col_size _ _ _ _ _ param_b 0.
rewrite refines_row_size Eb'; move/(_ erefl) => /=.
case Eb'0 : b'0 => [//|b'00 b'01] Hb'0; simpl in Hb'0.
case: k Hk => //= k Hk; set cc := (c + - _)%C.
have Hk1 : (k < n'.+1)%N by rewrite -ltnS.
rewrite <-(IHn' k Hk1 (\row_(i < n'.+1) a ord0 (lift ord0 i))
                      (\row_(i < n'.+1) b ord0 (lift ord0 i)) cc
                      [:: behead a'0] [:: behead b'0]).
{ apply fsum_l2r_rec_eq => [|i]; rewrite !ffunE /cc.
  { repeat f_equal.
    { by rewrite -(refines_nth _ _ param_a) Ea' Ea'0 /= inordK. }
    by rewrite -(refines_nth _ _ param_b) Eb' Eb'0 /= inordK. }
  f_equal; apply f_equal2; rewrite mxE; f_equal; apply ord_inj.
  { rewrite inordK /=.
    { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
    rewrite /bump; case (0 <= i)%N => /=.
    { by rewrite add1n ltnS; apply (ltn_trans (ltn_ord _)). }
    by rewrite add0n; apply (ltn_trans (ltn_ord _)), leqW. }
  rewrite inordK /=.
  { by apply f_equal, sym_eq, inordK, (ltn_trans (ltn_ord _)). }
  rewrite /bump; case (0 <= i)%N => /=.
  { by rewrite add1n ltnS; apply (ltn_trans (ltn_ord _)). }
  by rewrite add0n; apply (ltn_trans (ltn_ord _)), leqW. }
{ rewrite paramE; apply/refines_seqmxP=> //.
  { move=> i; rewrite ltnS leqn0; move/eqP=> -> /=.
    by rewrite Ea'0 /=; apply eq_add_S. }
  move=> i j; rewrite !mxE (ord_1_0 i) /= -[in RHS](refines_nth _ _ param_a).
  rewrite nth_behead Ea'; f_equal. }
{ by rewrite Ea'0. }
{ rewrite paramE; apply/refines_seqmxP=> //.
  { move=> i; rewrite ltnS leqn0; move/eqP=> -> /=.
    by rewrite Eb'0 /=; apply eq_add_S. }
  move=> i j; rewrite !mxE (ord_1_0 i) /= -[in RHS](refines_nth _ _ param_b).
  rewrite nth_behead Eb'; f_equal. }
by rewrite Eb'0.
Qed.

Global Instance param_ytilded :
  param (RordC ==> Logic.eq ==> RmxC ==> RmxC ==> Logic.eq ==> Logic.eq)
  (ytilded_ssr (n' := n)) (ytilded_seqmx (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
eapply param_abstr => b b' param_b.
eapply param_abstr => bk bk' param_bk.
rewrite /ytilded_ssr /ytilded_seqmx /ytilded.
eapply param_apply; last by tc.
eapply param_apply.
rewrite paramE; by move=> ? ? h1 ? ? h2; rewrite h1 h2.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
eapply param_apply; last by tc.
by tc.
Qed.

Global Instance param_ytildes :
  param (RordC ==> Logic.eq ==> RmxC ==> Logic.eq)
  (ytildes_ssr (n' := n)) (ytildes_seqmx (n := n)).
Proof.
eapply param_abstr => k k' param_k.
eapply param_abstr => c c' param_c.
eapply param_abstr => a a' param_a.
rewrite /ytildes_ssr /ytildes_seqmx /ytildes.
eapply param_apply; last by tc.
by rewrite paramE; move=> ? ? ->.
Qed.

Lemma param_iteri_ord :
  forall T T', forall RT : T -> T' -> Prop,
  param ((fun j j' => j = j' /\ (j <= n.+1)%N) ==> (RordC ==> RT ==> RT) ==> RT
  ==> RT)
  (@iteri_ord _ n.+1 I0_ssr succ0_ssr T) (@iteri_ord _ n.+1 I0_instN succ0_instN T').
Proof.
move=> T T' RT.
apply param_abstr => j j' param_j.
rewrite paramE in param_j; destruct param_j as (Hj', Hj); rewrite -Hj'.
eapply param_abstr => f f' param_f.
apply param_abstr => x x'.
apply (iteri_ord_ind2 (M := T) (M' := T') (j := j)) => //.
move=> i i' s s' Hi Hi'.
apply param_apply.
have: param Rord i i'.
{ by move: Hi'; rewrite paramE /Rord /nat_of /nat_of_ord. }
by apply param_apply.
Qed.

Lemma param_inner_loop :
  param (RordC ==> RmxC ==> RmxC ==> RmxC)
  (inner_loop_ssr (n' := n)) (inner_loop_seqmx (n := n)).
Proof.
apply param_abstr => j j' param_j.
rewrite paramE /Rord in param_j; rewrite -param_j => {j' param_j}.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /inner_loop_ssr /inner_loop_seqmx /inner_loop.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ eapply param_apply; [by apply param_iteri_ord|].
  rewrite paramE; split; [by []|].
  rewrite /nat_of /nat_of_ord; apply ltnW, ltn_ord. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ eapply param_apply; [|exact param_i].
  eapply param_apply.
  { by eapply param_apply; [apply param_store_seqmx|]. }
  by rewrite paramE. }
eapply param_apply.
{ eapply param_apply.
  { eapply param_apply.
    { eapply param_apply.
      { by eapply param_apply; [apply param_ytilded|exact param_i]. }
      eapply param_apply.
      { eapply param_apply; [|exact param_i].
        by eapply param_apply; [apply Rseqmx_fun_of_seqmx'|apply param_A]. }
      by rewrite paramE. }
    eapply param_apply; [|exact param_s].
    eapply param_apply; [apply Rseqmx_rowseqmx'|exact param_i]. }
  eapply param_apply; [|exact param_s].
  eapply param_apply; [apply Rseqmx_rowseqmx'|by rewrite paramE]. }
do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_s].
Qed.

Lemma param_outer_loop :
  param (RmxC ==> RmxC ==> RmxC)
  (outer_loop_ssr (n' := n)) (outer_loop_seqmx (n := n)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => R Rs param_R.
rewrite /outer_loop_ssr /outer_loop_seqmx /outer_loop.
eapply param_apply; [|exact param_R].
eapply param_apply.
{ by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => j j' param_j.
apply param_abstr => s s' param_s.
have Hin : param Rseqmx (inner_loop_ssr j A s) (inner_loop_seqmx (n := n) j' As s').
{ eapply param_apply; [|exact param_s].
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_inner_loop|exact param_j]. }
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_j]).
  by eapply param_apply; [apply param_store_seqmx|]. }
eapply param_apply.
{ eapply param_apply.
  { eapply param_apply; [apply param_ytildes|exact param_j]. }
  do 2 (eapply param_apply; [|exact param_j]).
  eapply param_apply; [|exact param_A].
  apply Rseqmx_fun_of_seqmx'. }
eapply param_apply; [|apply Hin].
eapply param_apply; [apply Rseqmx_rowseqmx'|exact param_j].
Qed.

Global Instance param_cholesky :
  param (RmxC ==> RmxC) (cholesky_ssr (n' := n)) (cholesky_seqmx (n := n)).
Proof.
apply param_abstr => A As param_A.
rewrite /cholesky_ssr /cholesky_seqmx /cholesky.
do 2 (eapply param_apply; [|exact param_A]).
apply param_outer_loop.
Qed.

End data_refinement.

Section data_refinement'.

Variable fs : Float_round_up_infnan_spec.

Notation C := (FI fs) (only parsing).

Context {n : nat}.

Definition posdef_check5 := @posdef_check_ssr n fs.

Definition posdef_check_itv5 := @posdef_check_itv_ssr n fs.

Variables (F : Type) (F2FI : F -> FI fs).

Definition posdef_check_F5 := @posdef_check_F_ssr n fs F F2FI.

Lemma param_heq_op :
  param (Rseqmx ==> Rseqmx ==> Logic.eq)
  (@heq_op _ _ (@fheq fs) n.+1 n.+1)
  (@heq_op _ _ (@eq_seqmx C (@eq_instFI _)) n.+1 n.+1).
Proof.
apply param_abstr => A1 A1s param_A1.
apply param_abstr => A2 A2s param_A2.
have SA1s : seq.size A1s = n.+1 by move: param_A1; apply refines_row_size.
have SA2s : seq.size A2s = n.+1 by move: param_A2; apply refines_row_size.
have SzAs : seq.size (zip A1s A2s) = n.+1.
{ by rewrite size1_zip; rewrite SA1s; [|rewrite SA2s]. }
have SA1si : forall i : 'I_n.+1, seq.size (nth [::] A1s i) = n.+1.
{ move=> i; rewrite refines_nth_col_size // SA1s; apply ltn_ord. }
have SA2si : forall i : 'I_n.+1, seq.size (nth [::] A2s i) = n.+1.
{ move=> i; rewrite refines_nth_col_size // SA2s; apply ltn_ord. }
rewrite paramE /heq_op /fheq /eq_seqmx /eq_seqmx.
set b := eq_seq _ _ _.
apply /forallP; case_eq b => Hb.
{ move=> i; apply /forallP => j.
  move: Hb; rewrite /b eq_seqE; [|by rewrite SA1s SA2s].
  move /all_nthP => Ha.
  have Hi : (i < seq.size (zip A1s A2s))%N by rewrite SzAs; apply ltn_ord.
  specialize (Ha ([::], [::]) i Hi); move: Ha; rewrite eq_seqE.
  { move /all_nthP; set s := zip _ _; move=> Ha.
    have Hs' : seq.size s = n.+1.
    { rewrite /s nth_zip /=; [|by rewrite SA1s SA2s].
      by rewrite size1_zip; rewrite SA1si; [|rewrite SA2si]. }
    have Hj : (j < seq.size s)%N by rewrite Hs'; apply ltn_ord.
    specialize (Ha (A1 i j, A2 i j) j Hj).
    rewrite /s !nth_zip /= in Ha; first last.
    - by rewrite SA1s SA2s.
    - by rewrite SA1si SA2si.
    - by rewrite SA1s SA2s.
    rewrite (@refines_nth _ _ _ _ _ _ _ param_A1) in Ha.
    by rewrite (@refines_nth _ _ _ _ _ _ _ param_A2) in Ha. }
  by rewrite nth_zip /=; [rewrite SA1si SA2si|rewrite SA1s SA2s]. }
move=> Ha.
rewrite /b eq_seqE in Hb; [|by rewrite SA1s SA2s].
move: Hb; set al := all _ _; suff: al = true; [|rewrite /al].
{ by move=> Hal; rewrite Hal. }
apply /(all_nthP ([::], [::])) => i Hi; specialize (Ha (inord i)).
have Hii : (i = @inord n i)%N by rewrite inordK; [|rewrite SzAs in Hi].
rewrite nth_zip /=; [|by rewrite SA1s SA2s].
rewrite eq_seqE; [|by rewrite Hii SA1si SA2si].
apply /(all_nthP (FI0 fs, FI0 fs)) => j Hj.
have Hsz : seq.size (zip (nth [::] A1s i) (nth [::] A2s i)) = n.+1.
{ by rewrite size1_zip; rewrite Hii SA1si; [|rewrite SA2si]. }
have Hjj : (j = @inord n j)%N by rewrite inordK; rewrite Hsz in Hj.
rewrite Hii Hjj nth_zip /=; [|by rewrite SA1si SA2si].
rewrite (set_nth_default (A1 (inord i) (inord j)) (FI0 _)); [|by rewrite SA1si].
rewrite (set_nth_default (A2 (inord i) (inord j)) (FI0 _)); [|by rewrite SA2si].
by rewrite !refines_nth; move /forallP in Ha; specialize (Ha (inord j)).
Qed.

Lemma param_is_sym :
  param (Rseqmx ==> Logic.eq)
  (@is_sym _ _ n.+1 (@fheq fs) (@trmx C))
  (@is_sym _ _ n.+1 (@eq_seqmx C (@eq_instFI _)) transpose_seqmx).
Proof.
apply param_abstr => A As param_A.
rewrite /is_sym.
eapply param_apply; [|exact param_A].
eapply param_apply; [apply param_heq_op|].
eapply param_apply; [apply Rseqmx_trseqmx|exact param_A].
Qed.

Lemma param_foldl_diag T' :
  param (Logic.eq ==> Logic.eq ==> Rseqmx ==> Logic.eq)
  (@foldl_diag _ _ matrix (@fun_of_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n) T')
  (@foldl_diag _ _ seqmatrix' (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1
     (@I0_instN n) (@succ0_instN n) T').
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => x x' param_x.
apply param_abstr => A As param_A.
rewrite /foldl_diag.
eapply param_apply; [|exact param_x].
eapply param_apply.
{ rewrite -/iteri_ord_ssr.
  by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
rewrite !paramE in param_f, param_s; rewrite param_f param_s paramE.
apply f_equal, paramP; do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_all_diag :
  param (Logic.eq ==> Rseqmx ==> Logic.eq)
  (@all_diag _ _ _ (@fun_of_ssr C) n.+1 (@I0_ssr n) (@succ0_ssr n))
  (@all_diag _ _ seqmatrix'
     (@fun_of_seqmx C (@zero_instFI _)) n.+1 (@I0_instN n)
     (@succ0_instN n)).
Proof.
apply param_abstr => f f' param_f; rewrite paramE in param_f; rewrite param_f.
apply param_abstr => A As param_A.
rewrite /all_diag.
eapply param_apply; [|exact param_A].
do 2 (eapply param_apply; [|apply param_eq_refl]).
apply param_foldl_diag.
Qed.

Lemma param_max_diag :
  param (Rseqmx ==> Logic.eq)
  (@max_diag _ _ _ (FI0 fs)
     (@fun_of_ssr (FI fs)) n.+1 (@I0_ssr n) (@succ0_ssr n)
     (@leq_instFI fs))
  (@max_diag _ _ seqmatrix' (FI0 fs)
     (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1 (@I0_instN n)
     (@succ0_instN n) leq_instFI).
Proof.
apply param_abstr => A As param_A.
rewrite /max_diag.
eapply param_apply; [|exact param_A].
do 2 (eapply param_apply; [|apply param_eq_refl]).
apply param_foldl_diag.
Qed.

Lemma param_compute_c_aux :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@compute_c_aux _ _ _ (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs))
  (@compute_c_aux _ _ seqmatrix' (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1
     (@I0_instN n) (@succ0_instN n) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => x x' param_x.
rewrite paramE /compute_c_aux; apply f_equal2; apply f_equal; [|apply f_equal].
{ apply paramP; eapply param_apply; [|exact param_A].
  rewrite /tr_up; do 2 (eapply param_apply; [|apply param_eq_refl]).
  apply param_foldl_diag. }
by move: param_x; rewrite paramE.
Qed.

Lemma param_compute_c :
  param (Rseqmx ==> Logic.eq)
  (@compute_c (FI fs) _ _
     (@zero_instFI fs) (@one_instFI fs) (@opp_instFI fs)
     (@fun_of_ssr (FI fs)) n.+1 (@I0_ssr n)
     (@succ0_ssr n) (@leq_instFI fs) (@lt_instFI fs) (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs) (@is_finite fs))
  (@compute_c C _ seqmatrix'
     zero_instFI one_instFI opp_instFI
     (@fun_of_seqmx C zero_instFI) n.+1 (@I0_instN n)
     (@succ0_instN n) leq_instFI lt_instFI (@fiplus_up fs) (@fimult_up fs) (@fidiv_up fs)
     (float_of_nat_up fs) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /compute_c /C.
case (_ && _) => //.
set cc := compute_c_aux _ _ A _.
set cc' := compute_c_aux _ _ As _.
have Hcccc' : cc = cc'; [rewrite /cc /cc'|by rewrite Hcccc'].
apply paramP; apply (param_apply (R:=Logic.eq)).
{ eapply param_apply; [apply param_compute_c_aux|exact param_A]. }
eapply param_apply; [apply param_max_diag|exact param_A].
Qed.

Lemma param_map_diag :
  param ((Logic.eq ==> Logic.eq) ==> Rseqmx ==> Rseqmx)
  (@map_diag _ _ _
     (@fun_of_ssr (FI fs)) (@store_ssr (FI fs)) n.+1
     (@I0_ssr n) (@succ0_ssr n))
  (@map_diag _ _ seqmatrix'
     (@fun_of_seqmx C zero_instFI) (@store_seqmx C) n.+1
     (@I0_instN n) (@succ0_instN n)).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => A As param_A.
rewrite /map_diag.
eapply param_apply; [|exact param_A].
eapply param_apply.
{ by eapply param_apply; [apply param_iteri_ord|rewrite paramE]. }
apply param_abstr => i i' param_i.
apply param_abstr => s s' param_s.
eapply param_apply.
{ do 2 (eapply param_apply; [|exact param_i]).
  eapply param_apply; [apply param_store_seqmx|exact param_s]. }
eapply param_apply; first exact: param_f.
do 2 (eapply param_apply; [|exact param_i]).
eapply param_apply; [apply Rseqmx_fun_of_seqmx'|exact param_A].
Qed.

Lemma param_posdef_check :
  param (Rseqmx ==> Logic.eq)
  (@posdef_check_ssr n fs)
  (posdef_check_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /posdef_check_ssr /posdef_check_seqmx /posdef_check.
apply f_equal2; [apply f_equal2; [apply f_equal|]|].
{ by apply param_eq; eapply param_apply; [apply param_is_sym|exact param_A]. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set c := compute_c _ _ _ A.
set c' := compute_c _ _ _ As.
have Hcc' : c = c'; [|rewrite -Hcc'; case c => // {c c' Hcc'} c].
{ rewrite /c /c'; apply paramP.
  eapply param_apply; [apply param_compute_c|exact param_A]. }
set R := cholesky _; set Rs := cholesky _; apply paramP.
suff param_R : param Rseqmx R Rs; [|rewrite /R /Rs].
{ rewrite paramE; apply f_equal2; apply paramP.
  { eapply param_apply; [|exact param_R].
    eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
  rewrite /pos_diag; eapply param_apply; [|exact param_R].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set At := map_diag _ A; set Ats := map_diag _ As.
suff: param Rseqmx At Ats; [|rewrite /At /Ats].
{ rewrite -/cholesky_seqmx -/cholesky_ssr; apply param_apply, param_cholesky. }
eapply param_apply; [|exact param_A].
eapply param_apply; [exact param_map_diag|].
by eapply param_fun_eq; rewrite paramE.
Qed.

Lemma param_posdef_check_itv :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@posdef_check_itv_ssr n fs)
  (posdef_check_itv_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite paramE /posdef_check_itv_ssr /posdef_check_itv_seqmx /posdef_check_itv /posdef_check.
apply f_equal2=> //; apply f_equal2; [apply f_equal2; [apply f_equal2=> //|]|].
{ apply param_eq; eapply param_apply; first by apply param_is_sym.
  eapply param_apply; last by tc.
  eapply param_apply; first exact: param_map_diag.
  (* This could be simplified with a param lemma for sub_down *)
  rewrite paramE => a b Hab; repeat f_equal =>//. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply.
  eapply param_apply; [by apply param_all_diag|apply param_eq_refl].
  eapply param_apply; last exact: param_A.
  eapply param_apply; first eapply param_map_diag.
  rewrite paramE => a b Hab; repeat f_equal =>//. }
set c := compute_c _ _ _ (_ _ A).
set c' := compute_c _ _ _ (map_diag _ As).
have Hcc' : c = c'; [|rewrite -Hcc'; case c => // {c c' Hcc'} c].
{ rewrite /c /c'; apply paramP.
  eapply param_apply; [by apply param_compute_c|].
  eapply param_apply; last exact: param_A.
  eapply param_apply; first exact param_map_diag.
  rewrite paramE => a b Hab; repeat f_equal => //. }
set R := cholesky _; set Rs := cholesky _; apply paramP.
suff param_R : param Rseqmx R Rs; [|rewrite /R /Rs].
{ rewrite paramE; apply f_equal2; apply paramP.
  { eapply param_apply; [|exact param_R].
    eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
  rewrite /pos_diag; eapply param_apply; [|exact param_R].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set At := map_diag _ A; set Ats := map_diag _ As.
suff HA : param Rseqmx At Ats; [|rewrite /At /Ats].
{ rewrite -/cholesky_seqmx -/cholesky_ssr.
  eapply param_apply; first exact: param_cholesky.
  eapply param_apply; last exact: HA.
  eapply param_apply; [eapply param_map_diag|].
  by apply param_fun_eq, param_eq_refl. }
eapply param_apply; last exact: param_A.
eapply param_apply; first exact: param_map_diag.
rewrite paramE => a b Hab; repeat f_equal => //.
Qed.

(* Version of Rseqmx_map_seqmx not assuming identical input and return types for f *)
Lemma param_map_mx m n'' T T' :
  param (Logic.eq ==> Rseqmx ==> Rseqmx)
    (@map_mx_ssr T T' m n'')
    (@map_mx_seqmx T T' m n'').
Proof.
rewrite paramE => f _ <- x a rxa.
apply /refines_seqmxP=> [|i lt_im|i j].
{ by rewrite !sizeE. }
{ by rewrite (nth_map [::]) !sizeE. }
rewrite mxE (nth_map [::]) ?sizeE //.
by rewrite (nth_map (x i j)) ?sizeE // refines_nth.
Qed.

Lemma param_posdef_check_F :
  param (Rseqmx ==> Logic.eq)
  (@posdef_check_F_ssr n fs _ F2FI)
  (posdef_check_F_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
rewrite /posdef_check_F_ssr /posdef_check_F_seqmx /posdef_check_F.
eapply param_apply; [apply param_posdef_check|].
eapply param_apply; [|apply param_A].
eapply param_apply; [apply param_map_mx|apply param_eq_refl].
Qed.

Definition posdef_check_itv_F5 := @posdef_check_itv_F_ssr n fs _ F2FI.

Lemma param_posdef_check_itv_F :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (@posdef_check_itv_F_ssr n fs _ F2FI)
  (posdef_check_itv_F_seqmx (n:=n) (fieps fs) (fieta fs) (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite /posdef_check_itv_F_ssr /posdef_check_itv_F_seqmx /posdef_check_itv_F.
eapply param_apply; [|apply param_eq_refl].
eapply param_apply; [apply param_posdef_check_itv|].
eapply param_apply; [|apply param_A].
eapply param_apply; [apply param_map_mx|apply param_eq_refl].
Qed.

End data_refinement'.

Require Import BigQ.
Require Import coqinterval_infnan.
Require Import Interval.Interval_xreal.

Notation toR := (fun f => proj_val (F.toX f)).

Section test_CoqInterval.

Definition prec := 53%bigZ.

Local Notation T := (s_float BigZ.t_ BigZ.t_).

Instance add'' : add T := F.add rnd_NE prec.
Instance mul'' : mul T := F.mul rnd_NE prec.
Instance sqrt'' : sqrt T := F.sqrt rnd_NE prec.
Instance div'' : div T := F.div rnd_NE prec.
Instance opp'' : opp T := F.neg.
Instance zero'' : zero T := F.zero.
Instance one'' : one T := Float 1%bigZ 0%bigZ.

Instance eq'' : eq T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xeq => true
    | _ => false
  end.

Instance leq'' : leq T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xlt => true
    | Interval_xreal.Xeq => true
    | _ => false
  end.

Instance lt'' : lt T := fun x y =>
  match F.cmp x y with
    | Interval_xreal.Xlt => true
    | _ => false
  end.

Instance add1 : addup_class T := F.add rnd_UP prec.
Instance mul1 : mulup_class T := F.mul rnd_UP prec.
Instance div1 : divup_class T := F.div rnd_UP prec.

Definition feps : T := Float 1%bigZ (-53)%bigZ.
Definition feta : T := Float 1%bigZ (-1075)%bigZ.

Definition is_finite : T -> bool := F.real.

Instance float_of_nat_up'' : nat2Fup_class T :=
  fun n => iter n (fun x => add1 x one'') zero''.

Definition test_n'' : nat -> bool :=
  fun n => lt'' (mul1 (mul1 (float_of_nat_up'' 4%N)
                            (float_of_nat_up'' n.+1)) feps) one''.

Instance sub1 : subdn_class T := fun x y => opp'' (add1 y (opp'' x)).

Definition posdef_check4_coqinterval (M : seq (seq T)) : bool :=
  posdef_check_seqmx (T := T) (n := (seq.size M).-1)
    feps feta is_finite M.

Definition posdef_check_itv4_coqinterval (M : seq (seq T)) (r : T) : bool :=
  posdef_check_itv_seqmx (T := T) (n := (seq.size M).-1)
    feps feta is_finite M r.

End test_CoqInterval.

Section test_CoqInterval_F2FI.

Definition eps_inv := 9007199254740992%bigZ.  (* 2^53 *)

Lemma eps_inv_correct : (Z2R [eps_inv]%bigZ <= / eps fis)%Re.
Proof. by rewrite /= /flx64.eps /= Rinv_involutive; [right|lra]. Qed.

Definition F2FI_val (f : F.type) : F.type :=
  match f with
    | Interval_specific_ops.Fnan => Interval_specific_ops.Fnan
    | Interval_specific_ops.Float m e =>
      if (BigZ.abs m <? eps_inv)%bigZ then f else Interval_specific_ops.Fnan
  end.

Lemma F2FI_proof (x : F.type) : mantissa_bounded (F2FI_val x).
Proof.
unfold mantissa_bounded, x_bounded, F2FI_val.
case x; [now left|intros m e].
set (c := BigZ.ltb _ _); case_eq c; intro Hc; [right|now left].
exists (@F2R radix2 {| Fnum := [m]%bigZ; Fexp := [e]%bigZ |}).
{ unfold F.toX, FtoX, F.toF.
  assert (Hm := Bir.mantissa_sign_correct m); revert Hm.
  set (s := _ m); case_eq s; unfold Bir.MtoZ, F2R.
  { now intros Hs Hm; rewrite Hm; rewrite Rmult_0_l. }
  intros s' p Hp (Hm, Hm'); rewrite Hm; simpl; unfold Bir.EtoZ, FtoR, bpow.
  case [e]%bigZ.
  { now rewrite Rmult_1_r; case s'. }
  { now intro p'; rewrite Z2R_mult; case s'. }
  now intro p'; case s'. }
revert Hc; unfold c; clear c; rewrite BigZ.ltb_lt; intro Hm.
apply FLX_format_generic; [exact refl_equal|].
set (f := {| Fnum := _; Fexp := _ |}).
apply generic_format_F2R' with f; [reflexivity|intro Hf].
unfold canonic_exp, FLX_exp; rewrite Z.le_sub_le_add_r; apply ln_beta_le_bpow.
{ exact Hf. }
unfold F2R, f; simpl.
rewrite Rabs_mult; rewrite (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
apply (Rmult_lt_reg_r (bpow radix2 (-[e]%bigZ))); [now apply bpow_gt_0|].
rewrite Rmult_assoc; rewrite <- !bpow_plus.
replace (_ + - _)%Z with Z0 by ring; rewrite Rmult_1_r.
replace (_ + _)%Z with 53%Z by ring.
rewrite <- Z2R_abs; unfold bpow; apply Z2R_lt.
now revert Hm; unfold eps_inv, Z.pow_pos; simpl; rewrite <- BigZ.spec_abs.
Qed.

Definition F2FI (f : F.type) : FI := Build_FI _ (F2FI_proof f).

Lemma real_FtoX_toR f : F.real f -> F.toX f = Xreal (toR f).
Proof. by rewrite FtoX_real; rewrite /X_real; case: F.toX. Qed.

Lemma F2FI_correct (f : F.type) : finite (F2FI f) -> FI2F (F2FI f) = toR f :> R.
Proof.
case f => // m e.
rewrite /finite FtoX_real /FI2F.
case (FI_prop (F2FI (Float m e))) => Hf; [by rewrite Hf|].
destruct Hf as (r, Hr, Hr'); move=> HF /=.
suff: Xreal r = Xreal (proj_val (F.toX (Float m e))).
{ by move=> H; inversion H. }
by move: HF; rewrite -real_FtoX_toR // -Hr /F2FI /=; case (_ <? _).
Qed.

(* Erik: A little test to know which FI are in play:

Goal zero FI.
Fail by tc.
change FI with (float_infnan_spec.FI coqinterval_infnan.coqinterval_infnan).
tc.
Qed.
*)

(* Let's override FI for now...! *)
Local Notation FI := (float_infnan_spec.FI coqinterval_infnan.coqinterval_round_up_infnan).

Definition posdef_check4_coqinterval' (M : seq (seq FI)) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) M.

Definition posdef_check_F4_coqinterval' (M : seq (seq F.type)) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_F_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) F2FI M.

Definition posdef_check_itv4_coqinterval' (M : seq (seq FI)) (r : FI) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_itv_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) M r.

Definition posdef_check_itv_F4_coqinterval' (M : seq (seq F.type)) (r : F.type) : bool :=
  let m := seq.size M in
  all (fun l => seq.size l == m)%B M &&
  posdef_check_itv_F_seqmx (T := FI) (n := m.-1)
    fieps fieta
    (@float_infnan_spec.is_finite _) F2FI M r.

Definition BigQ2F (q : bigQ) : F.type * F.type :=
  match q with
  | BigQ.Qz m => let m0 := Interval_specific_ops.Float m Bir .exponent_zero in (m0, m0)
  | BigQ.Qq m n => let m0 := Interval_specific_ops.Float m Bir.exponent_zero in
                   let n0 := Interval_specific_ops.Float (BigZ.Pos n) Bir.exponent_zero in
                   (F.div rnd_DN prec m0 n0, F.div rnd_UP prec m0 n0)
  end.

Require Import Interval.Interval_missing.
Lemma toR_Float (m e : bigZ) : toR (Float m e) = (Z2R [m]%bigZ * bpow F.radix [e])%Re.
Proof.
rewrite /F.toX /F.toF /=.
have := Bir.mantissa_sign_correct m.
case E_m: (Bir.mantissa_sign m) => [|s m']; last case.
  by rewrite /Bir.MtoZ =>-> /=; rewrite Rsimpl.
rewrite /proj_val /FtoX.
rewrite (FtoR_split radix2 s (Bir.MtoP m') ((* Bir.EtoZ *) [e])).
rewrite /F2R /= /cond_Zopp => H1 H2; congr Rmult.
move: H1; case: (s) => H1.
by rewrite Pos2Z.opp_pos -H1.
by rewrite -H1.
Qed.

Definition test_posdef_check_itv (M : seq (seq F.type)) (r : bigQ) : bool :=
  posdef_check_itv_F4_coqinterval' M (snd (BigQ2F r)).

(* Remark: ultimately, we'll have to check that mat does not contain NaNs *)
(*
Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (@mx_of_seqmx_val _ R0 m m (map (map toR) mat)).
*)

Local Existing Instance zero''.

Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (matrix.map_mx toR (mx_of_seqmx_val m m mat)).

(* First attempt
Context `{mx : Type -> nat -> nat -> Type, !map_mx_class mx}.
Context `{!heq (mx FI)}.
Context `{!transpose_class (mx FI)}.
Context `{ordT : nat -> Type, !fun_of FI ordT (mx FI)}.
Context `{!row_class ordT (mx FI)}.
Typeclasses eauto := debug.
*)

Lemma posdef_check_F_correct_inst (A : seqmatrix F.type) :
  posdef_check_F4_coqinterval' A ->
  posdef_seqF A.
Proof.
case: A => [|A0 A1].
{ by move=> _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> Hmain.
eapply (@posdef_check_F_correct _ coqinterval_round_up_infnan).
{ by apply F2FI_correct. }
rewrite /posdef_check_F4_coqinterval' in Hmain.
have /andP[Hall Hmain'] := Hmain.
rewrite /is_true -Hmain' /posdef_check_F4_coqinterval'.
apply paramP.
eapply param_apply; first exact: param_posdef_check_F.
move/all_nthP in Hall.
apply/trivial_param/refines_seqmxP; rewrite -/(seq.size _); first done.
by move=> i Hi; move/(_ [::] i Hi)/eqP in Hall.
move=> [i Hi] j /=; rewrite !mxE.
apply: set_nth_default.
by move/(_ [::] i Hi)/eqP: Hall =>->.
Qed.

Ltac prove_posdef :=
  (by apply posdef_check_F_correct_inst; abstract (vm_cast_no_check (erefl true)))
  || fail "Numerical evaluation failed to prove positive-definiteness".

Definition posdef_itv_seqF (mat : seqmatrix F.type) (r : F.type) : Prop :=
  let m := seq.size mat in
  forall Xt : 'M_m, Xt^T = Xt ->
  Mabs (Xt - matrix.map_mx toR (@mx_of_seqmx_val _ zero'' m m mat))
    <=m: matrix.const_mx (toR r) ->
  posdef Xt.

Lemma posdef_check_itv_F_correct_inst (A : seqmatrix F.type) (r : F.type) :
  let m := seq.size A in
  posdef_check_itv_F4_coqinterval' A r ->
  posdef_itv_seqF A r.
Proof.
case: A => [|A0 A1].
{ by move=> _ _ Xt _ _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> m Hmain Xt.
set mA := mx_of_seqmx_val _ _ _.
change (proj_val (F.toX r)) with (toR r).
apply (posdef_check_itv_F_correct (fs := coqinterval_round_up_infnan) (F2FI := F2FI)).
- exact: F2FI_correct.
- rewrite /posdef_check_F4_coqinterval' in Hmain.
  have /andP[Hall Hmain'] := Hmain.
  rewrite /is_true -Hmain' /posdef_check_F4_coqinterval'.
  apply paramP.
  eapply param_apply; [eapply param_apply|exact: param_eq_refl].
  { exact: param_posdef_check_itv_F. }
  move/all_nthP in Hall.
  apply/trivial_param/refines_seqmxP; rewrite -/(seq.size _); first done.
  by move=> i Hi; move/(_ [::] i Hi)/eqP in Hall.
  move=> [i Hi] j /=; rewrite !mxE.
  apply: set_nth_default.
  by move/(_ [::] i Hi)/eqP: Hall =>->.
Qed.

Ltac prove_posdef_itv :=
  (by apply posdef_check_itv_F_correct_inst; abstract (vm_cast_no_check (erefl true)))
  || fail "Numerical evaluation failed to prove positive-definiteness".

Require Import testsuite.

Lemma test_m12 : posdef_seqF m12.
Time prove_posdef.
Qed.

Lemma test_m12_r : posdef_itv_seqF m12 (Float 1%bigZ (-10)%bigZ).
Time prove_posdef_itv.
Qed.

Goal True. idtac "test_posdef_check_CoqInterval". done. Qed.
Time Eval vm_compute in posdef_check4_coqinterval m12.
(* 6.3 s on Erik's laptop *)

Time Eval vm_compute in posdef_check_F4_coqinterval' m12.
(* 7.1 s on Erik's laptop *)

End test_CoqInterval_F2FI.
