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

Class sqrt T := sqrt_op : T -> T.

Class store_class A I B :=
  store : forall (m n : nat), B m n -> I m -> I n -> A -> B m n.

Class dotmulB0_class A I B :=
  dotmulB0 : forall n : nat, I n -> A -> B 1%nat n -> B 1%nat n -> A.

Class map_mx_class mx := map_mx :
  forall {T T'} {m n : nat},
  (T -> T') -> mx T m n -> mx T' m n.

Require Import cholesky_prog.

Section generic_algos.
Context {T : Type} {ordT : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !mul T, !div T, !sqrt T}.
Context `{!fun_of T ordT (mx T), !row_class ordT (mx T), !store_class T ordT (mx T), !dotmulB0_class T ordT (mx T)}.
Context {n : nat}.
Context `{!I0_class ordT n, !succ0_class ordT n, !nat_of_class ordT n}.

Local Open Scope nat_scope.

Context `{!heq (mx T)}.
Context `{!transpose_class (mx T)}.

Definition is_sym (A : mx T n n) : bool := (A^T == A)%HC.

Definition foldl_diag T' f (z : T') A :=
  iteri_ord n (fun i z => f z (fun_of_matrix A i i)) z.

Definition all_diag f A := foldl_diag (fun b c => b && f c) true A.

Context `{!leq T}.

Definition noneg_diag := all_diag (fun x => 0 <= x)%C.

Context `{!lt T}.

Definition pos_diag := all_diag (fun x => 0 < x)%C.

Definition max x y := if (x <= y)%C then y else x.

Definition max_diag A := foldl_diag max 0%C A.

Definition map_diag f A :=
  iteri_ord n (fun i A' => store A' i i (f (fun_of_matrix A i i))) A.

Section directed_rounding.

(* upward rounded operations *)
Variable add1 mul1 div1 : T -> T -> T.
(* @Érik: idéalement, on aimerait utiliser des typeclasses,
   mais je galère trop, on verra ça ensemble. *)

Definition tr_up A := foldl_diag add1 0%C A.

(* get a float overapprox of n *)
Definition float_of_nat_up n := iter n (fun x => add1 x 1%C) 0%C.

(* [compute_c n A maxdiag] overapproximates
   /2 gamma (2 (n + 1)) \tr A + 4 eta n * (2 (n + 1) + maxdiag) *)
Definition compute_c_aux (eps eta : T)  (* overapproximations of eps and eta *)
  (A : mx T n n) (maxdiag : T) : T :=
let np1 := float_of_nat_up n.+1 in
let dnp1 := float_of_nat_up (2 * n.+1)%N in
let tnp1 := mul1 dnp1 eps in
let g := div1 (mul1 np1 eps) (- (add1 tnp1 (-1%C)))%C in
add1
  (mul1 g (tr_up A))
  (mul1
    (mul1 (mul1 (float_of_nat_up 4) eta) (float_of_nat_up n))
    (add1 dnp1 maxdiag)).

Definition compute_c (is_finite : T -> bool) (eps eta : T) (A : mx T n n) :
  option T :=
  let nem1 := add1 (mul1 ((float_of_nat_up (2 * n.+1)%N)) eps) (-1%C)%C in
  if is_finite nem1 && (nem1 < 0)%C then
    let c := compute_c_aux eps eta A (max_diag A) in
    if is_finite c then Some c else None
  else None.

(* subtraction rounded downward *)
Definition sub_down x y := (- (add1 y (- x)%C))%C.

Definition posdef_check
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mx T n n) : bool :=
test_n n && is_sym A && noneg_diag A &&
  (match compute_c is_finite eps eta A with
     | None => false
     | Some c =>
       let A' := map_diag (fun x => sub_down x c) A in
       let R := cholesky A' in
       all_diag is_finite R && pos_diag R
   end).

Definition posdef_check_itv
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mx T n n) (r : T) : bool :=
is_finite r && (0 <= r)%C &&
  let nm := mul1 (float_of_nat_up n) r in
  let A' := map_diag (fun x => sub_down x nm) A in
  posdef_check eps eta is_finite test_n A'.

Context `{!map_mx_class mx}.

Variables (F : Type) (F2FI : F -> T).

Definition posdef_check_F
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mx F n n) : bool :=
  posdef_check eps eta is_finite test_n (map_mx F2FI A).

Definition posdef_check_itv_F
  (* overapproximations of eps and eta *)
  (eps eta : T)
  (is_finite : T -> bool)
  (* check that n is not too large *)
  (test_n : nat -> bool)
  (* matrix to check *)
  (A : mx F n n) (r : F) : bool :=
  posdef_check_itv eps eta is_finite test_n (map_mx F2FI A) (F2FI r).

End directed_rounding.

End generic_algos.

Section inst_ssr_matrix.

Context {T : Type}.
Context `{!zero T, !one T, !add T, !opp T, (* !sub T, *) !div T, !mul T, !sqrt T}.

Context {n' : nat}.
Let n := n'.+1.

Section proof.

Definition ssr_all_diag : (T -> bool) -> 'M[T]_n -> bool :=
  @all_diag _ _ _ fun_of_ssr _ _ succ0_ssr.

Lemma all_diag_correct f (A : 'M[T]_n) :
  ssr_all_diag f A = true -> forall i, f (A i i) = true.
Proof.
move=> Had i; move: (ltn_ord i) Had.
set P := fun i b => b = true -> f (A i i) = true.
rewrite -/(P i (ssr_all_diag f A)).
rewrite -/(nat_of _); apply iteri_ord_ind_strong_cases.
{ move=> j' s Hj' H j'' Hj''.
  by rewrite /P Bool.andb_true_iff => Hb; elim Hb => Hb' _; apply H. }
by move=> j' s Hj' H; rewrite /P Bool.andb_true_iff => Hb; elim Hb.
Qed.

Definition ssr_foldl_diag (T' : Type) : (T' -> T -> T') -> T' -> 'M[T]_n -> T' :=
  @foldl_diag _ _ _ fun_of_ssr _ _ succ0_ssr T'.

Lemma foldl_diag_correct (T' : Type) (f : T' -> T -> T') (z : T') (A : 'M[T]_n) :
  forall (P : nat -> T' -> Type),
  (forall (i : 'I_n) z, P i z -> P i.+1 (f z (A i i))) ->
  P O z -> P n (ssr_foldl_diag f z A).
Proof.
move=> P Hind; rewrite /ssr_foldl_diag /foldl_diag.
apply iteri_ord_ind => // i s Hi HPi; apply Hind.
by move: HPi; rewrite /nat_of /nat_of_ord.
Qed.

Definition ssr_map_diag : (T -> T) -> 'M[T]_n -> 'M[T]_n :=
  @map_diag _ _ _ fun_of_ssr _ _ _ succ0_ssr.

Lemma map_diag_correct_ndiag f (A : 'M[T]_n) :
  forall i j : 'I_n, i <> j -> (ssr_map_diag f A) i j = A i j.
Proof.
move=> i j Hij.
rewrite /ssr_map_diag /map_diag /iteri_ord; set f' := fun _ _ => _.
suff H : forall k R i',
           (matrix.fun_of_matrix (@iteri_ord_rec _ _ succ0_ssr _ k i' f' R) i j
            = R i j) => //; elim => // k IHk R i' /=.
rewrite IHk; case (ltnP i' j) => Hi'j; [by rewrite store_ssr_gt2|].
case (ltnP i j) => Hij'.
{ by rewrite store_ssr_lt1 //; apply (leq_trans Hij'). }
case (ltnP i' i) => Hi'i; [by rewrite store_ssr_gt1|].
rewrite store_ssr_lt2 //; move: Hi'i; apply leq_trans.
case (leqP i j) => Hij'' //.
by casetype False; apply Hij, ord_inj, anti_leq; rewrite Hij''.
Qed.

Lemma map_diag_correct_diag f (A : 'M[T]_n) :
  forall i, (ssr_map_diag f A) i i = f (A i i).
Proof.
move=> i; rewrite /ssr_map_diag /map_diag.
set f' := fun _ _ => _.
set P := fun i s => s i i = f (A i i); rewrite -/(P i _).
apply iteri_ord_ind_strong_cases with (i0 := i) => //.
{ move=> j s Hj Hind j' Hj'.
  rewrite /P /f' store_ssr_lt1 //; apply Hind => //; apply ltn_ord. }
{ move=> j s Hj Hind; rewrite /P /f' store_ssr_eq //. }
apply ltn_ord.
Qed.

End proof.

End inst_ssr_matrix.

Section proof_inst_ssr_matrix_float_infnan.

Context {n' : nat}.
Let n := n'.+1.

Require Import float_infnan_spec real_matrix cholesky_infnan.

Variable fs : Float_infnan_spec.

(* REMARK: Already defined in cholesky_prog.v ...
Instance add_instFI : add (FI fs) := @fiplus fs.
Instance mul_instFI : mul (FI fs) := @fimult fs.
Instance sqrt_instFI : sqrt (FI fs) := @fisqrt fs.
Instance div_instFI : div (FI fs) := @fidiv fs.
Instance opp_instFI : opp (FI fs) := @fiopp fs.
Instance zero_instFI : zero (FI fs) := @FI0 fs.
Instance one_instFI : one (FI fs) := @FI1 fs.
*)

Variable eps_inv : BigZ.t_.

(* Example:
 * Definition eps_inv := Eval vm_compute in (2^53)%bigZ. *)

Hypothesis eps_inv_spec : Z2R [eps_inv] <= / eps (fis fs).

Definition test_n n'' : bool :=
  (4 * (BigZ.of_Z (Z.of_nat n'') + 1) <? eps_inv)%bigZ.

Lemma test_n_correct : test_n n = true ->
  4 * INR n.+1 * eps (fis fs) < 1.
Proof.
unfold test_n; intro H.
case (Req_dec (eps (fis fs)) 0); intro Heps; [rewrite Heps; lra|].
rewrite <- (Rinv_l _ Heps) at 5.
apply Rmult_lt_compat_r; [assert (H' := eps_pos (fis fs)); lra|].
revert eps_inv_spec; apply Rlt_le_trans.
rewrite S_INR INR_IZR_INZ -Z2R_IZR.
change 4 with (Z2R 4); rewrite -(Z2R_plus _ 1) -Z2R_mult.
apply Z2R_lt; revert H; rewrite Zlt_is_lt_bool BigZ.spec_ltb.
by rewrite BigZ.spec_mul BigZ.spec_add BigZ.spec_of_Z.
Qed.

Global Instance fheq : @heq nat (matrix (FI fs)) :=
  fun n1 n2 a b => [forall i, [forall j, fieq (a i j) (b i j)]].

Global Instance ftrmx : transpose_class (matrix (FI fs)) := @matrix.trmx (FI fs).

Lemma is_sym_correct_aux (A : 'M[FI fs]_n) :
  is_sym A = true -> forall i j, fieq (A^T i j) (A i j).
Proof. by move=> H i j; move/forallP/(_ i)/forallP/(_ j) in H. Qed.

Lemma is_sym_correct (A : 'M[FI fs]_n) :
  is_sym A = true -> cholesky.MF2R (MFI2F A^T) = cholesky.MF2R (MFI2F A).
Proof.
move/is_sym_correct_aux=> H; apply /matrixP=> i j.
move: (H i j); rewrite !mxE; apply fieq_spec.
Qed.

Definition gen_max_diag (A : 'M[FI fs]_n) : FI fs :=
  @max_diag _ _ _ _ fun_of_ssr _ I0_ssr succ0_ssr _ A.

Lemma max_diag_correct (A : 'M[FI fs]_n) : (forall i, finite (A i i)) ->
  forall i, (MFI2F A) i i <= FI2F (gen_max_diag A).
Proof.
move=> HF.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
move=> i; move: i (ltn_ord i).
set P' := fun j (s : FI fs) => forall (i : 'I_n), (i < j)%N ->
  (MFI2F A) i i <= FI2F s; rewrite -/(P' _ _).
suff : (finite (ssr_foldl_diag f (FI0 fs) A)
        /\ P' n (ssr_foldl_diag f (FI0 fs) A)).
{ by move=> H; elim H. }
set P := fun j s => finite s /\ P' j s; rewrite -/(P _ _).
apply foldl_diag_correct; rewrite /P /P'.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by apply fimax_spec_f. }
  move=> j Hj; case (ltnP j i) => Hji.
  { rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ (Hind' _ Hji)).
    by apply fimax_spec_lel. }
  have H' : j = i.
  { by apply ord_inj, anti_leq; rewrite Hji Bool.andb_true_r. }
  by rewrite H' /f -/(fimax _ _) mxE; apply fimax_spec_ler. }
by split; [apply finite0|].
Qed.

Lemma max_diag_pos (A : 'M[FI fs]_n) : (forall i, finite (A i i)) ->
  0 <= FI2F (gen_max_diag A).
Proof.
move=> HF.
set f := fun m c : FI fs => if (m <= c)%C then c else m.
suff : (finite (ssr_foldl_diag f (FI0 fs) A)
        /\ 0 <= FI2F (ssr_foldl_diag f (FI0 fs) A)).
{ by move=> H; elim H. }
set P := fun (j : nat) s => @finite fs s /\ 0 <= FI2F s.
apply foldl_diag_correct with (P0 := P); rewrite /P.
{ move=> i z Hind; destruct Hind as (Hind, Hind'); split.
  { by case (fimax_spec_eq z (A i i)) => H; rewrite /f -/(fimax _ _) H. }
  by rewrite /f -/(fimax _ _); apply (Rle_trans _ _ _ Hind'), fimax_spec_lel. }
by split; [apply finite0|rewrite FI2F0; right].
Qed.

(* addition with upward rounding *)
Variable add_up : FI fs -> FI fs -> FI fs.

Hypothesis add_up_spec : forall x y, finite (add_up x y) ->
  (FI2F x + FI2F y <= FI2F (add_up x y))%R.
Hypothesis add_up_spec_fl : forall x y, finite (add_up x y) -> finite x.
Hypothesis add_up_spec_fr : forall x y, finite (add_up x y) -> finite y.

Definition gen_tr_up (n : nat) (A : 'M[FI fs]_n.+1) : FI fs :=
  @tr_up _ _ _ _ fun_of_ssr _ I0_ssr succ0_ssr add_up A.

Lemma tr_up_correct (A : 'M[FI fs]_n) : finite (gen_tr_up A) ->
  \tr (cholesky.MF2R (MFI2F A)) <= FI2F (gen_tr_up A).
Proof.
rewrite /gen_tr_up /tr_up -/(ssr_foldl_diag _ _ _).
replace (\tr _) with (\sum_(i < n) (FI2F (A (inord i) (inord i)) : R));
  [|by apply eq_big => // i _; rewrite !mxE inord_val].
set P := fun j (s : FI fs) => finite s ->
  (\sum_(i < j) (FI2F (A (inord i) (inord i)) : R)) <= FI2F s.
rewrite -/(P _ _); apply foldl_diag_correct; rewrite /P.
{ move=> i z Hind Fa; move: (add_up_spec Fa); apply Rle_trans.
  rewrite big_ord_recr /= /GRing.add /= inord_val.
  apply Rplus_le_compat_r, Hind, (add_up_spec_fl Fa). }
move=> _; rewrite big_ord0 FI2F0; apply Rle_refl.
Qed.

Definition gen_float_of_nat_up : nat -> FI fs := float_of_nat_up add_up.

Lemma float_of_nat_up_correct k : finite (gen_float_of_nat_up k) ->
  INR k <= FI2F (gen_float_of_nat_up k).
Proof.
elim: k => [|k IHk].
{ move=> _; rewrite FI2F0; apply Rle_refl. }
move=> Fa; move: (add_up_spec Fa); apply Rle_trans; rewrite S_INR.
apply Rplus_le_compat; [|by rewrite FI2F1; right]; apply IHk.
move: Fa => /=; apply add_up_spec_fl.
Qed.

(* multiplication with upward rounding *)
Variable mul_up : FI fs -> FI fs -> FI fs.

Hypothesis mul_up_spec : forall x y, finite (mul_up x y) ->
  (FI2F x * FI2F y <= FI2F (mul_up x y))%R.
Hypothesis mul_up_spec_fl : forall x y, finite (mul_up x y) -> finite x.
Hypothesis mul_up_spec_fr : forall x y, finite (mul_up x y) -> finite y.

(* division with upward rounding *)
Variable div_up : FI fs -> FI fs -> FI fs.

Hypothesis div_up_spec : forall x y, finite (div_up x y) -> finite y ->
  (FI2F x / FI2F y <= FI2F (div_up x y))%R.
Hypothesis div_up_spec_fl : forall x y, finite (div_up x y) -> finite y ->
  finite x.

Variable feps : FI fs.

Hypothesis feps_spec : eps (fis fs) <= FI2F feps.

Variable feta : FI fs.

Hypothesis feta_spec : eta (fis fs) <= FI2F feta.

Definition gen_compute_c_aux (A : 'M[FI fs]_n) (maxdiag : FI fs) : FI fs :=
  @compute_c_aux _ _ _ _ _ _ fun_of_ssr _ I0_ssr succ0_ssr add_up mul_up div_up
    feps feta A maxdiag.

Lemma compute_c_aux_correct (A : 'M[FI fs]_n) maxdiag :
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (finite (add_up
             (mul_up ((gen_float_of_nat_up (2 * n.+1)%N)) feps)
             (- (1)))%C) ->
  (FI2F (add_up
             (mul_up ((gen_float_of_nat_up (2 * n.+1)%N)) feps)
             (- (1)))%C < 0) ->
  (forall i, 0 <= FI2F (A i i)) ->
  (0 <= FI2F maxdiag) ->
  finite (gen_compute_c_aux A maxdiag) ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F maxdiag)
  <= FI2F (gen_compute_c_aux A maxdiag))%R.
Proof.
have Pnp2 := pos_INR (n.+1)%N.
have P2np2 := pos_INR (2 * n.+1)%N.
have Pe := eps_pos (fis fs).
move=> Heps Fnem1 Nnem1 Pdiag Pmaxdiag Fc.
rewrite /gen_compute_c_aux /compute_c_aux.
move: (add_up_spec Fc); apply Rle_trans, Rplus_le_compat.
{ have Fl := add_up_spec_fl Fc.
  move: (mul_up_spec Fl); apply Rle_trans, Rmult_le_compat.
  { by apply Rmult_le_pos; [lra|apply gamma_pos]. }
  { by apply big_sum_pos_pos => i; rewrite !mxE. }
  { rewrite /gamma mult_INR -!(Rmult_assoc (/2)) Rinv_l; [|lra].
    rewrite Rmult_1_l.
    have Fll := mul_up_spec_fl Fl.
    have F1mne := fiopp_spec_f Fnem1.
    move: (div_up_spec Fll F1mne); apply Rle_trans, Rmult_le_compat.
    { apply Rmult_le_pos; [apply pos_INR|apply eps_pos]. }
    { apply Rlt_le, Rinv_0_lt_compat; rewrite -mult_INR.
      by set ne := Rmult _ _; apply (Rplus_lt_reg_r ne); ring_simplify. }
    { have Flr := div_up_spec_fl Fll F1mne.
      move: (mul_up_spec Flr); apply /Rle_trans /Rmult_le_compat => //.
      apply float_of_nat_up_correct, (mul_up_spec_fl Flr). }
    rewrite (fiopp_spec F1mne) -mult_INR; apply Rinv_le.
    { by rewrite -Ropp_0; apply Ropp_lt_contravar. }
    rewrite -Ropp_minus_distr; apply Ropp_le_contravar.
    move: (add_up_spec Fnem1); apply Rle_trans; apply Rplus_le_compat.
    { have Fne := add_up_spec_fl Fnem1.
      move: (mul_up_spec Fne); apply /Rle_trans /Rmult_le_compat => //.
      apply float_of_nat_up_correct, (mul_up_spec_fl Fne). }
    rewrite (fiopp_spec (add_up_spec_fr Fnem1)); apply Ropp_le_contravar.
    by rewrite FI2F1; right. }
  apply tr_up_correct, (mul_up_spec_fr Fl). }
have Fr := add_up_spec_fr Fc.
move: (mul_up_spec Fr); apply Rle_trans; apply Rmult_le_compat.
{ apply Rmult_le_pos; [|by apply pos_INR]; apply Rmult_le_pos; [lra|].
  apply Rlt_le, eta_pos. }
{ apply Rplus_le_le_0_compat; [|apply Pmaxdiag].
  apply Rmult_le_pos; [lra|apply pos_INR]. }
{ move: (mul_up_spec (mul_up_spec_fl Fr)); apply Rle_trans.
  have Frl := mul_up_spec_fl Fr.
  apply Rmult_le_compat.
  { apply Rmult_le_pos; [lra|apply Rlt_le, eta_pos]. }
  { apply pos_INR. }
  { have Frll := mul_up_spec_fl Frl.
    move: (mul_up_spec Frll); apply Rle_trans.
    apply Rmult_le_compat; [lra|apply Rlt_le, eta_pos| |by []].
    replace 4 with (INR 4); [|by simpl; lra].
    apply float_of_nat_up_correct, (mul_up_spec_fl Frll). }
  apply float_of_nat_up_correct, (mul_up_spec_fr Frl). }
have Frr := mul_up_spec_fr Fr.
move: (add_up_spec Frr); apply Rle_trans, Rplus_le_compat_r.
have Frrl := add_up_spec_fl Frr.
by change 2 with (INR 2); rewrite -mult_INR; apply float_of_nat_up_correct.
Qed.

Definition gen_compute_c (A : 'M[FI fs]_n) :
  option (FI fs) :=
  @compute_c _ _ _ _ _ _ fun_of_ssr _ I0_ssr succ0_ssr
    leq_instFI lt_instFI add_up mul_up div_up
    (@is_finite fs) feps feta A.

Lemma compute_c_correct (A : 'M[FI fs]_n) :
  (INR (2 * n.+1) * eps (fis fs) < 1) ->
  (forall i, finite (A i i)) ->
  (forall i, (0 <= FI2F (A i i))%R) ->
  forall c : FI fs, gen_compute_c A = Some c ->
  (/2 * gamma (fis fs) (2 * n.+1) * (\tr (cholesky.MF2R (MFI2F A)))
   + 4 * eta (fis fs) * INR n * (2 * INR n.+1 + FI2F (gen_max_diag A))
   <= FI2F c)%R.
Proof.
move=> Heps Fdiag Pdiag c.
rewrite /gen_compute_c /compute_c.
set nem1 := add_up _ _.
case_eq (is_finite nem1 && (nem1 < 0)%C); [|by []].
rewrite Bool.andb_true_iff => H; elim H => Fnem1 Nnem1.
set c' := compute_c_aux _ _ _ _ _ _ _.
case_eq (is_finite c') => Hite'; [|by []]; move=> Hc'.
have Hc'' : c' = c by injection Hc'.
rewrite -Hc''; apply compute_c_aux_correct => //.
{ eapply (Rlt_le_trans _ (FI2F 0%C)); [|by right; rewrite FI2F0].
  apply filt_spec => //; apply finite0. }
by apply max_diag_pos.
Qed.

Definition gen_sub_down : FI fs -> FI fs -> FI fs :=
  @sub_down _ (@opp_instFI _) add_up.

Lemma sub_down_correct x y : finite (gen_sub_down x y) ->
  FI2F (gen_sub_down x y) <= FI2F x - FI2F y.
Proof.
move=> Fxy; rewrite /gen_sub_down /sub_down.
rewrite (fiopp_spec Fxy) -Ropp_minus_distr; apply Ropp_le_contravar.
have Fxy' := fiopp_spec_f1 Fxy.
move: (add_up_spec Fxy'); apply Rle_trans, Rplus_le_compat_l.
by rewrite (fiopp_spec (add_up_spec_fr Fxy')); right.
Qed.

Lemma sub_down_fl x y : finite (gen_sub_down x y) -> finite x.
Proof. by move /fiopp_spec_f1 /add_up_spec_fr /fiopp_spec_f1. Qed.

Definition gen_posdef_check (A : 'M[FI fs]_n) : bool :=
  @posdef_check _ _ _ _ _ _ (@div_instFI _) _
    fun_of_ssr row_ssr store_ssr dotmulB0_ssr _
    I0_ssr succ0_ssr nat_of_ssr fheq (@matrix.trmx (FI fs)) _ _
    add_up mul_up div_up feps feta (@is_finite fs) test_n A.

Lemma posdef_check_f1 A : gen_posdef_check A = true ->
  forall i j, finite (A i j).
Proof.
rewrite /gen_posdef_check /posdef_check !Bool.andb_true_iff.
do 3 elim; move=> _ SA _.
set cc := compute_c _ _ _ _ _ _ _; case_eq cc => // c' Hc'.
set At := map_diag _ _; set Rt := cholesky _.
move/andP => [Had Hpd].
suff: forall i j : 'I_n, (i <= j)%N -> finite (A i j).
{ move=> H i j; case (ltnP j i); [|by apply H]; move=> Hij.
  rewrite -(@fieq_spec_f _ (A^T i j)); [by rewrite mxE; apply H, ltnW|].
  by apply is_sym_correct_aux. }
move=> i j Hij; suff: finite (At i j).
{ case_eq (i == j :> nat) => Hij'.
  { move /eqP /ord_inj in Hij'; rewrite Hij' map_diag_correct_diag.
    apply sub_down_fl. }
  rewrite map_diag_correct_ndiag //.
  by move /eqP in Hij' => H; apply Hij'; rewrite H. }
apply (@cholesky_success_infnan_f1 _ _ At Rt^T) => //; split.
{ rewrite /Rt -/(cholesky_ssr At).
  apply cholesky_spec_correct, cholesky_correct. }
move=> i'; rewrite mxE.
have->: R0 = FI2F (FI0 fs) by rewrite FI2F0.
apply filt_spec; [by apply finite0| |].
{ move: Had i'; rewrite -/(ssr_all_diag _ _); apply all_diag_correct. }
move: Hpd i'; rewrite /pos_diag -/(ssr_all_diag _ _); apply all_diag_correct.
Qed.

Lemma posdef_check_correct A : gen_posdef_check A = true ->
  posdef (cholesky.MF2R (MFI2F A)).
Proof.
move=> H; have Hfdiag := posdef_check_f1 H; move: H.
rewrite /gen_posdef_check /posdef_check !Bool.andb_true_iff.
do 3 elim; move=> Hn Hsym Htpdiag.
apply test_n_correct in Hn.
have Hn' : 2 * INR n.+1 * eps (fis fs) < 1.
{ move: (neps_pos (fis fs) n.+1); rewrite !Rmult_assoc; lra. }
have Hn'' : INR (2 * n.+1) * eps (fis fs) < 1 by rewrite mult_INR.
apply is_sym_correct in Hsym.
set cc := compute_c _ _ _ _ _ _ _; case_eq cc => // c' Hc'.
rewrite Bool.andb_true_iff; elim.
set At := map_diag _ _; set Rt := cholesky _.
move=> HtfRt HtpRt.
have Htpdiag' := all_diag_correct Htpdiag.
have Hpdiag : forall i, 0 <= FI2F (A i i).
{ move=> i; eapply (Rle_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  by apply file_spec => //; [apply finite0|apply Htpdiag']. }
have HfRt := all_diag_correct HtfRt.
have HtpRt' := all_diag_correct HtpRt.
have HpRt : forall i, 0 < (MFI2F Rt) i i.
{ move=> i; eapply (Rle_lt_trans _ (FI2F 0%C)); [by right; rewrite FI2F0|].
  by rewrite mxE; apply filt_spec => //; [apply finite0|apply HtpRt']. }
move {Htpdiag HtfRt HtpRt Htpdiag' HtpRt'}.
apply corollary_2_4_with_c_upper_bound with
 (maxdiag := FI2F (gen_max_diag A)) (c := FI2F c') (At0 := At) => //.
{ by move=> i; rewrite mxE. }
{ by apply max_diag_correct. }
{ by apply compute_c_correct. }
have Hfat : forall i, finite (At i i).
{ move=> i; move: (cholesky_spec_correct (cholesky_correct At)).
  elim=> _ Hs; move: (Hs i); rewrite mxE /cholesky_ssr => {Hs} Hs.
  move: (HfRt i); rewrite /Rt Hs /ytildes_infnan => H.
  move: (fisqrt_spec_f1 H); apply stilde_infnan_fc. }
split; move=> i; [move=> j Hij|].
{ by apply /map_diag_correct_ndiag /eqP; rewrite neq_ltn Hij. }
move: (Hfat i); rewrite !mxE /At map_diag_correct_diag; apply sub_down_correct.
Qed.

Lemma map_diag_sub_down_correct (A : 'M_n) r :
  (forall i, finite (gen_sub_down (A i i) r)) ->
  exists d : 'rV_n, cholesky.MF2R (MFI2F (ssr_map_diag (gen_sub_down^~ r) A))
    = cholesky.MF2R (MFI2F A) - diag_mx d
    /\ (FI2F r : R) *: 1 <=m: diag_mx d.
Proof.
move=> HF.
set A' := ssr_map_diag (gen_sub_down^~ r) A.
exists (\row_i (((MFI2F A) i i : R) - ((MFI2F A') i i : R))); split.
{ rewrite -matrixP => i j; rewrite !mxE.
  set b := (_ == _)%B; case_eq b; rewrite /b /GRing.natmul /= => Hij.
  { move /eqP in Hij; rewrite Hij map_diag_correct_diag.
    rewrite /GRing.add /GRing.opp /=; ring. }
  rewrite /GRing.add /GRing.opp /GRing.zero /= Ropp_0 Rplus_0_r.
  by apply /f_equal /f_equal /map_diag_correct_ndiag /eqP; rewrite Hij. }
move=> i j; rewrite !mxE.
set b := (_ == _)%B; case_eq b; rewrite /b /GRing.natmul /= => Hij.
{ rewrite /GRing.mul /GRing.one /= Rmult_1_r /A' map_diag_correct_diag.
  rewrite /GRing.add /GRing.opp /=.
  replace (FI2F r : R)
  with (Rminus (FI2F (A i i)) (Rminus (FI2F (A i i)) (FI2F r))) by ring.
  by apply Rplus_le_compat_l, Ropp_le_contravar, sub_down_correct. }
by rewrite GRing.mulr0; right.
Qed.

Definition gen_posdef_check_itv (A : 'M[FI fs]_n) (r : FI fs) : bool :=
  @posdef_check_itv _ _ _ _ _ _ (@div_instFI _) _
    fun_of_ssr row_ssr store_ssr dotmulB0_ssr _
    I0_ssr succ0_ssr nat_of_ssr fheq (@matrix.trmx (FI fs)) _ _
    add_up mul_up div_up feps feta (@is_finite fs) test_n A r.

Lemma posdef_check_itv_f1 A r : gen_posdef_check_itv A r = true ->
  forall i j, finite (A i j).
Proof.
rewrite /gen_posdef_check_itv /posdef_check_itv; set A' := map_diag _ _.
move/andP => [_ Hp] i j.
suff: finite (A' i j); [|by apply posdef_check_f1].
case_eq (i == j :> nat) => Hij'.
{ move /eqP /ord_inj in Hij'; rewrite Hij' map_diag_correct_diag.
  apply sub_down_fl. }
rewrite map_diag_correct_ndiag //.
by move /eqP in Hij' => H; apply Hij'; rewrite H.
Qed.

Lemma posdef_check_itv_correct A r : gen_posdef_check_itv A r = true ->
  forall Xt : 'M[R]_n, Xt^T = Xt ->
  Mabs (Xt - cholesky.MF2R (MFI2F A)) <=m:
    cholesky.MF2R (MFI2F (matrix.const_mx r)) ->
  posdef Xt.
Proof.
rewrite /gen_posdef_check_itv /posdef_check_itv.
set nr := mul_up _ _; set A' := map_diag _ _.
rewrite 2!Bool.andb_true_iff; elim; elim=> Fr Pr HA' Xt SXt HXt.
have HA'' := posdef_check_correct HA'.
have HF := posdef_check_f1 HA'.
have HF' : forall i, finite (gen_sub_down (A i i) nr).
{ by move=> i; move: (HF i i); rewrite map_diag_correct_diag. }
rewrite -(GRing.addr0 Xt) -(GRing.subrr (cholesky.MF2R (MFI2F A))).
elim (map_diag_sub_down_correct HF') => d [Hd Hd'].
rewrite /ssr_map_diag /gen_sub_down -/A' in Hd.
have HA : cholesky.MF2R (MFI2F A) = cholesky.MF2R (MFI2F A') + diag_mx d.
{ by rewrite Hd -GRing.addrA (GRing.addrC _ (_ d)) GRing.subrr GRing.addr0. }
rewrite {1}HA.
rewrite !GRing.addrA (GRing.addrC Xt) -!GRing.addrA (GRing.addrC (diag_mx d)).
apply posdef_norm_eq_1 => x Hx.
rewrite mulmxDr mulmxDl -(GRing.addr0 0); apply Madd_lt_le_compat.
{ apply HA'' => Hx'; rewrite Hx' norm2_0 /GRing.zero /GRing.one /= in Hx.
  move: Rlt_0_1; rewrite Hx; apply Rlt_irrefl. }
rewrite GRing.addrA mulmxDr mulmxDl -(GRing.opprK (_ *m diag_mx d *m _)).
apply Mle_sub.
apply Mle_trans with (- Mabs (x^T *m (Xt - cholesky.MF2R (MFI2F A)) *m x));
  [apply Mopp_le_contravar|by apply Mge_opp_abs].
apply Mle_trans with ((Mabs x)^T *m Mabs (Xt - cholesky.MF2R (MFI2F A)) *m Mabs x).
{ apply (Mle_trans (Mabs_mul _ _)), Mmul_le_compat_r; [by apply Mabs_pos|].
  rewrite map_trmx; apply (Mle_trans (Mabs_mul _ _)).
  by apply Mmul_le_compat_l; [apply Mabs_pos|apply Mle_refl]. }
apply (Mle_trans (cholesky.Mmul_abs_lr _ HXt)).
apply Mle_trans with (INR n * FI2F r)%Re%:M.
{ apply cholesky.r_upper_bound => //.
  { move: HXt; apply Mle_trans, Mabs_pos. }
  by move=> i j; rewrite !mxE; right. }
set IN := INR n; rewrite Mle_scalar !mxE /GRing.natmul /= -(Rmult_1_r (_ * _)).
replace R1 with (R1^2) by ring; rewrite /GRing.one /= in Hx; rewrite -Hx.
rewrite norm2_sqr_dotprod /dotprod mxE /= big_distrr /=.
apply big_rec2 => [|i y1 y2 _ Hy12]; [by right|]; rewrite mul_mx_diag !mxE.
rewrite /GRing.add /GRing.mul /=; apply Rplus_le_compat => //.
rewrite (Rmult_comm _ (d _ _)) !Rmult_assoc -Rmult_assoc.
apply Rmult_le_compat_r; [by apply Rle_0_sqr|].
have Fnr : finite nr.
{ move: (HF' ord0); rewrite /gen_sub_down /sub_down => F.
  apply fiopp_spec_f1 in F; apply (add_up_spec_fl F). }
apply (Rle_trans _ (FI2F nr)).
{ apply (Rle_trans _ (FI2F (float_of_nat_up add_up n) * FI2F r)).
  { apply Rmult_le_compat_r.
    { change R0 with (F0 (fis fs) : R); rewrite -FI2F0; apply file_spec.
      { apply finite0. }
      { move: Fnr; rewrite /nr; apply mul_up_spec_fr. }
      by move: Pr. }
    by apply float_of_nat_up_correct, (@mul_up_spec_fl _ r). }
  by apply mul_up_spec. }
by move: (Hd' i i); rewrite !mxE eq_refl /GRing.natmul /GRing.mul /= Rmult_1_r.
Qed.

Variables (F : Type) (F2FI : F -> FI fs) (toR : F -> R).
Hypothesis (F2FI_correct : forall f, finite (F2FI f) -> FI2F (F2FI f) = toR f :> R).

(* TODO: rename "gen_" to "inst_" or so *)

Global Instance map_mx_ssr : map_mx_class matrix :=
  fun T T' m n f A => matrix.map_mx f A.

Definition gen_posdef_check_F (A : 'M[F]_n) :=
  @posdef_check_F _ _ _ _ _ _ _ _ fun_of_ssr row_ssr store_ssr dotmulB0_ssr _
  I0_ssr succ0_ssr nat_of_ssr fheq (@matrix.trmx (FI fs)) _ _
  add_up mul_up div_up map_mx_ssr F F2FI feps feta (@is_finite fs) test_n A.

Definition gen_posdef_check_itv_F (A : 'M[F]_n) (r : F) :=
  @posdef_check_itv_F _ _ _ _ _ _ _ _ fun_of_ssr row_ssr store_ssr dotmulB0_ssr _
  I0_ssr succ0_ssr nat_of_ssr fheq (@matrix.trmx (FI fs)) _ _
  add_up mul_up div_up map_mx_ssr F F2FI feps feta (@is_finite fs) test_n A r.

Lemma posdef_check_F_f1 A : gen_posdef_check_F A = true ->
  forall i j, finite ((map_mx F2FI A) i j).
Proof. apply posdef_check_f1. Qed.

Lemma posdef_check_itv_F_f1 A r : gen_posdef_check_itv_F A r = true ->
  forall i j, finite ((map_mx F2FI A) i j).
Proof. apply posdef_check_itv_f1. Qed.

Lemma posdef_check_F_correct (A : 'M[F]_n) :
  gen_posdef_check_F A = true ->
  posdef (matrix.map_mx toR A).
Proof.
move=> H; move: (posdef_check_correct H).
set A' := cholesky.MF2R _; set A'' := matrix.map_mx _ _.
have->: A' = A''; [|by []].
apply/matrixP=> i j; rewrite !mxE; apply F2FI_correct.
by move: (posdef_check_f1 H i j); rewrite mxE.
Qed.

Lemma posdef_check_itv_F_correct (A : 'M[F]_n) (r : F) :
  gen_posdef_check_itv_F A r = true ->
  forall Xt : 'M_n, Xt^T = Xt ->
  Mabs (Xt - matrix.map_mx toR A) <=m: matrix.const_mx (toR r) ->
  posdef Xt.
Proof.
move=> H Xt SXt HXt; apply (posdef_check_itv_correct H SXt).
move=> i j; move: (HXt i j); rewrite !mxE F2FI_correct.
{ by rewrite F2FI_correct //; move: H; do 2 (move/andP; elim). }
by move: (posdef_check_itv_f1 H i j); rewrite mxE.
Qed.

End proof_inst_ssr_matrix_float_infnan.

Notation ord_instN := (fun _ : nat => nat) (only parsing).
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

(*
Definition iteri_ord_instN : forall T, nat -> (ordT n -> T -> T) -> T -> T :=
  @iteri_ord ordT _ O S. (* ?? *)
*)

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

Variable eps_inv : BigZ.t_.

(* arithmetic operations with directed rounding *)
Variable add1 mul1 div1 : T -> T -> T.
Variable feps feta : T.

Variable is_finite : T -> bool.

Definition posdef_check_seqmx (M : seqmatrix T) : bool :=
  @posdef_check T ord_instN seqmatrix' _ _ _ _ _ _ _ _ _ n.+1 _ _ _ _ _ _ _
    add1 mul1 div1 feps feta is_finite (test_n eps_inv) M.

Definition posdef_check_itv_seqmx (M : seqmatrix T) (r : T) : bool :=
  @posdef_check_itv T ord_instN seqmatrix' _ _ _ _ _ _ _ _ _ n.+1 _ _ _ _ _ _ _
    add1 mul1 div1 feps feta is_finite (test_n eps_inv) M r.

Global Instance map_mx_seqmx : map_mx_class seqmatrix' :=
  fun T T' m n f s => map (map f) s.

Variables (F : Type) (F2FI : F -> T).

Definition posdef_check_F_seqmx (M : seqmatrix F) : bool :=
  @posdef_check_F T ord_instN seqmatrix' _ _ _ _ _ _ _ _ _ n.+1 _ _ _ _ _ _ _
    add1 mul1 div1 map_mx_seqmx
    F F2FI feps feta is_finite (test_n eps_inv) M.

Definition posdef_check_itv_F_seqmx (M : seqmatrix F) (r : F) : bool :=
  @posdef_check_itv_F T ord_instN seqmatrix' _ _ _ _ _ _ _ _ _ n.+1 _ _ _ _ _ _ _
    add1 mul1 div1 map_mx_seqmx
    F F2FI feps feta is_finite (test_n eps_inv) M r.

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

Variable fs : Float_infnan_spec.

Notation C := (FI fs) (only parsing).

(*
Instance : add (FI fs) := @fiplus fs.
Instance : mul (FI fs) := @fimult fs.
Instance : sqrt (FI fs) := @fisqrt fs.
Instance : div (FI fs) := @fidiv fs.
Instance : opp (FI fs) := @fiopp fs.
Instance : zero (FI fs) := @FI0 fs.
Instance : one (FI fs) := @FI1 fs.

Would be useless. Indeed:

Goal add (FI fs).
tc.
Qed.
*)

Context {n : nat}.

Variable eps_inv : BigZ.t_.

Variable add1 mul1 div1 : C -> C -> C.
Variable feps feta : C.

Definition posdef_check5 :=
  gen_posdef_check (n':=n) eps_inv add1 mul1 div1 feps feta.

Definition posdef_check_itv5 :=
  gen_posdef_check_itv (n':=n) eps_inv add1 mul1 div1 feps feta.

Variables (F : Type) (F2FI : F -> FI fs).

Definition posdef_check_F5 :=
  gen_posdef_check_F (n':=n) eps_inv add1 mul1 div1 feps feta F2FI.

(* Now in cholesky_prog.v:

Instance : eq C := @fieq fs.
Instance : leq C := @file fs.
Instance : lt C := @filt fs.
*)

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
     (@I0_ssr n) (@succ0_ssr n) add1 mul1 div1
     feps feta)
  (@compute_c_aux _ _ seqmatrix' (FI0 fs) (FI1 fs) (@fiopp fs)
     (@fun_of_seqmx (FI fs) (FI0 fs)) n.+1
     (@I0_instN n) (@succ0_instN n) add1 mul1 div1
     feps feta).
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
     (@succ0_ssr n) (@leq_instFI fs) (@lt_instFI fs) add1 mul1 div1
     (@is_finite fs) feps feta)
  (@compute_c C _ seqmatrix'
     zero_instFI one_instFI opp_instFI
     (@fun_of_seqmx C zero_instFI) n.+1 (@I0_instN n)
     (@succ0_instN n) leq_instFI lt_instFI add1 mul1 div1
     (@is_finite fs) feps feta).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /compute_c /C.
case (_ && _) => //.
set cc := compute_c_aux _ _ _ _ _ A _.
set cc' := compute_c_aux _ _ _ _ _ As _.
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
  (gen_posdef_check (n':=n) eps_inv add1 mul1 div1 feps feta)
  (posdef_check_seqmx (n:=n) eps_inv add1 mul1 div1 feps feta (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
rewrite paramE /gen_posdef_check /posdef_check_seqmx /posdef_check.
apply f_equal2; [apply f_equal2; [apply f_equal|]|].
{ by apply param_eq; eapply param_apply; [apply param_is_sym|exact param_A]. }
{ apply param_eq; rewrite /noneg_diag.
  eapply param_apply; [|exact param_A].
  eapply param_apply; [apply param_all_diag|apply param_eq_refl]. }
set c := compute_c _ _ _ _ _ _ A.
set c' := compute_c _ _ _ _ _ _ As.
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
  (gen_posdef_check_itv (n':=n) eps_inv add1 mul1 div1 feps feta)
  (posdef_check_itv_seqmx (n:=n) eps_inv add1 mul1 div1 feps feta (@is_finite fs)).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite paramE /gen_posdef_check_itv /posdef_check_itv_seqmx /posdef_check_itv /posdef_check.
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
set c := compute_c _ _ _ _ _ _ (_ _ A).
set c' := compute_c _ _ _ _ _ _ (map_diag _ As).
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
by apply param_fun_eq, param_eq_refl.
}
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
  (gen_posdef_check_F (n':=n) eps_inv add1 mul1 div1 feps feta F2FI)
  (posdef_check_F_seqmx (n:=n) eps_inv add1 mul1 div1 feps feta (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
rewrite /gen_posdef_check_F /posdef_check_F_seqmx /posdef_check_F.
eapply param_apply; [apply param_posdef_check|].
eapply param_apply; [|apply param_A].
eapply param_apply; [apply param_map_mx|apply param_eq_refl].
Qed.

Definition posdef_check_itv_F5 :=
  gen_posdef_check_itv_F (n':=n) eps_inv add1 mul1 div1 feps feta F2FI.

Lemma param_posdef_check_itv_F :
  param (Rseqmx ==> Logic.eq ==> Logic.eq)
  (gen_posdef_check_itv_F (n':=n) eps_inv add1 mul1 div1 feps feta F2FI)
  (posdef_check_itv_F_seqmx (n:=n) eps_inv add1 mul1 div1 feps feta (@is_finite fs) F2FI).
Proof.
apply param_abstr => A As param_A.
apply param_abstr => r r' param_r.
rewrite paramE in param_r; rewrite -param_r.
rewrite /gen_posdef_check_itv_F /posdef_check_itv_F_seqmx /posdef_check_itv_F.
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

Definition eps_inv := 9007199254740992%bigZ.  (* 2^53 *)

Lemma eps_inv_correct : (Z2R [eps_inv]%bigZ <= / eps fis)%Re.
Proof. by rewrite /= /flx64.eps /= Rinv_involutive; [right|lra]. Qed.

Definition add1 := F.add rnd_UP prec.
Definition mul1 := F.mul rnd_UP prec.
Definition div1 := F.div rnd_UP prec.

Definition feps : T := Float 1%bigZ (-53)%bigZ.
Definition feta : T := Float 1%bigZ (-1075)%bigZ.

Definition is_finite : T -> bool := F.real.

Definition posdef_check4_coqinterval (M : seq (seq T)) : bool :=
  @posdef_check_seqmx T _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv add1 mul1 div1 feps feta is_finite M.

Definition posdef_check_itv4_coqinterval (M : seq (seq T)) (r : T) : bool :=
  @posdef_check_itv_seqmx T _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv add1 mul1 div1 feps feta is_finite M r.

End test_CoqInterval.

Section test_CoqInterval_F2FI.

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

Lemma F2FI_correct (f : F.type) :
  finite (F2FI f) -> FI2F (F2FI f) = toR f :> R.
Proof.
case f => // m e.
rewrite /finite FtoX_real /FI2F.
case (FI_prop (F2FI (Float m e))) => Hf; [by rewrite Hf|].
destruct Hf as (r, Hr, Hr'); move=> HF /=.
suff: Xreal r = Xreal (proj_val (F.toX (Float m e))).
{ by move=> H; inversion H. }
by move: HF; rewrite -real_FtoX_toR // -Hr /F2FI /=; case (_ <? _).
Qed.

(* Can be removed:

Instance add''' : add FI := fiplus.
Instance mul''' : mul FI := fimult.
Instance sqrt''' : sqrt FI := fisqrt.
Instance div''' : div FI := fidiv.
Instance opp''' : opp FI := fiopp.
Instance zero''' : zero FI := FI0.
Instance one''' : one FI := FI1.

Instance eq''' : eq FI := @fieq coqinterval_infnan.
Instance leq''' : leq FI := @file coqinterval_infnan.
Instance lt''' : lt FI := @filt coqinterval_infnan.
*)

Lemma fiplus1_proof (x y : FI) : mantissa_bounded (F.add rnd_UP 53%bigZ x y).
unfold mantissa_bounded, x_bounded.
rewrite F.add_correct; set (z := Xadd _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set r'' := round _ _ _ _; exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Definition fiplus1 (x y : FI) : FI :=
  {| FI_val := F.add rnd_UP 53%bigZ x y; FI_prop := fiplus1_proof x y |}.

Lemma round_UP_ge beta fexp :  (* TODO: pas trouvé dans Flocq *)
  Valid_exp fexp ->
  forall x, (x <= Fcore_generic_fmt.round beta fexp Zceil x)%Re.
Proof.
intros vfexp x.
destruct (generic_format_EM beta fexp x).
{ now right; rewrite round_generic. }
now apply Rlt_le, round_DN_UP_lt.
Qed.

Lemma fiplus1_spec_fl x y : finite (fiplus1 x y) -> finite x.
Proof.
unfold finite, fiplus1; simpl; do 2 rewrite FtoX_real.
rewrite F.add_correct /Xround /Xbind.
by case: (F.toX x).
Qed.

Lemma fiplus1_spec_fr x y : finite (fiplus1 x y) -> finite y.
Proof.
unfold finite, fiplus1; simpl; do 2 rewrite FtoX_real.
rewrite F.add_correct /Xround /Xbind.
case (F.toX y) =>//; by rewrite Xadd_comm.
Qed.

Lemma fiplus1_spec x y : finite (fiplus1 x y) ->
  (FI2F x + FI2F y <= FI2F (fiplus1 x y))%Re.
Proof.
move=> Fxy.
have Fx := fiplus1_spec_fl Fxy.
have Fy := fiplus1_spec_fr Fxy.
move: Fxy Fx Fy.
unfold finite; rewrite !(FI2F_X2F_FtoX _) !FtoX_real.
unfold fiplus1; simpl; rewrite F.add_correct.
case (FI_prop x) => [->//|] [rx -> Hrx].
case (FI_prop y) => [->//|] [ry -> Hry].
set (z := Xadd _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite !round_generic //; try now apply generic_format_FLX.
{ rewrite /round /rnd_of_mode.
  apply (Rle_trans _ r); [|by apply round_UP_ge, FLX_exp_valid].
  by right; injection Hr. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Lemma fimult1_proof (x y : FI) : mantissa_bounded (F.mul rnd_UP 53%bigZ x y).
unfold mantissa_bounded, x_bounded.
rewrite F.mul_correct; set (z := Xmul _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set r'' := round _ _ _ _; exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Definition fimult1 (x y : FI) : FI :=
  {| FI_val := F.mul rnd_UP 53%bigZ x y; FI_prop := fimult1_proof x y |}.

Lemma fimult1_spec_fl x y : finite (fimult1 x y) -> finite x.
Proof.
unfold finite, fimult1; simpl; do 2 rewrite FtoX_real.
rewrite F.mul_correct /Xround /Xbind.
by case: (F.toX x).
Qed.

Lemma fimult1_spec_fr x y : finite (fimult1 x y) -> finite y.
Proof.
unfold finite, fimult1; simpl; do 2 rewrite FtoX_real.
rewrite F.mul_correct /Xround /Xbind.
case (F.toX y) =>//; by rewrite Xmul_comm.
Qed.

Lemma fimult1_spec x y : finite (fimult1 x y) ->
  (FI2F x * FI2F y <= FI2F (fimult1 x y))%Re.
Proof.
move=> Fxy.
have Fx := fimult1_spec_fl Fxy.
have Fy := fimult1_spec_fr Fxy.
move: Fxy Fx Fy.
unfold finite; rewrite !(FI2F_X2F_FtoX _) !FtoX_real.
unfold fimult1; simpl; rewrite F.mul_correct.
case (FI_prop x) => [->//|] [rx -> Hrx].
case (FI_prop y) => [->//|] [ry -> Hry].
set (z := Xmul _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite !round_generic //; try now apply generic_format_FLX.
{ rewrite /round /rnd_of_mode.
  apply (Rle_trans _ r); [|by apply round_UP_ge, FLX_exp_valid].
  by right; injection Hr. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Lemma fidiv1_proof (x y : FI) : mantissa_bounded (F.div rnd_UP 53%bigZ x y).
unfold mantissa_bounded, x_bounded.
rewrite F.div_correct; set (z := Xdiv _ _).
unfold Xround; case z; [now left|intro r'; right]; unfold Xbind.
set (r'' := round _ _ _ _); exists r''; [now simpl|].
apply FLX_format_generic; [now simpl|].
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Definition fidiv1 (x y : FI) : FI :=
  {| FI_val := F.div rnd_UP 53%bigZ x y; FI_prop := fidiv1_proof x y |}.

Lemma fidiv1_spec_fl x y : finite (fidiv1 x y) -> finite y -> finite x.
Proof.
move=> Fxy _; move: Fxy; unfold finite, fidiv; simpl; do 2 rewrite FtoX_real.
now rewrite F.div_correct; case (F.toX x); [|intro r].
Qed.

Lemma fidiv1_spec x y : finite (fidiv1 x y) -> finite (y) ->
  (FI2F x / FI2F y <= FI2F (fidiv1 x y))%Re.
Proof.
move=> Fxy Fy.
have Fx := fidiv1_spec_fl Fxy Fy.
move: Fxy Fx Fy.
unfold finite; rewrite !(FI2F_X2F_FtoX _) !FtoX_real.
unfold fidiv1; simpl; rewrite F.div_correct.
case (FI_prop x) => [->//|] [rx -> Hrx].
case (FI_prop y) => [->//|] [ry -> Hry].
set (z := Xdiv _ _); case_eq z; [now simpl|]; intros r Hr _ _ _; simpl.
rewrite !round_generic //; try now apply generic_format_FLX.
{ rewrite /round /rnd_of_mode.
  apply (Rle_trans _ r); [|by apply round_UP_ge, FLX_exp_valid].
  right; move: Hr; rewrite /z /= /Xdiv'; case (is_zero ry) => //.
  by move=> H; injection H. }
now apply generic_format_round; [apply FLX_exp_valid|apply valid_rnd_UP].
Qed.

Definition feps' : FI := F2FI feps.
Definition feta' : FI := F2FI feta.

Lemma feps'_correct : (eps fis <= FI2F feps')%Re.
Proof. by rewrite F2FI_correct /=; [rewrite /Rdiv Rmult_1_l; right|]. Qed.

Lemma feta'_correct : (eta fis <= FI2F feta')%Re.
Proof. by rewrite F2FI_correct /=; [rewrite /Rdiv Rmult_1_l; right|]. Qed.

(* Erik: A little test to know which FI are in play:

Goal zero FI.
Fail by tc.
change FI with (float_infnan_spec.FI coqinterval_infnan.coqinterval_infnan).
tc.
Qed.
*)

(* Let's override FI for now...! *)
Local Notation FI := (float_infnan_spec.FI coqinterval_infnan.coqinterval_infnan).

Definition posdef_check4_coqinterval' (M : seq (seq FI)) : bool :=
  @posdef_check_seqmx FI _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv fiplus1 fimult1 fidiv1 feps' feta' (@float_infnan_spec.is_finite coqinterval_infnan) M.

Definition posdef_check_F4_coqinterval' (M : seq (seq F.type)) : bool :=
  @posdef_check_F_seqmx FI _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv fiplus1 fimult1 fidiv1 feps' feta' (@float_infnan_spec.is_finite coqinterval_infnan) F.type F2FI M.

Definition posdef_check_itv4_coqinterval' (M : seq (seq FI)) (r : FI) : bool :=
  @posdef_check_itv_seqmx FI _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv fiplus1 fimult1 fidiv1 feps' feta' (@float_infnan_spec.is_finite coqinterval_infnan) M r.

Definition posdef_check_itv_F4_coqinterval' (M : seq (seq F.type)) (r : F.type) : bool :=
  @posdef_check_itv_F_seqmx FI _ _ _ _ _ _ _ (seq.size M).-1 _ _ _
    eps_inv fiplus1 fimult1 fidiv1 feps' feta' (@float_infnan_spec.is_finite coqinterval_infnan) F.type F2FI M r.

Definition BigQ2F (q : bigQ) : F.type * F.type :=
  match q with
  | BigQ.Qz m => let m0 := Interval_specific_ops.Float m Bir.exponent_zero in (m0, m0)
  | BigQ.Qq m n => let m0 := Interval_specific_ops.Float m Bir.exponent_zero in
                   let n0 := Interval_specific_ops.Float (BigZ.Pos n) Bir.exponent_zero in
                   (F.div rnd_DN prec m0 n0, F.div rnd_UP prec m0 n0)
  end.

Definition test_posdef_check_itv (M : seq (seq F.type)) (r : bigQ) : bool :=
  posdef_check_itv_F4_coqinterval' M (snd (BigQ2F r)).

(* Remark: ultimately, we'll have to check that mat does not contain NaNs *)
(*
Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (@mx_of_seqmx_val _ R0 m m (map (map toR) mat)).
*)

Definition posdef_seqF (mat : seqmatrix F.type) : Prop :=
  let m := seq.size mat in
  posdef (matrix.map_mx toR (@mx_of_seqmx_val _ zero'' m m mat)).

(* First attempt
Context `{mx : Type -> nat -> nat -> Type, !map_mx_class mx}.
Context `{!heq (mx FI)}.
Context `{!transpose_class (mx FI)}.
Context `{ordT : nat -> Type, !fun_of FI ordT (mx FI)}.
Context `{!row_class ordT (mx FI)}.
Typeclasses eauto := debug.
*)

Lemma posdef_check_F_correct_inst (A : seqmatrix F.type) :
  posdef_check_F4_coqinterval' A = true ->
  posdef_seqF A.
Proof.
case: A => [|A0 A1].
{ by move=> _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> Hmain.
eapply (@posdef_check_F_correct _ coqinterval_infnan).
- apply eps_inv_correct.
- apply fiplus1_spec.
- apply fiplus1_spec_fl.
- apply fiplus1_spec_fr.
- apply fimult1_spec.
- apply fimult1_spec_fl.
- apply fimult1_spec_fr.
- apply fidiv1_spec.
- apply fidiv1_spec_fl.
- apply feps'_correct.
- apply feta'_correct.
- apply F2FI_correct.
- rewrite -Hmain /gen_posdef_check_F /posdef_check_F4_coqinterval'.
apply paramP.
eapply param_apply; first exact: param_posdef_check_F.
(* suff{4}->: (A0 :: A1) =
  (@padseqmx _ zero'' (seq.size (A0 :: A1)) (seq.size (A0 :: A1)) (A0 :: A1)). *)
apply/trivial_param/refines_seqmxP=>//; rewrite -/(seq.size _).
(* Erik: Missing hyp *) admit.
admit.
Admitted.

(* TODO: improve error message in case of failure *)
Ltac prove_posdef :=
  by apply posdef_check_F_correct_inst; abstract (vm_cast_no_check (erefl true)).

Definition posdef_itv_seqF (mat : seqmatrix F.type) (r : F.type) : Prop :=
  let m := seq.size mat in
  forall Xt : 'M_m, Xt^T = Xt ->
  Mabs (Xt - matrix.map_mx toR (@mx_of_seqmx_val _ zero'' m m mat))
    <=m: matrix.const_mx (toR r) ->
  posdef Xt.

Lemma posdef_check_itv_F_correct_inst (A : seqmatrix F.type) (r : F.type) :
  let m := seq.size A in
  posdef_check_itv_F4_coqinterval' A r = true ->
  posdef_itv_seqF A r.
Proof.
case: A => [|A0 A1].
{ by move=> _ _ Xt _ _ x Hx; casetype False; apply /Hx /matrixP; case. }
move=> m Hmain Xt SXt HXt.
eapply (@posdef_check_itv_F_correct _ coqinterval_infnan).
- apply eps_inv_correct.
- apply fiplus1_spec.
- apply fiplus1_spec_fl.
- apply fiplus1_spec_fr.
- apply fimult1_spec.
- apply fimult1_spec_fl.
- apply fimult1_spec_fr.
- apply fidiv1_spec.
- apply fidiv1_spec_fl.
- apply feps'_correct.
- apply feta'_correct.
- apply F2FI_correct.
- admit.  (* ingredient: param_posdef_check_itv_F *)
- exact SXt.
- exact HXt.
Admitted.

Ltac prove_posdef_itv :=
  by apply posdef_check_itv_F_correct_inst; abstract (vm_cast_no_check (erefl true)).

Require Import testsuite.

Lemma test_m12 : posdef_seqF m12.
Time prove_posdef.
Qed.

Lemma test_m12_r : posdef_itv_seqF m12 (Float 1%bigZ (-10)%bigZ).
Time prove_posdef_itv.
Qed.

About one.

Goal True. idtac "test_posdef_check_CoqInterval". done. Qed.
Time Eval vm_compute in posdef_check4_coqinterval m12.
(* 6.3 s on Erik's laptop *)

Time Eval vm_compute in posdef_check_F4_coqinterval' m12.
(* 7.1 s on Erik's laptop *)

Goal True. idtac "test_CoqInterval". done. Qed.
Fail Time Eval vm_compute in let res := cholesky4 (n := seq.size m12) m12 in tt.
(* 6.7 s on Erik's laptop *)

End test_CoqInterval_F2FI.
