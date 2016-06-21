Require Import FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype ssralg.
(* tests with multipolys from
   git clone https://github.com/math-comp/multinomials.git *)
From SsrMultinomials Require Import mpoly freeg.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements.
From CoqEAL_refinements Require Import seqmatrix (* for Rord *).
Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Tip to leverage a Boolean condition *)
Definition optb (b : bool) : option (is_true b) :=
  if b then Some erefl else None.
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true
  then left erefl else right erefl.
Definition sumb' (b : bool) : {b = true} + {b -> False}.
  refine (if b is true
          then left erefl else right _).
  done.
Defined.

(** Part I: Generic operations *)

Section seqmpoly_generic.

(** Monomials *)

Definition seqmultinom := seq nat.

Definition mnm0_seq {n} := nseq n 0%N.

(* TODO: may be refactored by using mnm1, mnm_add, mnm_muln *)
Definition mnmd {n} (c : 'I_n) (d : nat) :=
  [multinom (if (c == i :> nat) then d else 0%N) | i < n].

Definition mnmd_seq {n} (i d : nat) :=
  nseq i 0%N ++ [:: d] ++ nseq (n - i - 1) 0%N.

(** Multiplication of multinomials *)
Definition mnm_add_seq m1 m2 := map2 addn m1 m2.

(** Translation of [poset.ltx] *)
Fixpoint mnmc_lt_seq (s1 s2 : seq nat) {struct s1} : bool :=
  match s1 with
  | [::] => true
  | x1 :: s1' =>
      match s2 with
      | [::] => false
      | x2 :: s2' => (x1 < x2)%N && mnmc_lt_seq s1' s2'
      end
  end.

(* Maybe redundant with CoqEAL def *)
Fixpoint mnmc_eq_seq (s1 s2 : seq nat) {struct s1} : bool :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2)%N && mnmc_eq_seq s1' s2'
  | _, _ => false
  end.

End seqmpoly_generic.

(** Multivariate polynomials *)

Module MultinomOrd <: OrderedType.
Definition t := seqmultinom.
Definition eq : t -> t -> Prop := mnmc_eq_seq.
Definition lt : t -> t -> Prop := mnmc_lt_seq.

Lemma intro_eq x y :
  (mnmc_lt_seq x y = false) -> (mnmc_lt_seq y x = false) -> mnmc_eq_seq x y.
Proof.
Admitted.

Definition compare (x y : t) : Compare lt eq x y :=
  match sumb (mnmc_lt_seq x y) with
  | left prf => LT prf
  | right prf =>
    match sumb (mnmc_lt_seq y x) with
    | left prf' => GT prf'
    | right prf' => EQ (intro_eq prf prf')
    end
  end.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y} :=
  match sumb' (mnmc_eq_seq x y) with
  | left prf => left prf
  | right prf => right prf
  end.

Lemma eq_refl : forall x : t, eq x x.
Proof.
elim=> [//|x s IHs].
by rewrite /eq /mnmc_eq_seq eqxx /=.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Admitted.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Admitted.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
End MultinomOrd.

Module M := FMapList.Make MultinomOrd.
(*
Module M := FMapAVL.Make MultinomOrd.
*)
Definition effmpoly := M.t.


(** Part II: Proofs for proof-oriented types and programs *)
Section seqmpoly_theory.

Definition multinom_of_seqmultinom n (m : seqmultinom) : option 'X_{1..n} :=
  if sumb (size m == n) is left prf then
    Some (Multinom (@Tuple n nat m prf))
  else None.

Definition multinom_of_seqmultinom_val n (m : seqmultinom) : 'X_{1..n} :=
  odflt (@mnm0 n) (multinom_of_seqmultinom n m).

Definition seqmultinom_of_multinom n (m : 'X_{1..n}) :=
  let: Multinom m' := m in tval m'.

Lemma seqmultinom_of_multinomK n :
  pcancel (@seqmultinom_of_multinom n) (@multinom_of_seqmultinom n).
Proof.
move=> x; rewrite /seqmultinom_of_multinom /multinom_of_seqmultinom.
case: sumb => [prf|].
  congr Some; apply: val_inj; simpl; apply: val_inj; simpl; by case: (x).
case: x => [t].
by rewrite size_tuple eqxx.
Qed.

Definition Rseqmultinom {n} := ofun_hrel (@multinom_of_seqmultinom n).

Lemma refines_size
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  `{ref_mm' : !param Rseqmultinom m m'} :
  size m' = n.
Proof.
move: ref_mm'.
rewrite paramE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf _.
exact/eqP.
Qed.

Lemma refines_nth_def
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) x0 :
  param Rseqmultinom m m' -> nth x0 m' i = m i.
Proof.
move=> rMN; move: (rMN).
rewrite paramE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf [] <-.
by rewrite multinomE /= (tnth_nth x0).
Qed.

Lemma refines_nth
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) :
  param Rseqmultinom m m' -> nth 0%N m' i = m i.
Proof. exact: refines_nth_def. Qed.

Lemma refines_seqmultinomP
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom) :
  size m' = n ->
  (forall i : 'I_n, nth 0%N m' i = m i) ->
  Rseqmultinom m m'.
Proof.
move=> eq_sz eq_nth.
rewrite /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb => [prf|].
  congr Some; apply: val_inj; simpl.
  by apply: eq_from_tnth => i; rewrite (tnth_nth 0%N) /= eq_nth.
by rewrite eq_sz eqxx.
Qed.

Lemma param_mnm0 n : param Rseqmultinom (@mnm0 n) (@mnm0_seq n).
Proof.
rewrite paramE; apply refines_seqmultinomP.
  by rewrite size_nseq.
move=> i; rewrite nth_nseq if_same multinomE (tnth_nth 0%N) nth_map //=.
by rewrite size_enum_ord.
Qed.

Lemma param_mnmd n :
  param (Rord ==> Logic.eq ==> Rseqmultinom) (@mnmd n) (@mnmd_seq n).
Proof.
case: n => [|n].
  apply param_abstr => c c' param_c.
  apply param_abstr => d d' param_d.
  rewrite -(param_eq param_d).
  by case: (c).
apply param_abstr => c c' param_c.
apply param_abstr => d d' param_d.
rewrite -(param_eq param_d).
apply/trivial_param/refines_seqmultinomP.
  rewrite /mnmd_seq !(size_cat,size_nseq) /=.
  admit. (* easy but tedious *)
move=> i.
rewrite /mnmd_seq /mnmd multinomE (tnth_nth 0%N) /=.
rewrite !(nth_cat,nth_nseq).
rewrite (nth_map ord0); last by rewrite size_enum_ord.
rewrite paramE /Rord in param_c; rewrite -{}param_c.
case: ifP.
  rewrite if_same size_nseq.
  rewrite nth_enum_ord //.
  move=> Hic.
  rewrite ifF //.
  apply/negP; move/eqP => Keq.
  by rewrite Keq ltnn in Hic.
move/negbT; rewrite size_nseq -ltnNge ltnS => Hi.
rewrite nth_enum_ord //.
case: ifP; first by move/eqP->; rewrite subnn.
move/negbT/eqP => Hneq.
case: (ltnP c i) => Hci.
rewrite -(@prednK (i - c)) /=.
  by rewrite nth_nseq if_same.
by rewrite subn_gt0.
exfalso; apply/Hneq/anti_leq.
by rewrite Hi.
Admitted.

Lemma param_mnm_add n :
  param (Rseqmultinom ==> Rseqmultinom ==> Rseqmultinom)
  (@mnm_add n) mnm_add_seq.
Proof.
Admitted.

Lemma param_mnmc_lt n :
  param (Rseqmultinom ==> Rseqmultinom ==> Logic.eq)
  (@mnmc_lt n) mnmc_lt_seq.
Proof.
Admitted.

(** Multivariate polynomials *)

Definition mpoly_of_effmpoly (T : ringType) n (p' : effmpoly T) : option (mpoly n T) :=
  if M.fold (fun k e b => b && (size k == n)%N) p' true then
    Some [mpoly [freeg [seq (a.2, multinom_of_seqmultinom_val n a.1) | a <- M.elements p']]]
  else None.

Definition Mt_of_seq T (s : seq (_ * T)) :=
  foldl (fun acc x => M.add x.1 x.2 acc) (M.empty T) s.

Definition effmpoly_of_mpoly (T : ringType) n (p : mpoly n T) : effmpoly T :=
  Mt_of_seq [seq (seqmultinom_of_multinom a.2, a.1) | a <- fgenum (val p)].

Definition Reffmpoly `{T : ringType, n : nat} :=
  ofun_hrel (@mpoly_of_effmpoly T n).

End seqmpoly_theory.
