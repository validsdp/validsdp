(* (setq coq-prog-name "~/forge/git/validsdp/coq/bin/coqtop") *)
(** * Main tactic for multivariate polynomial positivity. *)

Require Import ZArith.
From Flocq Require Import Core. Require Import Datatypes.
From Interval Require Import Interval_definitions Interval_xreal.
From Interval Require Import Interval_missing.
From Interval Require Import Interval_specific_ops. (* for Float *)
From CoqEAL.theory Require Import ssrcomplements.
From CoqEAL.refinements Require Import hrel refinements param seqmx seqmx_complements binnat binint rational binrat.
Require Import Reals Flocq.Core.Raux QArith CBigZ CBigQ Psatz FSetAVL.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import choice finfun fintype tuple matrix ssralg bigop.
From mathcomp Require Import ssrnum ssrint rat div.
Require Import Rstruct.
Require Import iteri_ord float_infnan_spec real_matrix.
Import Refinements.Op.
Require Import cholesky_prog coqinterval_infnan.
From ValidSDP Require Import zulp.
From ValidSDP Require Import misc.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Require Export parse_reals. (** [Import] would not suffice... because
that file defines [Coercion bigQ2R : BigQ.t_ >-> R] that is used by the
tactics. *)

Fixpoint all_prop (T : Type) (a : T -> Prop) (s : seq T) : Prop :=
  match s with
  | [::] => True
  | x :: s' => a x /\ all_prop a s'
  end.

Lemma all_prop_nthP T (P : T -> Prop) (s : seq T) (x0 : T) :
  (forall i, (i < size s)%N -> P (nth x0 s i)) <-> all_prop P s.
Proof.
elim: s => [//|h t Ht] /=; split.
{ move=> H1; split; [by apply (H1 O)| ].
  by apply Ht => i Hi; apply (H1 i.+1). }
by move=> [Hh Ht'] [ |i] Hi //=; apply Ht.
Qed.

Lemma all_prop_forall T1 T2 (P : T1 -> T2 -> Prop) (s : seq T1) :
  all_prop (fun x : T1 => forall y : T2, P x y) s ->
  forall y : T2, all_prop (fun x : T1 => P x y) s.
Proof.
elim: s => [ |x s IHs] H y =>//=.
by have /= [H1 H2] := H; split; last exact: IHs.
Qed.

Lemma eq_map_all_prop T1 T2 (f1 f2 : T1 ->  T2) (s : seq T1) :
  all_prop (fun x : T1 => f1 x = f2 x) s ->
  [seq f1 i | i <- s] =
  [seq f2 i | i <- s].
Proof.
elim: s => [ |x s IHs] H //=.
have /= [-> H2] := H; congr cons; exact: IHs.
Qed.

Lemma all_prop_cat (T : Type) (a : T -> Prop) (s1 s2 : seq T) :
  all_prop a (s1 ++ s2) <-> all_prop a s1 /\ all_prop a s2.
Proof. by elim: s1 => [ |x s1 IHs] //=; intuition. Qed.

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

Variant Find_exc := not_found.
Variant Poly_exc := not_polynomial.
Variant Goal_exc := not_supported.

(** [list_idx a l = (idx, l)], [idx] being the index of [a] in [l].
    Otherwise return [not_found] *)
Ltac list_idx a l :=
  let rec aux a l n :=
    match l with
    | Datatypes.nil        => not_found
    | Datatypes.cons a _   => constr:((n, l))
    | Datatypes.cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, Datatypes.cons x l))
      | not_found => not_found
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
elim: s => [//|h t Ht H]; split; [by apply (H O)| ].
by apply Ht => i Hi; apply (H (S i)).
Qed.

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

(** ** Part 0: Definition of operational type classes *)

Notation map_mx2_of B :=
  (forall {T T'} {m n : nat}, map_mx_of T T' (B T m n) (B T' m n)) (only parsing).

(** ** Part 1: Generic programs *)

Section generic_soscheck.

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context `{!zero_of T, !opp_of T, !leq_of T}.
Context {ord : nat -> Type} {mx : Type -> nat -> nat -> Type}.
Context {I0n : forall n, I0_class ord n.+1}.
Context {succ0n : forall n, succ0_class ord n.+1}.
Context {natof0n : forall n, nat_of_class ord n.+1}.
Context `{!I0_class ord 1}.

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

Definition posdefcheck (Q : mx F s s) : bool :=
  posdef_check (@float_infnan_spec.fieps fs) (@float_infnan_spec.fieta fs)
               (@float_infnan_spec.finite fs) Q.

End generic_soscheck_size.

Context {s : nat}.
Context `{!I0_class ord s, !succ0_class ord s, !nat_of_class ord s}.

End generic_soscheck.

Section eff_soscheck.

(** *** General definitions for seqmx and effmpoly *)

Context {n : nat}.  (** number of variables of polynomials *)
Context {T : Type}.  (** type of coefficients of polynomials *)

Context `{!zero_of T, !one_of T, !opp_of T, !add_of T, !sub_of T, !mul_of T, !eq_of T}.

Context `{!leq_of T}.

Let ord := ord_instN.

Let mx := @hseqmx.

Context {s : nat}.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2T : F -> T}.  (* exact conversion *)
Context {T2F : T -> F}.  (* overapproximation *)

Definition posdefcheck_eff : mx F s.+1 s.+1 -> bool := posdefcheck.

End eff_soscheck.

(** ** Part 2: Correctness proofs for proof-oriented types and programs *)

Section theory_soscheck.

(** *** Proof-oriented definitions, polymorphic w.r.t scalars *)

Context {n : nat} {T : comRingType}.

Local Instance zero_ssr : zero_of T := 0%R.
Local Instance opp_ssr : opp_of T := fun x => (-x)%R.

Context `{!leq_of T}.

Let ord := ordinal.

Let mx := matrix.

Context {fs : Float_round_up_infnan_spec}.
Let F := FIS fs.
Context {F2T : F -> T}.  (* exact conversion for finite values *)
Context {T2F : T -> F}.  (* overapproximation *)

Global Instance map_mx_ssr : map_mx2_of mx := fun T T' m n f => @map_mx T T' f m n.

Definition posdefcheck_ssr (s : nat) : 'M[F]_s.+1 -> bool := posdefcheck.

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

Require Import bigop_tactics.

Lemma posdefcheck_correct s Q :
  @posdefcheck_ssr s Q ->
  posdef (cholesky.MF2R (cholesky_infnan.MFI2F Q)).
Proof.
rewrite /posdefcheck_ssr /posdefcheck.
apply posdef_check_correct.
Qed.

Hypothesis T2R_multiplicative : multiplicative T2R.
Canonical T2R_morphism_struct := AddRMorphism T2R_multiplicative.

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
  Q2R [bigZZ2Q m e]%bigQ = IZR [m]%bigZ * bpow radix2 [e]%bigZ.
Proof.
case: m => m; case: e => e.
{ rewrite /= BigN.spec_shiftl_pow2 /Q2R mult_IZR Rcomplements.Rdiv_1.
  rewrite (IZR_Zpower radix2) //.
  exact: BigN.spec_pos. }
{ rewrite /= ifF /Q2R /=; last exact/BigN.eqb_neq/BigN.shiftl_eq_0_iff.
  rewrite BigN.spec_shiftl_pow2 /=.
  rewrite bpow_opp -IZR_Zpower; last exact: BigN.spec_pos.
  move: (Zpower_gt_0 radix2 [e]%bigN (BigN.spec_pos _)); simpl.
  by case: Zpower =>// p Hp. }
{ rewrite /= BigN.spec_shiftl_pow2 /= -IZR_Zpower; last exact: BigN.spec_pos.
  by rewrite /Q2R /= Zopp_mult_distr_l mult_IZR Rcomplements.Rdiv_1. }
{ rewrite /= ifF /Q2R /=; last exact/BigN.eqb_neq/BigN.shiftl_eq_0_iff.
  rewrite BigN.spec_shiftl_pow2 /=.
  rewrite bpow_opp -IZR_Zpower; last exact: BigN.spec_pos.
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
  rewrite /Xdiv' ifF; [ |by apply Req_bool_false, R1_neq_R0].
  rewrite /Rdiv Rinv_1 Rmult_1_r /round /rnd_of_mode /=.
  set x := proj_val _; apply (Rle_trans _ x); last first.
  { by apply round_UP_pt, FLX_exp_valid. }
  rewrite /x -!Z2R_int2Z real_FtoX_toR // toR_Float /= Rmult_1_r.
  apply (Rmult_le_reg_r (IZR (int2Z d))).
  { by rewrite -[0%Re]/(IZR 0); apply IZR_lt. }
  rewrite -mult_IZR Hnr Z.mul_1_r /GRing.mul /= Rmult_assoc.
  rewrite Rstruct.mulVr ?Rmult_1_r; [by right| ].
  rewrite -[0%Re]/(IZR 0); apply/negP=>/eqP; apply IZR_neq=>H.
  by move: Hd; rewrite H. }
rewrite /= ifF /=; last first.
{ move: E; rewrite /nr; set nrnr := (_ # _)%bigQ; move: (BigQ_red_den_neq0 nrnr).
  by case (BigQ.red _)=>[//|n' d'] H [] _ <-; move: H=>/negbTE. }
rewrite F.div_correct /Xround /Xdiv real_FtoX_toR //= real_FtoX_toR //=.
rewrite /Xdiv' ifF; last first.
{ apply Req_bool_false; rewrite real_FtoX_toR // toR_Float /= Rmult_1_r.
  rewrite -[0%Re]/(IZR 0); apply IZR_neq.
  move: E; rewrite /nr; set nrnr := (_ # _)%bigQ.
  move: (BigQ_red_den_neq0_aux nrnr).
  by case (BigQ.red _)=>[//|n' d'] H [] _ <-. }
rewrite Z2Pos.id; last first.
{ move: E; rewrite /nr; set nrnr := (_ # _)%bigQ.
  move: (BigQ_red_den_neq0_aux nrnr); case (BigQ.red _)=>[//|? d'] H [] _ <-.
  by case (Z_le_lt_eq_dec _ _ (BigN.spec_pos d'))=>// H'; exfalso; apply H. }
move=> Hnd; rewrite /round /rnd_of_mode /=.
set x := _ / _; apply (Rle_trans _ x); [ |by apply round_UP_pt, FLX_exp_valid].
rewrite /x -!Z2R_int2Z; do 2 rewrite real_FtoX_toR // toR_Float /= Rmult_1_r.
apply (Rmult_le_reg_r (IZR (int2Z d))).
{ by rewrite -[0%Re]/(IZR 0); apply IZR_lt. }
set lhs := _ * _; rewrite Rmult_assoc (Rmult_comm (/ _)) -Rmult_assoc -mult_IZR.
rewrite Hnd {}/lhs /GRing.mul /= Rmult_assoc.
rewrite Rstruct.mulVr ?Rmult_1_r; [right| ]; last first.
{ rewrite -[0%Re]/(IZR 0); apply/negP=>/eqP; apply IZR_neq=>H.
  by move: Hd; rewrite H. }
rewrite mult_IZR Rmult_assoc Rinv_r ?Rmult_1_r //.
move: (erefl nr); rewrite /nr; set nrnr := (_ # _)%bigQ=>_.
move: (BigQ_red_den_neq0_aux nrnr); rewrite /nrnr -/nr E=>H.
by apply IZR_neq.
Transparent F.div.
Qed.

Lemma rat2R_FIS2rat :
 forall x0 : FIS fs, rat2R (FIS2rat x0) = FS_val (FI2FS x0).
Proof.
move=> x; rewrite -bigQ2R_rat /bigQ2R.
case: x => -[ |m e] H /=.
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
case: a Ha ref_a => [ |m e] Ha ref_a;
case: b Hb ref_a => [ |m' e'] Hb ref_b =>//.
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
  have {H} [ |[r H1 H2]] := H e; first by rewrite real_FtoX_toR.
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
  have {H} [ |[r H1 H2]] := H e'; first by rewrite real_FtoX_toR.
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
case: f ref_f => [ |m e] ref_f; case: f' ref_f => [ |m' e'] ref_f //.
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
  case=> ->; rewrite -Z2Pos.inj_1 Z2Pos.inj_iff; [by move<-|done| ].
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
case=>->; rewrite Z2Pos.inj_iff; [by move->| | ];
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

(* Goal forall n, nat_R n.+1 n.+1 <=> nat_R_S_R (nat_Rxx n). *)

Context `{!leq_of A}.
Context `{!leq_of C}.
Context `{!refines (rAC ==> rAC ==> bool_R) leq_op leq_op}.

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

Local Instance refine_posdefcheck {s} :
  refines (RseqmxC eq_F (nat_Rxx s.+1) (nat_Rxx s.+1) ==> bool_R)
    (posdefcheck_ssr (s:=s))
    (posdefcheck_eff (s:=s)).
Proof.
rewrite refinesE=> Q Q' rQ.
rewrite /posdefcheck_ssr /posdefcheck_eff /posdefcheck.
apply refinesP.
eapply refines_apply.
eapply (refine_posdef_check' (fs := fs) (eqFIS := eqFIS)).
exact: eqFIS_P.
exact: id.
Qed.

End refinement_soscheck.

(* TODO: PR CoqEAL ? *)
Lemma nth_lt_list_R T1 T2 (T_R : T1 -> T2 -> Type) (x01 : T1) (x02 : T2) s1 s2 :
  size s1 = size s2 ->
  (forall n, (n < size s1)%N -> T_R (nth x01 s1 n) (nth x02 s2 n)) -> list_R T_R s1 s2.
Proof.
elim: s1 s2 => [ |hs1 ts1 Hind]; [by move=> [//| ]| ].
move=> [//|hs2 ts2 /= Hs H]; apply list_R_cons_R; [by apply (H O)| ].
by apply Hind; [apply eq_add_S|move=> n Hn; apply (H (S n))].
Qed.

(** ** Part 4: The final tactic *)

Lemma map_R_nth (T1 T2 : Type) (x0 : T2) (T_R : T1 -> T2 -> Type) (f : T2 -> T1) l :
  (forall i, (i < size l)%N -> T_R (f (nth x0 l i)) (nth x0 l i)) ->
  list_R T_R [seq f x | x <- l] l.
Proof.
elim: l=> [ |a l IH H]; first by simpl.
constructor 2.
{ by move: (H 0%N) => /=; apply. }
apply IH=> i Hi.
by move: (H i.+1)=> /=; apply; rewrite ltnS.
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
(*-/*)

(** *** The main tactic. *)

Definition posdefcheck_eff_wrapup (Q : seq (seq (s_float bigZ bigZ))) :=
  let s := size Q in
  let s' := s.-1 in
  let Q := map (map F2FI) Q in
  [&&
   s != 0%N,
   size Q == s,
   all (fun e => size e == s) Q &
   posdefcheck_eff
     (s := s')
     (fs := coqinterval_infnan.coqinterval_round_up_infnan)
     Q].

Definition posdef_seqF (mat : seq (seq F.type)) : Prop :=
  let m := seq.size mat in
  posdef (spec_seqmx (H0 := id) m m (map (map toR) mat)).

Theorem posdefcheck_eff_wrapup_correct Q :
  @posdefcheck_eff_wrapup Q -> posdef_seqF Q.
Proof.
rewrite /posdefcheck_eff_wrapup.
set s := size Q.
set s' := s.-1.
set Q' := map (map F2FI) Q.
pose Qb := @spec_seqmx _ (FIS0 fs) _ (id) (s'.+1) (s'.+1) Q'.
case/and4P => Hs HQ'1 HQ'2 Hposdef.
have Hs' : s'.+1 = s by rewrite prednK => [//| ]; rewrite lt0n.
rewrite /posdef_seqF.
set Q'' := spec_seqmx _ _ _.
have Hpos : posdefcheck_ssr Qb.
{ move: Hposdef; apply etrans.
  apply refines_eq, refines_bool_eq.
  refines_apply1; rewrite refinesE.
  eapply Rseqmx_spec_seqmx. (* EMD: should be inferred? *)
  apply/andP; split.
  { by rewrite (eqP HQ'1) Hs'. }
  { by rewrite Hs'. } }
have HQb : posdef (cholesky.MF2R (cholesky_infnan.MFI2F Qb)).
{ by apply posdefcheck_correct with (Q0 := Qb). }
have Hfin := posdef_check_f1 Hpos.
have := HQb.
have HszQ : s'.+1 = size Q by rewrite Hs'.
suff->: Q'' = castmx (HszQ, HszQ) (cholesky.MF2R (cholesky_infnan.MFI2F Qb)).
{ rewrite /posdef.
  intros Hforall v Hv i j.
  move/(_ (castmx (esym HszQ, erefl 1%N) v)) in Hforall.
  have Hv' : castmx (esym HszQ, erefl 1%N) v <> 0%R.
  { move/matrixP in Hv.
    move/matrixP => Kv'.
    apply Hv => k l.
    move/(_ (cast_ord (esym HszQ) k) l) in Kv'.
    rewrite castmxE /= !(cast_ord_id, cast_ord_comp) in Kv'.
    by rewrite Kv' !mxE. }
  move/(_ Hv' i j): Hforall.
  congr Rlt; rewrite !mxE.
  set h := (fun j : 'I_(size Q) => cast_ord (esym HszQ) j).
  have hBij : {on [pred _ | true], bijective h}.
  { exists (fun i : 'I_(s'.+1) => cast_ord HszQ i).
    { by move=> k _; rewrite cast_ord_comp cast_ord_id. }
    { by move=> k _; rewrite /h cast_ord_comp cast_ord_id. } }
  rewrite (reindex h hBij).
  apply eq_bigr => k Hk.
  rewrite /h !(castmxE, cast_ord_comp, cast_ord_id, mxE).
  congr Rmult.
  rewrite (reindex h hBij).
  apply eq_bigr => l Hl.
  by rewrite /h !(castmxE, cast_ord_comp, cast_ord_id, mxE). }
apply/matrixP => i j; rewrite !(mxE, castmxE) /= /map_seqmx /Q'.
have Hrow : forall i : 'I_(size Q), (size (nth [::] Q i) = size Q)%N.
  by admit.
rewrite (nth_map ([::] : seq R)); last by rewrite size_map.
rewrite (nth_map R0);
  last by rewrite (nth_map ([::] : seq F.type)) // size_map Hrow.
rewrite (nth_map ([::] : seq F.type)) //.
rewrite (nth_map F.zero); last by rewrite Hrow.
rewrite (nth_map ([::] : seq FI)); last by rewrite size_map.
rewrite (nth_map (F2FI F.zero));
  last by rewrite (nth_map ([::] : seq F.type)) // size_map Hrow.
rewrite (nth_map ([::] : seq F.type)) //.
rewrite (nth_map F.zero); last by rewrite Hrow.
have HFin' : forall (i j : 'I_(size Q)),
  F.real (F2FI (nth F.zero(*?*) (nth [::] Q i) j)).
{ by admit. }
have H1 := HFin' i j.
have H2 := F2FI_correct H1.
by rewrite -H2.
Admitted.

Require matrices.

Ltac posdef_check :=
  match goal with
  | [ |- posdef_seqF ?Q ] =>
    abstract (apply @posdefcheck_eff_wrapup_correct;
      vm_cast_no_check (erefl true))
  end.

(* Eval vm_compute in posdef_check matrices.m4. Bug. *)
Time Eval vm_compute in posdefcheck_eff_wrapup matrices.m4.

Goal posdef_seqF matrices.m4.
Time posdef_check.
Qed.
