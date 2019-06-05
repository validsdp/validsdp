(** * Type for real numbers with bounded absolute value. *)

Require Import Reals Flocq.Core.Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory.

Section Bounded.

(** The type of bounded value (coercible to R). *)
Record bounded (r : R) := { bounded_val :> R;
                            bounded_prop : Rabs bounded_val <= r }.

(** A bound. *)
Variable r : R.

(** Must be non negative. *)
Hypothesis Hr : (0 <= r)%Re.

(** [bounded_0] is the value 0. *)
Definition bounded_0 :=
  {| bounded_val := 0;
     bounded_prop := (Rle_trans (Rabs 0) 0 r (or_intror Rabs_R0) Hr) |}.

Definition cast_bounded (r' : R) (Hrr' : r = r') (b : bounded r) :
  bounded r' :=
  {| bounded_val := bounded_val b;
     bounded_prop := (Rle_trans _ _ _ (bounded_prop b) (or_intror _ Hrr')) |}.

Definition widen_bounded (r' : R) (Hrr' : (r <= r')%Re) (b : bounded r) :
  bounded r' :=
  {| bounded_val := bounded_val b;
     bounded_prop := (Rle_trans _ _ _ (bounded_prop b) Hrr') |}.

Lemma bounded_opp_proof b : (Rabs b <= r -> Rabs (- b) <= r)%Re.
Proof. by move=> H; rewrite Rabs_Ropp. Qed.

(** [bounded_opp b] is [-b] *)
Definition bounded_opp (b : bounded r) : bounded r :=
  {| bounded_val := (- (bounded_val b))%Re;
     bounded_prop := bounded_opp_proof (bounded_prop b) |}.

(** Put two bounded values into one. *)
Lemma bounded_distrl (b1 b2 : bounded r) (r1 r2 : R) :
  exists b' : bounded r,
  (b1 * r1 + b2 * r2 = b' * (Rabs r1 + Rabs r2) :> R)%Re.
Proof.
have Pr1 := Rabs_pos r1. have Pr2 := Rabs_pos r2.
case (Req_dec (Rabs r1 + Rabs r2) 0)%Re => Hr1.
{ have Zr1 : (r1 = 0)%Re by apply Rabs_eq_R0; lra.
  have Zr2 : (r2 = 0)%Re by apply Rabs_eq_R0; lra.
  by exists bounded_0; rewrite Zr1 Zr2 /=; ring. }
set (bv := ((b1 * r1 + b2 * r2) / (Rabs r1 + Rabs r2))%Re).
suff H : (Rabs bv <= r)%Re.
{ exists (Build_bounded H); rewrite /bv /=; field; lra. }
rewrite /bv {bv} /Rdiv Rabs_mult Rabs_Rinv //.
have Hnn := Rabs_pos (Rabs r1 + Rabs r2).
have Hp : (0 < Rabs (Rabs r1 + Rabs r2)) by apply Rabs_pos_lt.
apply (Rmult_le_reg_r (Rabs (Rabs r1 + Rabs r2))); [by []|].
field_simplify; [|lra]; try rewrite /Rdiv Rinv_1 !Rmult_1_r.
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
rewrite !Rabs_mult (Rabs_right (_ + _)); [|lra].
rewrite (Rmult_comm _ r) Rmult_plus_distr_l.
by apply Rplus_le_compat; apply Rmult_le_compat_r; [|case b1| |case b2].
Qed.

(** Put an array of bounded values into one. *)
Lemma big_bounded_distrl n (ba : bounded r ^ n) (a : R ^ n) :
  exists b' : bounded r,
  (\sum_i (ba i * a i)%Re = b' * (\sum_i (Rabs (a i))) :> R)%Re.
Proof.
move: n ba a; elim=> [|n IHn] ba a.
{ by exists bounded_0; rewrite big_ord0 Rmult_0_l. }
have [b' Hb'] := IHn [ffun i => ba (lift ord0 i)] [ffun i => a (lift ord0 i)].
set (hb1 := \sum_i ([ffun i => ba (lift ord0 i)] i
                    * [ffun i => a (lift ord0 i)] i)%Re).
set (hb2 := \sum_i Rabs ([ffun i0 => a (lift ord0 i0)] i)).
move: Hb'; rewrite -/hb1 -/hb2; move=> Hb'.
have [b'' Hb''] := (bounded_distrl (ba ord0) b' (a ord0) hb2).
exists b''; rewrite big_ord_recl.
apply eq_trans with (ba ord0 * a ord0 + hb1)%Re; [apply Rplus_eq_compat_l|].
{ by rewrite /hb1; apply /eq_bigr => i _; rewrite !ffunE. }
rewrite Hb' Hb'' big_ord_recl.
apply Rmult_eq_compat_l, Rplus_eq_compat_l.
rewrite /hb2 Rabs_pos_eq; [|by apply big_sum_Rabs_pos].
by apply /eq_bigr => i _; rewrite ffunE.
Qed.

(** Useful for overapproximating a complex term (r1)
    with a simpler one (r2). *)
Lemma bounded_larger_factor (b : bounded r) (r1 r2 : R) :
  (Rabs r1 <= Rabs r2 -> exists b' : bounded r, b * r1 = b' * r2 :> R)%Re.
Proof.
move=> Hr12; case (Req_dec r2 0) => Hr2.
{ have Hr1 : r1 = 0.
  { rewrite Hr2 Rabs_R0 in Hr12.
    by apply Rabs_eq_R0, Rle_antisym; [|apply Rabs_pos]. }
  by exists bounded_0; rewrite Hr1 Hr2 !Rmult_0_r. }
suff H : (Rabs (b * r1 / r2) <= r).
{ by exists (Build_bounded H); simpl; field. }
rewrite /Rdiv !Rabs_mult Rabs_Rinv //.
have H0 := Rabs_no_R0 r2 Hr2; have H1 := Rabs_pos r1.
have H2 : (0 < Rabs r2) by lra.
apply (Rmult_le_reg_r (Rabs r2)); [by []|].
rewrite Rmult_assoc Rinv_l; [rewrite Rmult_1_r|lra].
by apply Rmult_le_compat; try apply Rabs_pos; try case b.
Qed.

End Bounded.

(** Translation from inequalities to bounded terms. *)
Lemma bounded_le_1 (r1 r2 : R) :
  Rabs r1 <= r2 -> exists b : bounded 1, (r1 = b * r2)%Re.
Proof.
move=> Hr12; case (Req_dec r2 0) => Hr2.
{ exists (bounded_0 Rle_0_1); rewrite Hr2 Rmult_0_r.
  by apply Rabs_eq_R0, Rle_antisym; [lra|apply Rabs_pos]. }
suff H : (Rabs (r1 / r2) <= 1).
{ by exists (Build_bounded H); rewrite Rmult_assoc Rinv_l // Rmult_1_r. }
rewrite Rabs_mult Rabs_Rinv //.
have HAr2 : (0 < Rabs r2) by move: (Rabs_pos r2) (Rabs_no_R0 r2 Hr2); lra.
apply (Rmult_le_reg_r (Rabs r2)); [by []|rewrite Rmult_1_l].
rewrite Rmult_assoc Rinv_l; [rewrite Rmult_1_r|lra].
apply (Rle_trans _ _ _ Hr12 (Rle_abs r2)).
Qed.

Lemma bounded_le_1_abs (r1 r2 : R) :
  Rabs r1 <= r2 -> exists b : bounded 1, (Rabs r1 = b * r2)%Re.
Proof.
move=> Hr12.
have [b Hb] := bounded_le_1 Hr12.
split_Rabs.
{ exists (bounded_opp b); rewrite Hb /=; ring. }
by exists b; rewrite Hb.
Qed.

Lemma bounded_scale (r1 r2 : R) (b1 : bounded r1) :
  (0 < r2 -> exists b2 : bounded r2, b1 = b2 * (r1 / r2) :> R)%Re.
Proof.
move=> Hr2; case (Rle_or_lt r1 0) => Hr1.
{ exists (bounded_0 (Rlt_le _ _ Hr2)); rewrite Rmult_0_l.
  by apply Rabs_eq_R0, Rle_antisym;
    [apply (Rle_trans _ _ _ (bounded_prop b1))|apply Rabs_pos]. }
suff H : (Rabs (b1 * (r2 / r1)) <= r2).
{ exists (Build_bounded H); simpl; field; lra. }
rewrite !Rabs_mult Rabs_Rinv; [|lra].
rewrite (Rabs_right r1); [|lra]; rewrite (Rabs_right r2); [|lra].
apply (Rmult_le_reg_r r1); [by []|].
replace (_ * _)%Re with (r2 * Rabs b1)%Re; [|by field; lra].
by apply Rmult_le_compat_l; [lra|case b1].
Qed.

Lemma bounded_plus_proof (r1 r2 : R) (b1 : bounded r1) (b2 : bounded r2) :
  (Rabs (b1 + b2) <= r1 + r2)%Re.
Proof.
apply (Rle_trans _ _ _ (Rabs_triang _ _)).
by apply Rplus_le_compat; [case b1|case b2].
Qed.

(** Sum of bounded values. *)
Definition bounded_plus (r1 r2 : R) (b1 : bounded r1) (b2 : bounded r2) :=
  {| bounded_val := (b1 + b2)%Re; bounded_prop := bounded_plus_proof b1 b2 |}.

Lemma bounded_mult_proof (r1 r2 : R) (b1 : bounded r1) (b2 : bounded r2) :
  (Rabs (b1 * b2) <= r1 * r2)%Re.
Proof.
case (Rlt_or_le r1 0) => Hr1.
{ casetype False; apply (Rlt_irrefl 0).
  have Hb1 := bounded_prop b1.
  apply (Rle_lt_trans 0 (Rabs b1)); [apply Rabs_pos|lra]. }
case (Rlt_or_le r2 0) => Hr2.
{ casetype False; apply (Rlt_irrefl 0).
  have Hb2 := bounded_prop b2.
  apply (Rle_lt_trans 0 (Rabs b2)); [apply Rabs_pos|lra]. }
by rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos;
  [case b1|case b2].
Qed.

(** Product of bounded values. *)
Definition bounded_mult (r1 r2 : R)
           (b1 : bounded r1) (b2 : bounded r2) : bounded (r1 * r2) :=
  {| bounded_val := (b1 * b2)%Re; bounded_prop := bounded_mult_proof b1 b2 |}.

Definition bounded_mult_1_l (r : R)
           (b1 : bounded 1) (b : bounded r) : bounded r :=
  cast_bounded (Rmult_1_l r) (bounded_mult b1 b).

Definition bounded_mult_1_r (r : R)
           (b : bounded r) (b1 : bounded 1) : bounded r :=
  cast_bounded (Rmult_1_r r) (bounded_mult b b1).
