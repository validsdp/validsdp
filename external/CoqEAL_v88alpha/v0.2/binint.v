(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

Require Import hrel refinements pos.

(******************************************************************************)
(* Attempt to refine SSReflect integers (ssrint) are to a new type            *)
(* paremetrized by positive numbers (represented by a sigma type) and natural *)
(* numbers. This gives simpler proofs than in binint, but in order for this   *)
(* to be useful the parametricity part of the library must be used to change  *)
(* the representation of positive numbers and naturals to more efficient      *)
(* representations (e.g. N) which has not been done yet.                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory Refinements.

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section binint_op.
Variable N P : Type.

Import Op AlgOp.
Local Open Scope computable_scope.

Inductive Z := Zpos of N | Zneg of P.

Definition Zmatch T (n : Z) f g : T :=
   match n with Zpos p => f p | Zneg n => g n end.

Context `{zero N, one N, sub N, add N, mul N, leq N, lt N, eq N}.
Context `{one P, sub P, add P, mul P, eq P, leq P, lt P}.
Context `{cast_class N P, cast_class P N}.
Context `{spec_of N nat, spec_of P pos}.

Global Instance zeroZ : zero Z := Zpos 0.
Global Instance oneZ : one Z := Zpos 1.

Global Instance addZ : add Z := fun x y : Z => match x, y with
  | Zpos x, Zpos y => Zpos (x + y)
  | Zneg x, Zneg y => Zneg (x + y)
  | Zpos x, Zneg y => if (cast y <= x) then Zpos (x - cast y)
                                       else Zneg (cast (cast y - x))
  | Zneg x, Zpos y => if (cast x <= y) then Zpos (y - cast x)
                                       else Zneg (cast (cast x - y))
  end.

Global Instance oppZ : opp Z := fun x : Z => match x with
  | Zpos x => if (x == 0)%C then 0%C else Zneg (cast x)
  | Zneg x => Zpos (cast x)
  end.

Global Instance subZ : sub Z := fun x y : Z => match x, y with
  | Zpos x, Zneg y => Zpos (x + cast y)
  | Zneg x, Zpos y => if (y == 0)%C then Zneg x else Zneg (x + cast y)
  | Zpos x, Zpos y => if (y <= x) then Zpos (x - y)
                                  else Zneg (cast (y - x))
  | Zneg x, Zneg y => if (cast x <= cast y) then Zpos (cast y - cast x)
                                            else Zneg (cast (cast x - cast y))
  end.

Global Instance eqZ : eq Z := fun x y : Z => match x, y with
  | Zpos x, Zpos y => (x == y)
  | Zneg x, Zneg y => (x == y)
  | _, _ => false
  end.

Global Instance mulZ : mul Z := fun x y : Z => match x, y with
  | Zpos x, Zpos y => Zpos (x * y)
  | Zneg x, Zpos y => if (y == 0)%C then 0%C else Zneg (x * cast y)
  | Zpos x, Zneg y => if (x == 0)%C then 0%C else Zneg (cast x * y)
  | Zneg x, Zneg y => Zpos (cast x * cast y)
  end.

Global Instance leqZ : leq Z := fun x y : Z => match x, y with
  | Zpos x, Zpos y => (x <= y)
  | Zneg x, Zneg y => (y <= x)
  | Zneg _, Zpos _ => true
  | Zpos _, Zneg _ => false
  end.

Global Instance ltZ : lt Z := fun x y : Z => match x, y with
  | Zpos x, Zpos y => (x < y)
  | Zneg x, Zneg y => (y < x)
  | Zneg _, Zpos _ => true
  | Zpos _, Zneg _ => false
  end.

Global Instance cast_NZ : cast_class N Z := fun n : N => Zpos n.

Global Instance cast_PZ : cast_class P Z := fun n : P => Zpos (cast n).

Global Instance cast_ZN : cast_class Z N := fun z =>
 if z is Zpos n then n else 0.

Global Instance cast_ZP : cast_class Z P := fun z => cast (cast_ZN z).

Global Instance specZ : spec_of Z int :=
  fun x => (match x with
             | Zpos p => (spec p)%:Z
             | Zneg n => - (val (spec n))%:Z
           end)%R.

End binint_op.

(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section binint_theory.

Notation Znp := (Z nat pos).

Definition Z_of_int (m : int) : Znp := match m with
  | Posz m => Zpos _ m
  | Negz m => Zneg _ (posS m)
  end.

Definition int_of_Z (m : Znp) : int := match m with
  | Zpos p => p%:Z
  | Zneg p => -(val p)%:Z
  end.

Lemma Z_of_intK : pcancel Z_of_int (some \o int_of_Z).
Proof. by rewrite /Z_of_int /int_of_Z => [[[]|]]. Qed.

Definition Rint : int -> Znp -> Prop := fun_hrel int_of_Z.

Import Op AlgOp.
Instance zero_nat : zero nat := 0%N.
Instance one_nat  : one nat  := 1%N.
Instance add_nat  : add nat  := addn.
Instance sub_nat  : sub nat  := subn.
Instance mul_nat  : mul nat  := muln.
Instance leq_nat  : leq nat  := ssrnat.leq.
Instance lt_nat   : lt nat  := ssrnat.ltn.
Instance eq_nat   : eq nat   := eqtype.eq_op.

Instance one_pos : one pos := posS 0.
Instance add_pos : add pos := fun m n => insubd (posS 0) (val m + val n)%N.
Instance sub_pos : sub pos := fun m n => insubd (posS 0) (val m - val n)%N.
Instance mul_pos : mul pos := fun m n => insubd (posS 0) (val m * val n)%N.
Instance leq_pos : leq pos := fun m n => (val m <= val n)%N.
Instance lt_pos  : lt pos  := fun m n => (val m < val n)%N.
Instance eq_pos  : eq pos  := eqtype.eq_op.

Instance cast_pos_nat : cast_class pos nat := val.
Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

Instance spec_nat : spec_of nat nat := spec_id.
Instance spec_pos : spec_of pos pos := spec_id.

Lemma RintE n x : param Rint n x -> n = int_of_Z x.
Proof. by rewrite paramE. Qed.

Instance Rint_0 : param Rint 0 0%C.
Proof. by rewrite paramE. Qed.

Instance Rint_1 : param Rint 1 1%C.
Proof. by rewrite paramE. Qed.

Instance Rint_Posz : param (Logic.eq ==> Rint) Posz cast.
Proof. by rewrite paramE=> n n' <-. Qed.

Instance Rint_pos_to_int : param (Logic.eq ==> Rint) pos_to_int cast.
Proof. by rewrite paramE=> n n' <-; rewrite /pos_to_int natz. Qed.

Instance Rint_int_to_nat : param (Rint ==> Logic.eq) int_to_nat cast.
Proof.
apply param_abstr => a b rab; rewrite [a]RintE paramE {a rab}.
case: b => [n|[n n_gt0]] //=; rewrite /cast /cast_ZP /cast_ZN /int_to_nat.
  by rewrite ltz_nat; have [->|] // := posnP n.
by rewrite ler_gtF // oppr_le0 ltrW.
Qed.

Instance Rint_int_to_pos : param (Rint ==> Logic.eq) int_to_pos cast.
Proof.
apply param_abstr => a b rab; rewrite /int_to_pos.
by rewrite [int_to_nat a]param_eq paramE {a rab}.
Qed.

Instance Rint_add : param (Rint ==> Rint ==> Rint) +%R +%C.
Proof.
rewrite paramE /Rint /fun_hrel /add_op /= => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; rewrite ?(add0r, addr0) //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [yx|xy] /= := leqP; first by rewrite addrC subzn.
  by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
by rewrite !insubdK -?topredE /= ?addn_gt0 ?valP // -opprB opprK addrC.
Qed.

Instance Rint_opp : param (Rint ==> Rint) -%R -%C.
Proof.
rewrite paramE  /Rint /fun_hrel => _ x <-.
by case: x => [[]|] //= n; rewrite ?insubdK ?opprK.
Qed.

Instance Rint_sub : param (Rint ==> Rint ==> Rint) subr sub_op.
Proof.
rewrite paramE /Rint /fun_hrel /subr /sub_op => _ x <- _ y <-.
case: x y => [x|x] [y|y]; rewrite ?opprK //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite subr0.
  by rewrite !insubdK -?opprD -?topredE //= ?addn_gt0 ?valP ?lt0n.
have [yx|xy] /= := leqP; first by rewrite addrC subzn.
by rewrite insubdK // -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
Qed.

Instance Rint_eq : param (Rint ==> Rint ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
rewrite paramE /Rint /fun_hrel /eq_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; rewrite ?eqr_opp // ?[- _ == _]eq_sym;
by rewrite gtr_eqF // (@ltr_le_trans _ 0) // ltr_oppl oppr0 [_ < _]valP.
Qed.

Instance Rint_leq : param (Rint ==> Rint ==> Logic.eq) Num.le leq_op.
Proof.
rewrite paramE /Rint /fun_hrel /eq_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=.
- by rewrite lerNgt (@ltr_le_trans _ 0) //; rewrite oppr_lt0; apply: valP.
- by rewrite (@ler_trans _ 0) // oppr_le0.
by rewrite ler_opp2.
Qed.

Instance Rint_lt : param (Rint ==> Rint ==> Logic.eq) Num.lt lt_op.
Proof.
rewrite paramE /Rint /fun_hrel /eq_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=.
- by rewrite ltrNge (@ler_trans _ 0) // oppr_le0.
- by rewrite (@ltr_le_trans _ 0) // oppr_lt0; apply: valP.
by rewrite ltr_opp2.
Qed.

Instance Rint_mul : param (Rint ==> Rint ==> Rint) *%R *%C.
Proof.
rewrite paramE /Rint /fun_hrel /mul_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; simpC; last by rewrite mulrNN.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite mul0r.
  by rewrite mulrN !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
have [->|y_neq0 /=] := (altP eqP); first by rewrite mulr0.
by rewrite mulNr !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
Qed.

Instance Rint_specZ x : param Rint (spec x) x.
Proof. by rewrite !paramE; case: x. Qed.

Instance Rint_specZ' :
  param (Rint ==> Logic.eq) id spec.
Proof. by rewrite paramE => a a' ra; rewrite [spec _]RintE. Qed.

(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section binint_parametricity.

Section Zrefinement.

Variables N N' P P' : Type.
Variables (RN : N -> N' -> Prop) (RP : P -> P' -> Prop).

Local Notation Z' := (Z N' P').
Local Notation Z  := (Z N P).

Definition RZ : Z -> Z' -> Prop := fun x y => match x, y with
  | Zpos x, Zpos y => RN x y
  | Zneg x, Zneg y => RP x y
  | _, _ => False
  end.

Lemma param_Zpos : (getparam RN ==> getparam RZ)%rel (@Zpos N P) (@Zpos N' P').
Proof. by rewrite !paramE. Qed.

Lemma param_Zneg : (getparam RP ==> getparam RZ)%rel (@Zneg N P) (@Zneg N' P').
Proof. by rewrite !paramE. Qed.

Lemma param_Zmatch T T' (R : T -> T' -> Prop) :
  (param RZ ==> getparam (RN ==> R) ==> getparam (RP ==> R) ==> getparam R)%rel
  (@Zmatch _ _ _) (@Zmatch _ _ _).
Proof.
rewrite ?paramE => x x' rx f f' rf g g' rg.
by case: x x' rx=> [a|b] [a'|b'] //= rab; [apply: rf|apply: rg].
Qed.

End Zrefinement.

Arguments param_Zmatch {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments param_Zpos {_ _ _ _ _ _ _ _ _}.
Arguments param_Zneg {_ _ _ _ _ _ _} _ _.

Hint Extern 1 (getparam _ _ _) => eapply param_Zmatch: typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
eapply param_Zneg: typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
eapply param_Zpos: typeclass_instances.

Section binint_nat_pos.

Variables N P : Type.
Variables (Rnat : nat -> N -> Prop) (Rpos : pos -> P -> Prop).

Definition RZNP := (Rint \o RZ Rnat Rpos)%rel.

Context `{zero N, one N, sub N, add N, mul N, leq N, eq N, lt N}.
Context `{one P, sub P, add P, mul P, eq P, leq P, lt P}.
Context `{cast_class N P, cast_class P N}.
Context `{spec_of N nat, spec_of P pos}.

Context `{!param Rnat 0%N 0%C, !param Rnat 1%N 1%C}.
Context `{!param Rpos pos1 1%C}.
Context `{!param (Rnat ==> Rnat ==> Rnat) addn +%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) add_pos +%C}.
Context `{!param (Rnat ==> Rnat ==> Rnat) subn sub_op}.
Context `{!param (Rpos ==> Rpos ==> Rpos) sub_pos sub_op}.
Context `{!param (Rnat ==> Rnat ==> Rnat) muln *%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) mul_pos *%C}.
Context `{!param (Rnat ==> Rnat ==> Logic.eq) ssrnat.leq leq_op}.
Context `{!param (Rnat ==> Rnat ==> Logic.eq) ssrnat.ltn lt_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) leq_pos leq_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) lt_pos lt_op}.
Context `{!param (Rnat ==> Rpos) (insubd pos1) cast}.
Context `{!param (Rpos ==> Rnat) val cast}.
Context `{!param (Rnat ==> Rnat ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{forall x, param Rnat (spec x) x,
          forall x, param Rpos (spec x) x}.
Context `{!param (Rnat ==> Logic.eq) spec_id spec,
          !param (Rpos ==> Logic.eq) spec_id spec}.

Local Notation Z := (Z N P).

Global Instance RZNP_zeroZ  : param RZNP 0 0%C.
Proof. exact: param_trans. Qed.

Global Instance RZNP_oneZ  : param RZNP 1 1%C.
Proof. exact: param_trans. Qed.

Global Instance RZNP_castNZ : param (Rnat ==> RZNP) Posz cast.
Proof. exact: param_trans. Qed.

Global Instance RZNP_castPZ : param (Rpos ==> RZNP) pos_to_int cast.
Proof. exact: param_trans. Qed.

Global Instance RZNP_castZN: param (RZNP ==> Rnat) int_to_nat cast.
Proof. by eapply param_trans; tc; tc. Qed.

Global Instance RZNP_castZP: param (RZNP ==> Rpos) int_to_pos cast.
Proof. by rewrite /int_to_pos /cast /cast_ZP; apply: get_param. Qed.

Global Instance RZNP_addZ : param (RZNP ==> RZNP ==> RZNP) +%R +%C.
Proof. exact: param_trans. Qed.

Global Instance RZNP_mulZ : param (RZNP ==> RZNP ==> RZNP) *%R *%C.
Proof. exact: param_trans. Qed.

Global Instance RZNP_oppZ : param (RZNP ==> RZNP) -%R -%C.
Proof. exact: param_trans. Qed.

Global Instance RZNP_subZ : param (RZNP ==> RZNP ==> RZNP) subr sub_op.
Proof. exact: param_trans. Qed.

Global Instance RZNP_eqZ :
  param (RZNP ==> RZNP ==> Logic.eq) eqtype.eq_op (@Op.eq_op Z _).
Proof. exact: param_trans. Qed.

Global Instance RZNP_leqZ :
  param (RZNP ==> RZNP ==> Logic.eq) Num.le (@Op.leq_op Z _).
Proof. exact: param_trans. Qed.

Global Instance RZNP_ltZ :
  param (RZNP ==> RZNP ==> Logic.eq) Num.lt (@Op.lt_op Z _).
Proof. exact: param_trans. Qed.

Instance param_eq_refl A (x : A) : param Logic.eq x x | 999.
Proof. by rewrite paramE. Qed.
Instance param_fun_eq1 A B (f : A -> B) :
  param (Logic.eq ==> Logic.eq) f f.
Proof. by rewrite !paramE => x x' ->. Qed.
Instance param_fun_eq2 A B C (f : A -> B -> C) :
  param (Logic.eq ==> Logic.eq ==> Logic.eq) f f.
Proof. by rewrite !paramE => x x' -> y y' ->. Qed.

Global Instance RZNP_specZ' : param (RZNP ==> Logic.eq) spec_id spec.
Proof. exact: param_trans. Qed.

End binint_nat_pos.
End binint_parametricity.
End binint_theory.
