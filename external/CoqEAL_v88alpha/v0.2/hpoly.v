(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.

Require Import refinements pos hrel.

(******************************************************************************)
(** This file implements sparse polynomials in sparse Horner normal form.     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Refinements.Op AlgOp.

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section hpoly.

Context {A N pos : Type}.

Inductive hpoly A := Pc : A -> hpoly A
                   | PX : A -> pos -> hpoly A -> hpoly A.

Section hpoly_op.

Context `{zero A, one A, add A, sub A, opp A, mul A, eq A}.
Context `{one pos, add pos, sub pos, eq pos, lt pos}.
Context `{zero N, one N, eq N, lt N, add N, sub N}.
Context `{cast_class N pos, cast_class pos N}.

Local Open Scope computable_scope.

Fixpoint normalize (p : hpoly A) : hpoly A := match p with
  | Pc c => Pc c
  | PX a n p => match normalize p with
    | Pc c => PX a n (Pc c)
    | PX b m q => if (b == 0)%C then PX a (m + n) q else PX a n (PX b m q)
    end
  end.

Fixpoint from_seq (p : seq A) : hpoly A := match p with
  | [::] => Pc 0
  | [:: c] => Pc c
  | x :: xs => PX x 1 (from_seq xs)
  end.

Global Instance zero_hpoly : zero (hpoly A) := Pc 0.
Global Instance one_hpoly  : one (hpoly A)  := Pc 1.

Fixpoint map_hpoly A B (f : A -> B) (p : hpoly A) : hpoly B := match p with
  | Pc c     => Pc (f c) 
  | PX a n p => PX (f a) n (map_hpoly f p)
  end.

Global Instance opp_hpoly : opp (hpoly A) := map_hpoly -%C.
Global Instance scale_hpoly : scale A (hpoly A) := fun a => map_hpoly [eta *%C a].

Fixpoint addXn_const n a (q : hpoly A) := match q with
  | Pc b      => if (n == 0)%C then Pc (a + b) else PX b (cast n) (Pc a)
  | PX b m q' => let cn := cast n in
    if (n == 0)%C then PX (a + b) m q' else
      if (n == cast m)%C    then PX b m (addXn_const 0 a q') else
      if n < cast m then PX b cn (PX a (m - cn) q')
                    else PX b m (addXn_const (n - cast m)%C a q')
  end.

Fixpoint addXn (n : N) p q {struct p} := match p, q with
  | Pc a      , q      => addXn_const n a q
  | PX a n' p', Pc b   => if (n == 0)%C then PX (a + b) n' p'
                                        else PX b (cast n) (PX a n' p')
  | PX a n' p', PX b m q' =>
    if (n == 0)%C then
      if (n' == m)%C then PX (a + b) n' (addXn 0 p' q') else
      if n' < m      then PX (a + b) n' (addXn 0 p' (PX 0 (m - n') q'))
                     else PX (a + b) m (addXn (cast (n' - m)) p' q')
    else addXn (n + cast n') p' (addXn_const 0 b (addXn_const n a (PX 0 m q')))
  end.

(* (* This definition is nicer but Coq doesn't like it *) *)
(* Fixpoint add_hpoly_op p q := match p, q with *)
(*   | Pc a, Pc b     => Pc (a + b) *)
(*   | PX a n p, Pc b => PX (a + b) n p *)
(*   | Pc a, PX b n p => PX (a + b) n p *)
(*   | PX a n p, PX b m q => *)
(*   if (m == n)%C then PX (a + b) n (add_hpoly_op p q) *)
(*                 else if n < m then PX (a + b) n (add_hpoly_op p (PX 0 (m - n) q)) *)
(*                               else PX (a + b) m (add_hpoly_op q (PX 0 (n - m) p)) *)
(*   end. *)

Global Instance add_hpoly : add (hpoly A) := addXn 0.
Global Instance sub_hpoly : sub (hpoly A) := fun p q => p + - q.

Definition shift_hpoly n (p : hpoly A) := PX 0 n p.

Global Instance mul_hpoly : mul (hpoly A) := fix f p q := match p, q with
  | Pc a, q => a *: q
  | p, Pc b => b *: p
  | PX a n p, PX b m q => 
     shift_hpoly (n + m) (f p q) + shift_hpoly m (a *: q) + 
    (shift_hpoly n (b *: p) + Pc (a * b))
  end.

Fixpoint eq0_hpoly (p : hpoly A) : bool := match p with
  | Pc a      => (a == 0)%C
  | PX a n p' => (eq0_hpoly p') && (a == 0)%C
  end.

Global Instance eq_hpoly : eq (hpoly A) := fun p q => eq0_hpoly (p - q).

(* Alternative definition, should be used with normalize: *)
(* Fixpoint eq_hpoly_op p q {struct p} := match p, q with *)
(*   | Pc a, Pc b => (a == b)%C *)
(*   | PX a n p', PX b m q' => (a == b)%C && (cast n == cast m) && (eq_hpoly_op p' q') *)
(*   | _, _ => false *)
(*   end. *)

Fixpoint size_hpoly (p : hpoly A) : N := 
  if eq0_hpoly p then 0%C else match p with
  | Pc a => 1%C
  | PX a n p' => if eq0_hpoly p' then 1%C else (cast n + size_hpoly p')%C
  end.

(* Fixpoint split_hpoly (m : N) p : hpoly A * hpoly A := match p with *)
(*   | Pc a => (Pc a, Pc 0) *)
(*   | PX a n p' => if (m == 0)%C then (Pc 0,p) *)
(*     else let (p1,p2) := split_hpoly (m - cast n)%C p' in (PX a n p1, p2) *)
(*   end. *)

End hpoly_op.
End hpoly.

Arguments Pc {_ _} _.
Arguments PX {_ _} _ _ _.

(**************************************************)
(* Interlude: parametric properties of hpoly_hrel *)
(**************************************************)

Lemma getparamE A B (R : A -> B -> Prop) : getparam R = param R.
Proof. by rewrite !paramE. Qed.

Fixpoint hpoly_elim {T A P} (fc : A -> T) (fX : A -> P -> hpoly A -> T)
         (p : hpoly A) : T :=
  match p with
    | Pc c => fc c
    | PX a n p => fX a n p
  end.

Section ParamHpoly.

Variables (A B : Type) (R : A -> B -> Prop) 
          (P P' : Type) (RP : P -> P' -> Prop).
 
Fixpoint hpoly_hrel (p : @hpoly P A) (q : @hpoly P' B) : Prop :=
  match p, q with 
    | Pc a, Pc b => R a b
    | PX a m p, PX b n q => [/\ R a b, RP m n & hpoly_hrel p q]
    | _, _ => False
  end.

Lemma hpoly_hrel_Pc : (getparam R ==> getparam hpoly_hrel)%rel Pc Pc.
Proof. by rewrite !paramE. Qed.

Lemma hpoly_hrel_PX : (getparam R ==> getparam RP ==>
  getparam hpoly_hrel ==> getparam hpoly_hrel)%rel PX PX.
Proof. by rewrite !paramE. Qed.

Lemma hpoly_hrel_elim (T T' : Type) (RT : T -> T' -> Prop) :
  (getparam (R ==> RT) ==> getparam (R ==> RP ==> hpoly_hrel ==> RT) ==>
            getparam hpoly_hrel ==> getparam RT)%rel hpoly_elim hpoly_elim.
Proof.
rewrite !getparamE => ??? ???.
elim=> [c|a m p ihp] [d|b n q]; rewrite !paramE //=.
  by move=> Rcd; exact: paramP.
by move=> [???]; exact: paramP.
Qed.

End ParamHpoly.

Lemma param_map_hpoly A A' B B' P P' (rA : A -> A' -> Prop) 
  (rB : B -> B' -> Prop) (rP : P -> P' -> Prop): 
    (getparam (rA ==> rB) ==> getparam (hpoly_hrel rA rP) ==>
      getparam (hpoly_hrel rB rP))%rel (@map_hpoly P A B) (@map_hpoly P' A' B').
Proof.
rewrite !paramE => f f' rf. 
elim => [a [b rab|]|a n p ih [|b m q [rab rnm rpq]]] //=; first exact: rf.
split; [exact: rf|exact: rnm|apply: ih; exact: rpq].
Qed.

Arguments hpoly_hrel_Pc {_ _ _ _ _ _ _ _ _}.
Arguments hpoly_hrel_PX {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments hpoly_hrel_elim {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments param_map_hpoly {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply hpoly_hrel_Pc : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply hpoly_hrel_PX : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply hpoly_hrel_elim : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply param_map_hpoly : typeclass_instances.

(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section hpoly_theory.

Variable A : comRingType.

Instance zeroA : zero A := 0%R.
Instance oneA  : one A  := 1%R.
Instance addA  : add A  := +%R.
Instance oppA  : opp A  := -%R.
Instance subA  : sub A  := subr.
Instance mulA  : mul A  := *%R.
Instance eqA   : eq A   := eqtype.eq_op.

Instance one_pos : one pos := posS 0.
Instance add_pos : add pos := fun m n => insubd (posS 0) (val m + val n)%N.
Instance sub_pos : sub pos := fun m n => insubd (posS 0) (val m - val n)%N.
Instance mul_pos : mul pos := fun m n => insubd (posS 0) (val m * val n)%N.
Instance eq_pos  : eq pos  := eqtype.eq_op.
Instance lt_pos  : lt pos  := fun m n => val m < val n.

Instance zero_nat : zero nat := 0%N.
Instance eq_nat   : eq nat   := eqtype.eq_op.
Instance lt_nat   : lt nat   := ltn.
Instance add_nat  : add nat  := addn.
Instance sub_nat  : sub nat  := subn.

Instance cast_pos_nat : cast_class pos nat := val.
Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

Fixpoint to_poly (p : hpoly A) := match p with
  | Pc c => c%:P 
  | PX a n p => to_poly p * 'X^(cast n) + a%:P
  end.

(* Global Instance spec_hpoly : spec_of (hpoly A pos) {poly A} := to_poly. *)

Definition to_hpoly : {poly A} -> hpoly A := fun p => from_seq (polyseq p).

(* This instance has to be declared here in order not to make form_seq confused *)
Instance one_nat  : one nat  := 1%N.

Lemma to_hpolyK : cancel to_hpoly to_poly.
Proof.
elim/poly_ind; rewrite /to_hpoly ?polyseq0 // => p c ih.
rewrite -{1}cons_poly_def polyseq_cons.
have [|pn0] /= := nilP.
  rewrite -polyseq0 => /poly_inj ->; rewrite mul0r add0r.
  apply/poly_inj; rewrite !polyseqC.
   by case c0: (c == 0); rewrite ?polyseq0 // polyseqC c0.
by case: (polyseq p) ih => /= [<-| a l -> //]; rewrite mul0r add0r.
Qed.

Lemma ncons_add : forall m n (a : A) p, 
  ncons (m + n) a p = ncons m a (ncons n a p).
Proof. by elim=> //= m ih n a p; rewrite ih. Qed.

Lemma normalizeK : forall p, to_poly (normalize p) = to_poly p.
Proof.
elim => //= a n p <-; case: (normalize p) => //= b m q.
case: ifP => //= /eqP ->; case: n => [[]] //= n n0.
by rewrite addr0 /cast /cast_pos_nat insubdK /= ?exprD ?mulrA ?addnS.
Qed.

Definition Rhpoly : {poly A} -> hpoly A -> Prop := fun_hrel to_poly.

(* This is OK here, but not everywhere *)
Instance param_eq_refl A (x : A) : param Logic.eq x x | 999.
Proof. by rewrite paramE. Qed.

Lemma RhpolyE p q : param Rhpoly p q -> p = to_poly q.
Proof. by rewrite paramE. Qed.

Instance Rhpolyspec_r x : param Rhpoly (to_poly x) x | 10000.
Proof. by rewrite !paramE; case: x. Qed.

Fact normalize_lock : unit. Proof. exact tt. Qed.
Definition normalize_id := locked_with normalize_lock (@id {poly A}).
Lemma normalize_idE p : normalize_id p = p.
Proof. by rewrite /normalize_id unlock. Qed.

Instance Rhpoly_normalize : param (Rhpoly ==> Rhpoly) normalize_id normalize.
Proof.
by rewrite paramE => p hp rp; rewrite /Rhpoly /fun_hrel normalizeK normalize_idE.
Qed.

(* zero and one *)
Instance Rhpoly_0 : param Rhpoly 0%R 0%C.
Proof. by rewrite paramE. Qed.

Instance Rhpoly_1 : param Rhpoly 1%R 1%C.
Proof. by rewrite paramE. Qed.

Lemma to_poly_shift : forall n p, to_poly p * 'X^(cast n) = to_poly (PX 0 n p).
Proof. by case; elim => //= n ih h0 hp; rewrite addr0. Qed.

Instance Rhpoly_opp : param (Rhpoly ==> Rhpoly) -%R -%C.
Proof.
apply param_abstr => p hp h1.
rewrite [p]RhpolyE paramE /Rhpoly /fun_hrel {p h1}.
by elim: hp => /= [a|a n p ->]; rewrite polyC_opp // opprD mulNr.
Qed.

Instance Rhpoly_scale : param (Logic.eq ==> Rhpoly ==> Rhpoly) *:%R *:%C.
Proof.
rewrite paramE => /= a b -> p hp h1.
rewrite [p]RhpolyE /Rhpoly /fun_hrel {a p h1}.
elim: hp => [a|a n p ih] /=; first by rewrite polyC_mul mul_polyC.
by rewrite ih polyC_mul -!mul_polyC mulrDr mulrA.
Qed.

Lemma addXn_constE n a q : to_poly (addXn_const n a q) = a%:P * 'X^n + to_poly q.
Proof.
elim: q n => [b [|n]|b m q' ih n] /=; simpC; first by rewrite polyC_add expr0 mulr1.
  by rewrite /cast /cast_pos_nat insubdK.
case: eqP => [->|/eqP n0] /=; first by rewrite polyC_add expr0 mulr1 addrCA.
case: eqP => [hn|hnc] /=; first by rewrite ih expr0 mulr1 -hn mulrDl -addrA.
have [hlt|hleq] /= := ltnP; rewrite /cast /cast_nat_pos /cast_pos_nat.
  rewrite insubdK -?topredE /= ?lt0n // mulrDl -mulrA -exprD addrCA -addrA.
  by rewrite ?insubdK -?topredE /= ?subn_gt0 ?lt0n ?subnK // ltnW. 
by rewrite ih mulrDl -mulrA -exprD subnK // addrA.
Qed.

Arguments addXn_const _ _ _ _ _ _ _ _ _ _ _ n a q : simpl never. 

Lemma addXnE n p q : to_poly (addXn n p q) = to_poly p * 'X^n + to_poly q.
Proof.
elim: p n q => [a n q|a n' p ih n [b|b m q]] /=; simpC; first by rewrite addXn_constE.
  case: eqP => [->|/eqP n0]; first by rewrite expr0 mulr1 /= polyC_add addrA.
  by rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK // -topredE /= lt0n.
case: eqP => [->|/eqP no].
  rewrite expr0 mulr1 /lt_op /lt_pos /eq_op /eq_pos.
  case: ifP => [/eqP ->|hneq] /=.
    by rewrite ih expr0 mulr1 mulrDl polyC_add -!addrA [_ + (a%:P + _)]addrCA.
  have [hlt|hleq] /= := ltnP; rewrite ih polyC_add mulrDl -!addrA ?expr0.
    rewrite mulr1 /= addr0 -mulrA -exprD [_ + (a%:P + _)]addrCA /cast.
    by rewrite /cast_pos_nat insubdK ?subnK -?topredE /= ?subn_gt0 // ltnW. 
  rewrite -mulrA -exprD [_ + (a%:P + _)]addrCA /cast /cast_pos_nat.
  rewrite  insubdK ?subnK // -?topredE /= subn_gt0; rewrite leq_eqVlt in hleq.
  by case/orP: hleq hneq => // /eqP /val_inj ->; rewrite eqxx.
rewrite !ih !addXn_constE expr0 mulr1 /= addr0 mulrDl -mulrA -exprD addnC.
by rewrite -!addrA [b%:P + (_ + _)]addrCA [b%:P + _]addrC.
Qed.

Instance Rhpoly_add : param (Rhpoly ==> Rhpoly ==> Rhpoly) +%R +%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE paramE /Rhpoly /fun_hrel {p q h1 h2}.
by rewrite /add_op /add_hpoly addXnE expr0 mulr1.
Qed.

Instance Rhpoly_mul : param (Rhpoly ==> Rhpoly ==> Rhpoly) *%R *%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE paramE /Rhpoly /fun_hrel {p q h1 h2}.
elim: hp hq => [a [b|b m q]|a n p ih [b|b m q]]; first by rewrite /= polyC_mul.
    by rewrite /mul_op /mul_hpoly -[to_poly _]RhpolyE /= -mul_polyC. 
  by rewrite /mul_op /mul_hpoly -[to_poly _]RhpolyE /= [_ * b%:P]mulrC -mul_polyC. 
rewrite /= mulrDr !mulrDl mulrCA -!mulrA -exprD mulrCA !mulrA [_ * b%:P]mulrC.
rewrite -polyC_mul !mul_polyC !addXnE /= expr0 !mulr1 !addr0 ih scalerAl /cast.
rewrite -?[to_poly (_ *: _)%C]RhpolyE /cast_pos_nat insubdK -?topredE //= addn_gt0.
by case: n => /= x ->.
Qed.

Instance Rhpoly_sub : param (Rhpoly ==> Rhpoly ==> Rhpoly) subr sub_op.
Proof.
apply param_abstr2 => p hp h1 q hq h2.
by rewrite paramE /sub_op /sub_hpoly /Rhpoly /fun_hrel -[to_poly _]RhpolyE.
Qed.

Instance Rhpoly_shift : param (Logic.eq ==> Rhpoly ==> Rhpoly) 
  (fun n p => p * 'X^(cast n)) (fun n p => shift_hpoly n p).
Proof.
rewrite paramE => /= a n -> p hp h1.
by rewrite [p]RhpolyE /Rhpoly /fun_hrel {a p h1} /= addr0.
Qed.

(* Add to ssr? *)
Lemma size_MXnaddC (R : comRingType) (p : {poly R}) (c : R) n :
  size (p * 'X^n.+1 + c%:P) = if (p == 0) then size c%:P else (n.+1 + size p)%N.
Proof.
have [->|/eqP hp0] := eqP; first by rewrite mul0r add0r.
rewrite size_addl polyseqMXn ?size_ncons // size_polyC.
by case: (c == 0)=> //=; rewrite ltnS ltn_addl // size_poly_gt0.
Qed.

Instance Rhpoly_eq0 : 
  param (Rhpoly ==> Logic.eq) (fun p => p == 0) (eq0_hpoly)%C.
Proof.
rewrite paramE => p hp rp; rewrite [p]RhpolyE {p rp}.
elim: hp => [a|a n p ih] /=; first by rewrite polyC_eq0.
rewrite /cast /cast_pos_nat /=; case: (sval n) (svalP n) => // m _.
rewrite -size_poly_eq0 -ih size_MXnaddC; case: ifP=> //= _.
by rewrite size_poly_eq0 polyC_eq0.
Qed.

Instance Rhpoly_eq : param (Rhpoly ==> Rhpoly ==> Logic.eq)
  (fun p q => p == q) (fun hp hq => hp == hq)%C.
Proof.
apply param_abstr2 => p hp h1 q hq h2.
by rewrite /eq_op /eq_hpoly paramE -[eq0_hpoly _]param_eq subr_eq0.
Qed.

Instance Rhpoly_size : param (Rhpoly ==> Logic.eq)
  (fun p => size p) (fun p => size_hpoly p).
Proof.
apply param_abstr => /= p hp h1; rewrite [p]RhpolyE paramE {p h1}.
elim: hp => [a|a n p ih] /=; first by rewrite size_polyC; simpC; case: eqP.
rewrite /cast /cast_pos_nat /=; case: (sval n) (svalP n) => // m _.
rewrite size_MXnaddC ih -[eq0_hpoly _]param_eq.
by case: ifP=> //= _; simpC; rewrite size_polyC; case: ifP.
Qed.

(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section hpoly_parametricity.

Import Refinements.Op.

Context (C : Type) (rAC : A -> C -> Prop).
Context (P : Type) (rP : pos -> P -> Prop).
Context (N : Type) (rN : nat -> N -> Prop).
Context `{zero C, one C, opp C, add C, sub C, mul C, eq C}.
Context `{one P, add P, sub P, eq P, lt P}.
Context `{zero N, one N, eq N, lt N, add N, sub N}.
Context `{cast_class N P, cast_class P N}.
Context `{!param rAC 0%R 0%C, !param rAC 1%R 1%C}.
Context `{!param (rAC ==> rAC) -%R -%C}.
Context `{!param (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!param (rAC ==> rAC ==> rAC) subr sub_op}.
Context `{!param (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!param (rAC ==> rAC ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param rP pos1 1%C}.
Context `{!param (rP ==> rP ==> rP) add_pos +%C}.
Context `{!param (rP ==> rP ==> rP) sub_pos sub_op}.
Context `{!param (rP ==> rP ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (rP ==> rP ==> Logic.eq) lt_pos lt_op}.
Context `{!param rN 0%N 0%C, !param rN 1%N 1%C}.
Context `{!param (rN ==> rN ==> rN) addn +%C}.
Context `{!param (rN ==> rN ==> rN) subn sub_op}.
Context `{!param (rN ==> rN ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (rN ==> rN ==> Logic.eq) ltn lt_op}.
Context `{!param (rN ==> rP) cast_nat_pos cast}.
Context `{!param (rP ==> rN) cast_pos_nat cast}.

Local Notation hpoly_hrel := (hpoly_hrel rAC rP).
Definition RhpolyC := (Rhpoly \o hpoly_hrel)%rel.

Global Instance RhpolyC_0 : param RhpolyC 0%R 0%C.
Proof. exact: param_trans. Qed.

Global Instance RhpolyC_1 : param RhpolyC 1%R 1%C.
Proof. exact: param_trans. Qed.

Global Instance RhpolyC_add : param (RhpolyC ==> RhpolyC ==> RhpolyC) +%R +%C.
Admitted.

Global Instance RhpolyC_opp : param (RhpolyC ==> RhpolyC) -%R -%C.
Proof. exact: param_trans. Qed.

Global Instance RhpolyC_scale : param (rAC ==> RhpolyC ==> RhpolyC) *:%R *:%C.
Proof. exact: param_trans. Qed.

Global Instance RhpolyC_sub :
  param (RhpolyC ==> RhpolyC ==> RhpolyC) AlgOp.subr sub_op.
Proof. by rewrite /AlgOp.subr /sub_op /sub_hpoly; apply: get_param. Qed.

Global Instance RhpolyC_shift : param (rP ==> RhpolyC ==> RhpolyC)
  (fun n p => p * 'X^(cast n)) (fun n (p : hpoly C) => shift_hpoly n p).
Proof. exact: param_trans. Qed.

(* Global Instance RhpolyC_mul : *)
(*   param (RhpolyC ==> RhpolyC ==> RhpolyC) *%R *%C. *)
(* (* Proof. admit. Qed. *) *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RhpolyC_size : param (RhpolyC ==> Logic.eq) *)
(*   (fun (p : {poly R}) => size p) (fun s => size_hpoly s). *)
(* Proof. admit. Qed. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RhpolyC_lead_coef : *)
(*   param (RhpolyC ==> rAC) lead_coef (fun p => lead_coef_hpoly p). *)
(* (* Proof. admit. Qed. *) *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RhpolyC_polyC : *)
(*   param (rAC ==> RhpolyC) (fun a => a%:P) (fun a => cast a)%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance RhpolyC_eq : param (RhpolyC ==> RhpolyC ==> Logic.eq) *)
(*   (fun p q => p == q) (fun sp sq => sp == sq)%C. *)
(* (* Proof. admit. Qed. *) *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RhpolyC_horner : param (RhpolyC ==> rAC ==> rAC) *)
(*   (fun p x => p.[x]) (fun sp x => horner_seq sp x). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

End hpoly_parametricity.
End hpoly_theory.
