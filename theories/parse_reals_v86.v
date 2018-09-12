From Interval Require Import Interval_missing.
Require Import Reals QArith.
From Bignums Require Import BigQ.
From mathcomp Require Import ssreflect.
Require Import misc.

Local Open Scope R_scope.

Coercion bigQ2R : BigQ.t_ >-> R.

Variant Assert := assert_false.

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
    | _ => assert_false
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
