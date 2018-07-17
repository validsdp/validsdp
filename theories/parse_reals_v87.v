From Interval Require Import Interval_missing.
Require Import Reals QArith CBigQ.
From mathcomp Require Import ssreflect.
Require Import misc.

Local Open Scope R_scope.

Coercion bigQ2R : BigQ.t_ >-> R.

Variant Assert := assert_false.

Inductive p_real_cst :=
| PConstR0
(* | PConstQz of bigZ *)
| PConstQq of bigZ & bigN
| PConstIZR of BinNums.Z
| PConstRdiv of p_real_cst & positive
| PConstRopp of p_real_cst
| PConstRinv of positive.

Ltac get_real_cst t :=
  let rec aux t :=
    match t with
    (* | Z2R [?z]%bigZ *)
    | bigQ2R (?z # ?n)%bigQ => constr:(PConstQq z n)
    | R0 => PConstR0
    | Rdiv ?x (IZR (BinNums.Zpos ?y)) => let x := aux x in
                                         constr:(PConstRdiv x y)
    | Ropp ?x => let x := aux x in
                 constr:(PConstRopp x)
    | Rinv (IZR (BinNums.Zpos ?x)) => constr:(PConstRinv x)
    | IZR ?n => constr:(PConstIZR n)
    | _ => assert_false
    end in
  aux t.

Fixpoint interp_p_real_cst (p : p_real_cst) : R :=
  match p with
  | PConstR0 => R0
(* | PConstQz z => Z2R [z]%bigZ *)
  | PConstQq z n => bigQ2R (z # n)%bigQ
  | PConstIZR n => IZR n
  | PConstRdiv x y => Rdiv (interp_p_real_cst x) (IPR y)
  | PConstRopp x => Ropp (interp_p_real_cst x)
  | PConstRinv x => Rinv (IPR x)
  end.

Fixpoint bigQ_of_p_real_cst (c : p_real_cst) : bigQ :=
  let aux := bigQ_of_p_real_cst in
  match c with
  | PConstR0 => 0%bigQ
  | PConstQq z n => (z # n)%bigQ
  | PConstIZR n => BigQ.of_Q (inject_Z n)
  | PConstRdiv x y => (aux x / BigQ.of_Q (inject_Z (Z.pos y)))%bigQ
  | PConstRopp x => (- aux x)%bigQ
  | PConstRinv x => (1 / BigQ.of_Q (inject_Z (Z.pos x)))%bigQ
  end.

Lemma bigQ_of_p_real_cst_correct c :
  bigQ2R (bigQ_of_p_real_cst c) = interp_p_real_cst c.
Proof.
have IQRp : forall p,
  Q2R [BigQ.Qz (BigZ.Pos (BigN.of_pos p))]%bigQ = IPR p.
{ by move=> p; rewrite /Q2R /= BigN.spec_of_pos /= Rsimpl. }
elim c.
{ by rewrite /bigQ2R /Q2R /= /Rdiv Rmult_0_l. }
{ done. }
{ move=> [|p|p] /=.
  { by rewrite /bigQ2R /Q2R /= /Rdiv Rmult_0_l. }
  { by rewrite /bigQ2R IQRp /IZR. }
  by rewrite /bigQ2R /IZR -IQRp -Q2R_opp. }
{ move=> c' Hc' p; rewrite /= -Hc' /Rdiv /bigQ2R /= -IQRp -Q2R_inv.
  { by rewrite -Q2R_mult; apply Q2R_Qeq; rewrite BigQ.spec_div. }
  by rewrite /= BigN.spec_of_pos /Q2R /= Rsimpl. }
{ move=> p Hp; rewrite /= -Hp /bigQ2R -Q2R_opp; apply Q2R_Qeq, BigQ.spec_opp. }
move=> p; rewrite /bigQ2R /interp_p_real_cst -IQRp -Q2R_inv.
{ apply Q2R_Qeq; rewrite -(Qmult_1_l (Qinv _)) -/([1]%bigQ).
  by rewrite -BigQ.spec_inv -BigQ.spec_mul. }
by rewrite /= BigN.spec_of_pos /Q2R /= Rsimpl.
Qed.
