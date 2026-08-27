(** * Error bounds on triangular substitution *)

(** Bounds from:
    Effects of Underflow on Solving Linear Systems
    James Demmel, May 1981.
with some adaptations. *)

From Stdlib Require Import Reals Psatz.
From Flocq Require Import Core.Raux.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun bigop order ssralg matrix ssrnum.

From mathcomp Require Import Rstruct.

Require Import misc bounded fsum_l2r fcmsum cholesky.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Order.Theory Num.Theory.

Section Triangle.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).

(** Eq. (87) from Algorithm in Appendix 2 *)
Definition yhat n (bi : F) (L : 'M[F]_n.+1) (y : 'cV[F]_n.+1) (i : 'I_n.+1) :=
  ytilded bi [ffun j : 'I_i => L i (inord j)]
    [ffun j : 'I_i => y (inord j) ord0] (L i i).

(** Triangular substitution (algorithm in Appendix 2) *)
Definition fwd_subst n (L : 'M[F]_n.+1) (b : 'cV[F]_n.+1) :=
  foldl
    (fun (y : 'cV_n.+1) i =>
       \col_i' if i' != i then y i' ord0 else yhat (b i ord0) L y i)
    b (ord_enum n.+1).  (* initial value (b here) can be any vector of correct
                           dimensions, we chose b as it better matches the fctl
                           model where the C program overwrites b with y *)

Lemma fwd_subst_i n L b (i : 'I_n.+1) :
  fwd_subst L b i ord0
  = ytilded (b i ord0) [ffun j : 'I_i => L i (inord j)]
      [ffun j : 'I_i => fwd_subst L b (inord j) ord0] (L i i).
Proof.
rewrite /fwd_subst.
set f := fun y i => _.
pose fi i k := foldl f b (take k (ord_enum n.+1)) i ord0.
have fgei (i' : 'I_n.+1) k :
    (i'.+1 + k <= n.+1)%N -> fi i' (i'.+1 + k)%N = fi i' i'.+1.
  elim: k => [/[!addn0]//| k IHk /[!addnS] ikn].
  rewrite -IHk; last by rewrite ltnW.
  rewrite /fi (take_nth ord0) ?size_ord_enum// foldl_rcons mxE ifT//.
  apply/eqP => /(congr1 val)/=; rewrite nth_ord_enum ikn; apply/eqP.
  by rewrite neq_ltn leq_addr.
rewrite -[ord_enum n.+1]take_size size_ord_enum -/(fi i n.+1).
rewrite -[in LHS](subnKC (ltn_ord i)) fgei ?(subnKC (ltn_ord i))//.
rewrite /fi (take_nth ord0) ?size_ord_enum// foldl_rcons mxE ifF; last first.
  apply: negbTE; rewrite negbK.
  by apply/eqP/val_inj; rewrite /= nth_ord_enum ltn_ord.
have -> : nth ord0 (ord_enum n.+1) i = i.
  by apply/val_inj; rewrite /= nth_ord_enum ltn_ord.
congr (ytilded _ _ _ _); apply/ffunP => k /[!ffunE].
do 2![rewrite -/(fi _ _)].
have kSn : (k < n.+1)%N by apply/(leq_trans (ltn_ord k))/ltnW.
have ie : i = ((inord k : 'I_n.+1).+1 + (i - k.+1))%N :> nat.
  by rewrite inordK ?subnKC.
rewrite [X in fi _ X]ie fgei; last by rewrite inordK ?subnKC// ltnW.
have Sne : n.+1 = ((inord k : 'I_n.+1).+1 + (n.+1 - k.+1))%N :> nat.
  by rewrite inordK ?subnKC.
by rewrite [X in _ = fi _ X]Sne fgei// inordK ?subnKC.
Qed.

(** Lemma 4 (adapted) *)
Lemma lemma_4 n (L : 'M[F]_n.+1) (b : 'cV[F]_n.+1) :
    (forall i, L i i <> 0 :> R) ->
    (forall i j : 'I_n.+1, (i < j)%N -> L i j = 0 :> R) ->
  let yhat := fwd_subst L b in
  exists (dL : 'M_n.+1) (db : 'cV_n.+1),
    [/\
       (MF2R L + dL) *m MF2R yhat = MF2R b + db,
       (forall i j, Rabs (dL i j) <= n.+1%:R * eps * Rabs (L i j)) &
       forall i,
         db i ord0 <= (1 + n.+1%:R * eps) * eta * (n.+1%:R + Rabs (L i i))
    ].
Proof.
move=> Lii_neq0 Lij0 yhat'.
suff [dLb eLb] : exists (dLb : (R^n.+1 * R)%type^n.+1), forall i,
    [/\ \sum_j ((L i j : R) + (dLb i).1 j) * (yhat' j ord0 : R)
        = (b i ord0 : R) + (dLb i).2,
      forall j, Rabs ((dLb i).1 j) <= n.+1%:R * eps * Rabs (L i j) &
      (dLb i).2 <= (1 + n.+1%:R * eps) * eta * (n.+1%:R + Rabs (L i i))].
  exists (\matrix_(i, j) (dLb i).1 j), (\col_i (dLb i).2); split=> [| i j | i].
  - apply/matrixP => i j; rewrite ord1 !mxE.
    by have [<- _ _] := eLb i; apply: eq_bigr => {}j _ /[!mxE].
  - by have [_ /(_ j)+ _] := eLb i; rewrite mxE.
  - by have [_ _] := eLb i; rewrite mxE.
apply: (@ffun_exists n.+1 (R^n.+1 * R) (fun i dLbi =>
  [/\ \sum_j ((L i j : R) + dLbi.1 j) * yhat' j ord0 = (b i ord0 : R) + dLbi.2,
    forall j : 'I_n.+1, Rabs (dLbi.1 j) <= n.+1%:R * eps * Rabs (L i j) &
    dLbi.2 <= (1 + n.+1%:R * eps) * eta * (n.+1%:R + Rabs (L i i))])) => i.
have := lemma_2_1_aux [ffun j : 'I_i => L i (inord j)]
          [ffun j : 'I_i => yhat' (inord j) ord0] (b i ord0) (Lii_neq0 i).
move/RleP; rewrite !RealsE/=.
under eq_bigr => j _ do rewrite !RealsE !ffunE.
under [in leRHS]eq_bigr => j _ do rewrite !RealsE !ffunE.
rewrite -fwd_subst_i -/yhat' distrC -addrA -opprD.
set s := _ + (L i i : R) * _.
have -> : s = \sum_(j < i.+1) (L i (inord j) : R) * yhat' (inord j) ord0.
  rewrite big_ord_recr/= /s; congr (_ + _ * _).
    by congr (L _ _); apply/val_inj; rewrite inord_val.
  by congr (yhat' _ _); apply/val_inj; rewrite inord_val.
move=> {s}; set s := `| _ | + _.
have -> : s = \sum_(j < i.+1) `| (L i (inord j) : R) * yhat' (inord j) ord0 |.
  rewrite big_ord_recr/= /s addrC; congr (`| _ * _ | + _).
    by congr (L _ _); apply/val_inj; rewrite inord_val.
  by congr (yhat' _ _); apply/val_inj; rewrite inord_val.
rewrite distrC.
have r1ge0 : (0 <= (i.+1%:R * eps
    * \sum_(j < i.+1) `|(L i (inord j) : R) * yhat' (inord j) ord0|)%Ri)%Re.
  apply/RleP/mulr_ge0; first by apply: mulr_ge0 => //; apply/RleP/eps_pos.
  by apply: sumr_ge0 => j _; apply: normr_ge0.
have r2ge0 : (0 <= ((1 + i.+1%:R * eps) * (i%:R + `|L i i : R|) * eta)%Ri)%Re.
  apply/RleP/mulr_ge0; last exact/RleP/eta_pos.
  apply/mulr_ge0; last exact/addr_ge0.
  by apply/addr_ge0 => //; apply/mulr_ge0 => //; apply/RleP/eps_pos.
move/RleP; rewrite -RplusE -[X in (X <= _)%Re]RabsE.
move=> /bounded_distrl_rev /(_ r1ge0 r2ge0) [e1 [e2]].
pose F := [ffun j : 'I_i.+1 =>
  (i.+1%:R * eps * `|L i (inord j) * yhat' (inord j) ord0 : R|)%Ri].
have e1_le_sumF : (Rabs e1 <= \sum_(j < i.+1) F j)%Re.
  apply: (Rle_trans _ _ _ (bounded_prop e1)).
  rewrite mulr_sumr; apply/RleP/ler_sum => j _.
  by rewrite /F ffunE RmultE.
have Fge0 j : (0 <= F j)%Re.
  by apply/RleP; rewrite /F ffunE ?mulr_ge0//; first exact/RleP/eps_pos.
have [eF [-> eFF]] := big_bounded_distrl_rev e1_le_sumF Fge0.
pose eFn := [ffun k : 'I_(i.+1 + (n.+1 - i.+1)) =>
    (if split k isn't inl k' then 0
     else - eF k' / yhat' (widen_ord (ltn_ord i) k') ord0) : R].
pose einn := subnKC (ltn_ord i).
pose eFn' := [ffun k : 'I_n.+1 => eFn (cast_ord (esym einn) k)].
move/eqP; rewrite RplusE subr_eq addrAC -addrA [eqbRHS]addrC -subr_eq -sumrB.
move=> /eqP eFe2; exists (eFn', e2 : R).
have eps_ge0 : 0 <= eps by exact/RleP/eps_pos.
have eta_ge0 : 0 <= eta by exact/RleP/eta_pos.
split=> [|j|] /=; last first.
- move: (Rabs_le_inv _ _ (bounded_prop e2)) => [_ /RleP].
  have oieps_ge0 : 0 <= 1 + i.+1%:R * eps by rewrite addr_ge0 ?mulr_ge0.
  have oiepseta_ge0 : 0 <= (1 + i.+1%:R * eps) * eta by rewrite mulr_ge0.
  move/le_trans; apply; rewrite mulrAC; apply: ler_pM => //.
  + exact: addr_ge0.
  + by rewrite ler_pM ?lerD ?ler_pM// ler_nat.
  by rewrite lerD// ler_nat ltnW.
- rewrite /eFn' ffunE /eFn ffunE; case: splitP => k jk; last first.
    by rewrite Rabs_R0 ?mulr_ge0// RealsE.
  have -> : widen_ord (ltn_ord i) k = inord j.
    by apply: val_inj; rewrite /= -jk inordK ?(leq_trans (ltn_ord k)).
  rewrite Rabs_mult Rabs_Ropp Rabs_inv !RealsE.
  have [yhat'0 | /eqP yhat'n0] := (yhat' (inord j) ord0 : R) =P 0.
    move: (eFF (inord j)); rewrite /F ffunE.
    rewrite inordK; last by apply: leq_trans (ltn_ord k); rewrite -jk/=.
    rewrite yhat'0 !RealsE mulr0 normr0 mulr0 => /RleP; rewrite normr_le0.
    have -> : inord j = k.
      apply: val_inj; rewrite /= -jk inordK//.
      by apply: leq_trans (ltn_ord k); rewrite -jk/=.
    by move/eqP => ->; rewrite normr0 mul0r !mulr_ge0.
  rewrite ler_pdivrMr ?normr_gt0//.
  move: (eFF k) => /RleP; rewrite RealsE => /le_trans; apply.
  rewrite /F ffunE RealsE normrM mulrA ler_pM//.
  + by rewrite !mulr_ge0.
  + have -> : inord k = j by rewrite -jk inord_val.
    by rewrite ?ler_pM ?mulr_ge0// ler_nat.
  by have -> : inord k = inord j :> 'I_n.+1 by rewrite -jk.
rewrite -eFe2.
have -> : \sum_(j < n.+1) ((L i j : R) + eFn' j) * yhat' j ord0
    = \sum_(j < i.+1 + (n.+1 - i.+1)) ((L i (cast_ord einn j) : R)
        + eFn' (cast_ord einn j)) * yhat' (cast_ord einn j) ord0.
  set lhs := \sum__ _; set rhs := \sum__ _.
  have -> : lhs = \sum_(0 <= j < n.+1)
      ((L i (inord j) : R) + eFn' (inord j)) * yhat' (inord j) ord0.
    by rewrite big_mkord; apply: eq_bigr => j _; rewrite inord_val.
  suff -> : rhs = \sum_(0 <= j < i.+1 + (n.+1 - i.+1))
      ((L i (inord j) : R) + eFn' (inord j)) * yhat' (inord j) ord0.
    by rewrite (subnKC (ltn_ord i)).
  rewrite big_mkord; apply: eq_bigr => j _.
  have ->// : cast_ord einn j = inord j.
  by apply: val_inj; rewrite /= inordK// -[ltnRHS](subnKC (ltn_ord i)).
rewrite big_split_ord/=.
under eq_bigr => j _.
  rewrite (_ : cast_ord einn _ = inord j); last first.
    by apply/val_inj; rewrite /= inordK// (leq_trans (ltn_ord j)).
  rewrite mulrDl; over.
under [X in _ + X = _]eq_bigr => j _.
  rewrite (_ : _ * _ = 0); last first; [|over].
  rewrite Lij0 ?ffunE /= ?ltn_addr//.
  case: splitP => [k /=|]; last by rewrite add0r mul0r.
  by move: (ltn_ord k) => /[swap]<-; rewrite -[ltnRHS]addn0 ltn_add2l.
rewrite sumr_const mul0rn addr0; apply: eq_bigr => j _.
rewrite ffunE /eFn ffunE.
case: splitP => k /=; last first.
  rewrite inordK ?(leq_trans (ltn_ord j))// => jE.
  by move: (ltn_ord j); rewrite jE -[ltnRHS]addn0 ltn_add2l.
move=> jk; have {}jk : j = k.
  by apply: val_inj; rewrite /= -jk inordK ?(leq_trans (ltn_ord j)).
have -> : widen_ord (ltn_ord i) k = inord j.
  by apply: val_inj; rewrite /= jk inordK ?(leq_trans (ltn_ord k)).
have [yhat'0 | /eqP yhat'n0] := (yhat' (inord j) ord0 : R) =P 0; last first.
  by rewrite divfK// RoppE jk.
rewrite yhat'0 !mulr0 !add0r.
move: (eFF j); rewrite /F ffunE yhat'0 !RealsE mulr0 normr0 mulr0.
by move/RleP; rewrite normr_le0 => /eqP->; rewrite oppr0.
Qed.

End Triangle.
