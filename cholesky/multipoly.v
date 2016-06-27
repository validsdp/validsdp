Require Import FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype ssralg.
(* tests with multipolys from
   git clone https://github.com/math-comp/multinomials.git *)
From SsrMultinomials Require Import mpoly freeg.
From CoqEAL_theory Require Import hrel.
From CoqEAL_refinements Require Import refinements.
From CoqEAL_refinements Require Import seqmatrix (* for Rord, zipwith and eq_seq *).
Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

(** Part I: Generic operations *)

Section seqmpoly_generic.

(** Monomials *)

(* TODO: may be refactored by using mnm1, mnm_add, mnm_muln *)
Definition mnmd {n} (i : 'I_n) (d : nat) :=
  [multinom (if (i == j :> nat) then d else 0%N) | j < n].
Definition mpvar {T : ringType} {n} (c : T) d i : {mpoly T[n]} := c *: 'X_[mnmd i d].

Definition seqmultinom := seq nat.

Definition mnm0_seq {n} := nseq n 0%N.

Definition mnmd_seq {n} (i d : nat) :=
  nseq i 0%N ++ [:: d] ++ nseq (n - i - 1) 0%N.

(** Multiplication of multinomials *)
Definition mnm_add_seq m1 m2 := map2 addn m1 m2.

Fixpoint mnmc_lt_seq (s1 s2 : seq nat) {struct s1} : bool :=
  match s1, s2 with
    | [::], [::] => false
    | [::], _ => true
    | x1 :: s1', [::] => false
    | x1 :: s1', x2 :: s2' => (x1 < x2)%N || (x1 == x2)%N && mnmc_lt_seq s1' s2'
  end.

Definition mnmc_eq_seq := eq_seq (fun n m : nat => n == m)%N.

Lemma mnmc_eq_seqP s1 s2 : reflect (mnmc_eq_seq s1 s2) (s1 == s2).
Proof.
move: s2; elim s1 => {s1}[|a1 s1 Hind] s2.
{ now case s2 => [|n l]; apply (iffP idP). }
case s2 => {s2}[|a2 s2]; [by apply (iffP idP)|].
specialize (Hind s2); rewrite /mnmc_eq_seq /=; apply (iffP idP).
{ by move/eqP => H; injection H => Hs Ha; rewrite Ha eqxx; apply /Hind/eqP. }
by move/andP => [Ha Hs]; apply/eqP; f_equal; apply /eqP => //; apply/Hind.
Qed.

End seqmpoly_generic.

(** Multivariate polynomials *)

Module MultinomOrd <: OrderedType.
Definition t := seqmultinom.
Definition eq : t -> t -> Prop := mnmc_eq_seq.
Definition lt : t -> t -> Prop := mnmc_lt_seq.

Lemma intro_eq x y :
  (mnmc_lt_seq x y = false) -> (mnmc_lt_seq y x = false) -> mnmc_eq_seq x y.
Proof.
move: x y; elim => [|hx tx Hind]; case=> // hy ty.
rewrite /lt /=; case (ltnP hx hy) => //= Hxy; case (ltnP hy hx) => //= Hyx.
assert (Exy : hx == hy); [by apply/eqP /anti_leq; rewrite Hyx|].
rewrite /mnmc_eq_seq /= Exy; rewrite eq_sym in Exy; rewrite Exy /=; apply Hind.
Qed.

(* Remark: only compare is used in implementation (eq_dec isn't). *)
Definition compare (x y : t) : Compare lt eq x y :=
  match sumb (mnmc_lt_seq x y) with
  | left prf => LT prf
  | right prf =>
    match sumb (mnmc_lt_seq y x) with
    | left prf' => GT prf'
    | right prf' => EQ (intro_eq prf prf')
    end
  end.

Lemma eq_dec (x y : t) : {eq x y} + {~ eq x y}.
Proof. by rewrite /eq; case (mnmc_eq_seq x y); [left|right]. Qed.

Lemma eq_refl : forall x : t, eq x x.
Proof. by move=> x; apply/mnmc_eq_seqP/eqP. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. move=> x y /mnmc_eq_seqP/eqP =>->; apply eq_refl. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. by move=> x y z /mnmc_eq_seqP/eqP =>->. Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
elim => [|hx tx Hind] y z; [by case y => // hy ty; case z|].
case y => // hy ty; case z => // hz tz.
move/orP => [Hxy|Hxy].
{ move/orP => [Hyz|Hyz]; apply/orP; left; [by move: Hyz; apply ltn_trans|].
  move/andP in Hyz; destruct Hyz as [Hyz Hyz'].
  by move/eqP in Hyz; rewrite -Hyz. }
move/andP in Hxy; destruct Hxy as [Hxy Hxy']; move/eqP in Hxy; rewrite Hxy.
move/orP => [Hyz|Hyz]; apply/orP; [by left|right].
move/andP in Hyz; destruct Hyz as [Hyz Hyz']; rewrite Hyz /=.
by move: Hyz'; apply Hind.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
move=> x y Hlt /mnmc_eq_seqP/eqP Heq; move: Hlt; rewrite Heq.
elim y => [//|h t Hind] /orP [H|H]; [by move: H; rewrite ltnn|].
move/andP in H; apply Hind, H.
Qed.

End MultinomOrd.

Module M := FMapList.Make MultinomOrd.
Arguments M.empty {elt}.
(*
Module M := FMapAVL.Make MultinomOrd.
*)
Definition effmpoly := M.t.

Module MFacts := Facts M.

Module MProps.

Include Properties M.

Definition singleton T key (val : T) := M.add key val M.empty.

Lemma singleton_mapsto {T} k k' (e e' : T) :
  M.MapsTo k e (MProps.singleton k' e') -> (k = k' /\ e = e').
Proof.
rewrite F.add_mapsto_iff; elim; move=> [Hk He]; [split; [|by[]]|].
{ by move: Hk; move /mnmc_eq_seqP/eqP. }
by move: He; rewrite F.empty_mapsto_iff.
Qed.

Lemma singleton_in_iff {T} y k (e : T) :
  M.In y (MProps.singleton k e) <-> M.E.eq y k.
Proof.
split; [move/MFacts.add_in_iff|move=> H; apply/MFacts.add_in_iff].
by intuition; move/MFacts.empty_in_iff in H.
by left; symmetry.
Qed.

End MProps.

Section seqmpoly_generic_2.

Definition effmpoly_of_list : forall T, seq (seqmultinom * T) -> effmpoly T :=
  MProps.of_list.

Definition list_of_effmpoly : forall T, effmpoly T -> seq (seqmultinom * T) :=
  M.elements.

Context {T : Type} `{!one T, !add T, !sub T, !mul T} {n : nat}.

Definition mp0_eff : effmpoly T := M.empty.

Definition mp1_eff  := MProps.singleton (@mnm0_seq n) 1%C.

Definition mpvar_eff (c : T) (d : nat) (i : nat) : effmpoly T :=
  MProps.singleton (@mnmd_seq n i d) c.

Definition mpolyC_eff (c : T) : effmpoly T :=
  MProps.singleton (@mnm0_seq n) c.

Definition mpolyX_eff (m : seqmultinom) : effmpoly T :=
  MProps.singleton m 1%C.

Definition mpoly_scale_eff (c : T) (p : effmpoly T) : effmpoly T :=
  M.map (fun x => c * x)%C p.

Definition mpoly_add_eff : effmpoly T -> effmpoly T -> effmpoly T :=
  M.map2 (fun c1 c2 =>
    match c1, c2 with
    | Some c1, Some c2 => Some (c1 + c2)%C
    | Some c, _ | _, Some c => Some c
    | None, None => None
    end).

Definition mpoly_sub_eff : effmpoly T -> effmpoly T -> effmpoly T :=
  M.map2 (fun c1 c2 =>
    match c1, c2 with
    | Some c1, Some c2 => Some (c1 - c2)%C
    | Some c, _ | _, Some c => Some c
    | None, None => None
    end).

Definition mult_monomial_eff (m : seqmultinom) (c : T) : effmpoly T -> effmpoly T :=
  M.fold (fun m' c' (*acc*) => M.add (mnm_add_seq m m') (c * c')%C (*acc*)) M.empty.

Definition mpoly_mul_eff (p q : effmpoly T) : effmpoly T :=
  M.fold (fun m c (*acc*) => mpoly_add_eff (mult_monomial_eff m c p) (*acc*)) M.empty q.

(* TODO: fast exponentiation *)
Definition mpoly_exp_eff (p : effmpoly T) (n : nat) := iterop n mpoly_mul_eff p mp0_eff.

Definition comp_monomial_eff (m : seqmultinom) (c : T) (lq : seq (effmpoly T)) : effmpoly T :=
  let mq := zipwith mpoly_exp_eff lq m in
  mpoly_scale_eff c (foldr mpoly_mul_eff mp1_eff mq).

Definition comp_mpoly_eff (lq : seq (effmpoly T)) (p : effmpoly T) : effmpoly T :=
  M.fold (fun m c p => mpoly_add_eff p (comp_monomial_eff m c lq)) p mp0_eff.

End seqmpoly_generic_2.

(** ** Part II: Proofs for proof-oriented types and programs *)
Section seqmpoly_theory.

(** *** Data refinement for seqmultinom *)

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
  by congr Some; apply: val_inj; simpl; apply: val_inj; simpl; case: (x).
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

Lemma refines_multinom_of_seqmultinom_val (n : nat) (m : seqmultinom) :
  size m == n -> Rseqmultinom (multinom_of_seqmultinom_val n m) m.
Proof.
move=> Hsz; rewrite /Rseqmultinom /multinom_of_seqmultinom_val /ofun_hrel.
case_eq (multinom_of_seqmultinom n m) => //.
by rewrite /multinom_of_seqmultinom; case sumb => //; rewrite Hsz.
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
  rewrite /mnmd_seq !(size_cat,size_nseq) /= -subnDA addnA addn1 subnKC //.
  move: param_c; rewrite paramE => <-; apply ltn_ord.
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
Qed.

Lemma param_mnm_add n :
  param (Rseqmultinom ==> Rseqmultinom ==> Rseqmultinom)
  (@mnm_add n) mnm_add_seq.
Proof.
apply param_abstr => mnm1 mnm1' param_mnm1.
apply param_abstr => mnm2 mnm2' param_mnm2.
apply/trivial_param/refines_seqmultinomP.
  by rewrite /mnm_add_seq size_map2 !refines_size minnn.
move=> i; rewrite /mnm_add_seq (nth_map2 _ (da := O) (db := O)) //; last first.
  by rewrite !refines_size.
by rewrite mnmDE !refines_nth.
Qed.

(** Multivariate polynomials *)

Definition mpoly_of_effmpoly (T : ringType) n (p' : effmpoly T) : option (mpoly n T) :=
  if MProps.for_all (fun k _ => size k == n)%N p' then
    Some [mpoly [freeg [seq (a.2, multinom_of_seqmultinom_val n a.1) |
                        a <- M.elements p']]]
  else None.

Definition effmpoly_of_mpoly (T : ringType) n (p : mpoly n T) : effmpoly T :=
  MProps.of_list [seq (seqmultinom_of_multinom a.2, a.1) |
                  a <- fgenum (val p)].

Definition Reffmpoly `{T : ringType, n : nat} :=
  ofun_hrel (@mpoly_of_effmpoly T n).

Lemma eq_key_elt_eq T x y : (M.eq_key_elt (elt:=T)) x y <-> x = y.
Proof.
split.
{ move=> [H1 H2].
  rewrite (surjective_pairing x) (surjective_pairing y); f_equal=> //.
  by apply/eqP/mnmc_eq_seqP. }
move=> ->; split=> //; apply M.E.eq_refl.
Qed.

Lemma in_InA_eq_key_elt_iff (T : eqType) x s :
  x \in s <-> InA (M.eq_key_elt (elt:=T)) x s.
Proof.
split.
{ elim s => // h t Hind; rewrite inE; move/orP => [Hh|Ht].
  { by move: Hh => /eqP ->; apply InA_cons_hd; split; [apply M.E.eq_refl|]. }
  by apply InA_cons_tl, Hind. }
elim s => [|h t Hind]; [by rewrite InA_nil|].
rewrite InA_cons; elim.
{ by move/eq_key_elt_eq=>->; rewrite inE eqxx. }
by move/Hind; rewrite inE orb_comm=>->.
Qed.

Lemma in_fst_InA_eq_key_iff (T : Type) x s :
  x.1 \in [seq x.1 | x <- s] <-> InA (M.eq_key (elt:=T)) x s.
Proof.
split.
{ elim s => // h t Hind; rewrite inE; move/orP => [Hh|Ht].
  { apply InA_cons_hd; rewrite /M.eq_key /M.Raw.PX.eqk.
    move: Hh => /eqP ->; apply M.E.eq_refl. }
  by apply InA_cons_tl, Hind. }
elim s => [|h t Hind]; [by rewrite InA_nil|].
rewrite InA_cons; elim.
{ rewrite /M.eq_key /M.Raw.PX.eqk; move/mnmc_eq_seqP/eqP =>->.
  by rewrite inE eqxx. }
by rewrite inE orb_comm; move/Hind =>->.
Qed.

Lemma NoDupA_eq_key_uniq_fst elt s : 
  NoDupA (M.eq_key (elt:=elt)) s -> uniq [seq i.1 | i <- s].
Proof.
elim s => // h t Hind Hnd /=.
inversion Hnd as [x|h' t' H1 H2].  (* @Érik: equivalent ssreflect ? *)
apply/andP; split; [|by apply Hind].
by apply/negP => Hin; apply H1, in_fst_InA_eq_key_iff.
Qed.

Lemma multinom_of_seqmultinom_inj n x y :
  size x = n -> size y = n ->
  multinom_of_seqmultinom n x = multinom_of_seqmultinom n y -> x = y.
Proof.
move=> Sx Sy; rewrite /multinom_of_seqmultinom.
case (sumb _) => [prfx|] /=; [|by rewrite Sx eqxx].
case (sumb _) => [prfy|] /=; [|by rewrite Sy eqxx].
by move=> H; injection H.
Qed.

Lemma multinom_of_seqmultinom_val_inj n x y :
  size x = n -> size y = n ->
  multinom_of_seqmultinom_val n x = multinom_of_seqmultinom_val n y -> x = y.
Proof.
move=> Sx Sy; rewrite /multinom_of_seqmultinom_val /multinom_of_seqmultinom.
case (sumb _) => [prfx|] /=; [|by rewrite Sx eqxx].
case (sumb _) => [prfy|] /=; [|by rewrite Sy eqxx].
by move=> H; injection H.
Qed.

Lemma Rseqmultinom_eq n (x : 'X_{1..n}) x' y y' :
  Rseqmultinom x x' -> Rseqmultinom y y' -> (x == y) = (x' == y').
Proof.
move=> Hx Hy; apply/idP/idP => H.
{ have Sx' := @refines_size _ _ _ (trivial_param Hx).
  have Sy' := @refines_size _ _ _ (trivial_param Hy).
  apply/eqP.
  move: H Hy Hx; rewrite /Rseqmultinom /ofun_hrel; move/eqP -> => <-.
  by apply multinom_of_seqmultinom_inj. }
apply/eqP; move: H Hx Hy; rewrite /Rseqmultinom /ofun_hrel; move/eqP -> => ->.
by move=> H; inversion H.
Qed.

Lemma refines_size_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T)
  `{ref_pp' : !param Reffmpoly p p'} :
  forall m, M.In m p' -> size m == n.
Proof.
move: ref_pp'.
rewrite paramE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
set t := MProps.for_all _ _; case_eq t => //.
rewrite /t (MProps.for_all_iff _); [|by move=> m _ /mnmc_eq_seqP /eqP <-].
by move=> H _ m [e Hme]; apply (H m e).
Qed.

Lemma refines_find_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T) :
  Reffmpoly p p' ->
  forall m m', Rseqmultinom m m' ->
  p@_m = match M.find m' p' with None => 0 | Some c => c end.
Proof.
rewrite /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
set t := MProps.for_all _ _; case_eq t => //.
rewrite /t (MProps.for_all_iff _); [|by move=> m _ /mnmc_eq_seqP /eqP <-].
move=> H_sz H; injection H; move=> {H} H m m' Hm'.
rewrite -H mcoeff_MPoly coeff_Freeg.
case_eq (M.find m' p') => [c|] Hc.
{ change c with ((c, m).1); change m with ((c, m).2).
  apply precoeff_mem_uniqE.
  { rewrite /predom -map_comp.
    rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
    rewrite map_comp map_inj_in_uniq.
    { apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
    move=> x y Hx Hy; apply multinom_of_seqmultinom_val_inj.
    { move: Hx; move/mapP => [xe Hxe ->].
      apply/eqP /(H_sz _ xe.2) /M.elements_2.
      by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
    move: Hy; move/mapP => [ye Hye ->].
    apply/eqP /(H_sz _ ye.2) /M.elements_2.
    by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
  apply M.find_2, M.elements_1, in_InA_eq_key_elt_iff in Hc.
  apply/mapP; exists (m', c) => //=; f_equal.
  move: Hm'; rewrite /Rseqmultinom /ofun_hrel /multinom_of_seqmultinom_val.
  by case (multinom_of_seqmultinom n m') => // m'' Hm''; injection Hm''. }
apply precoeff_outdom.
rewrite /predom -map_comp.
rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
apply/negP=> Hm; apply MFacts.not_find_in_iff in Hc; apply Hc.
move/mapP in Hm; destruct Hm as [xe Hxe Hm].
rewrite MFacts.elements_in_iff; exists xe.2.
rewrite -in_InA_eq_key_elt_iff.
suff: m' = xe.1; [by move=> ->; rewrite -surjective_pairing|].
move: Hm' Hm; rewrite /Rseqmultinom /ofun_hrel /multinom_of_seqmultinom_val /=.
rewrite /multinom_of_seqmultinom /seqmultinom_of_multinom.
case (sumb _) => [prf|] //= Hm; injection Hm; move=> <- {Hm}.
case (sumb _) => [prf'|] //=; [by move=> H'; inversion H'|].
rewrite (H_sz xe.1 xe.2) => //; apply M.elements_2.
by rewrite -in_InA_eq_key_elt_iff -surjective_pairing.
Qed.

Lemma refines_effmpolyP (n : nat) T (p : mpoly n T) (p' : effmpoly T) :
  (forall m, M.In m p' -> size m == n)%N ->
  (forall m m', Rseqmultinom m m' ->
   p@_m = match M.find m' p' with None => 0 | Some c => c end) ->
  Reffmpoly p p'.
Proof.
move=> eq_sz eq_monom.
assert (Hsz : MProps.for_all (fun (k : M.key) (_ : T) => size k == n) p').
{ rewrite /is_true (MProps.for_all_iff _) => k e Hke.
  { by apply eq_sz; exists e. }
  by move=> _ _ _; move: Hke; move/mnmc_eq_seqP/eqP ->. }
rewrite /Reffmpoly /mpoly_of_effmpoly /ofun_hrel ifT //; f_equal.
apply mpolyP => m.
pose m' := seqmultinom_of_multinom m.
have Hm' : Rseqmultinom m m' by apply seqmultinom_of_multinomK.
rewrite (eq_monom _ _ Hm') mcoeff_MPoly coeff_Freeg.
case_eq (M.find m' p') => [c|] Hc.
{ change c with ((c, m).1); change m with ((c, m).2).
  apply precoeff_mem_uniqE.
  { rewrite /predom -map_comp.
    rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
    rewrite map_comp map_inj_in_uniq.
    { apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
    move=> x y Hx Hy; apply multinom_of_seqmultinom_val_inj.
    { move: Hx; move/mapP => [xe Hxe ->].
      apply/eqP /eq_sz; exists xe.2; apply/(M.elements_2 (e:=xe.2)).
      by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
    move: Hy; move/mapP => [ye Hye ->].
    apply/eqP /eq_sz; exists ye.2; apply/(M.elements_2 (e:=ye.2)).
    by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
  apply M.find_2, M.elements_1, in_InA_eq_key_elt_iff in Hc.
  apply/mapP; exists (m', c) => //=; f_equal.
  by rewrite /m' /multinom_of_seqmultinom_val seqmultinom_of_multinomK. }
apply precoeff_outdom.
rewrite /predom -map_comp.
rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
apply/negP=> Hm; apply MFacts.not_find_in_iff in Hc; apply Hc.
move/mapP in Hm; destruct Hm as [xe Hxe Hm].
rewrite MFacts.elements_in_iff; exists xe.2.
rewrite -in_InA_eq_key_elt_iff /m' Hm /= /multinom_of_seqmultinom_val.
rewrite /multinom_of_seqmultinom /seqmultinom_of_multinom.
case (sumb _) => [prf|] /=; [by rewrite -surjective_pairing|].
rewrite (@eq_sz xe.1); [by []|exists xe.2].
by apply /M.elements_2 /in_InA_eq_key_elt_iff; rewrite -surjective_pairing.
Qed.

(** *** Data refinement for effmpoly *)

Context {T : ringType}.
Context `{!one T, !add T, !sub T, !mul T}.
Context {n : nat}.

Hypothesis one_spec : 1%C = 1.

Global Instance param_mp0_eff : param (@Reffmpoly T n) 0%R mp0_eff.
Proof.
rewrite paramE.
apply: refines_effmpolyP.
- by move=> m /MProps.F.empty_in_iff Hm.
- by move=> m m' param_m; rewrite MFacts.empty_o mcoeff0.
Qed.

Global Instance param_mp1_eff : param (@Reffmpoly T n) 1%R (mp1_eff (n := n)).
Proof.
apply trivial_param; apply refines_effmpolyP.
- rewrite /mp1_eff => k /MProps.singleton_in_iff/mnmc_eq_seqP/eqP ->.
  by rewrite size_nseq.
- move=> m m' Hm; rewrite mcoeff1 MProps.F.add_o.
  have H0 := param_mnm0 n; rewrite paramE in H0.
  rewrite (Rseqmultinom_eq Hm H0).
  case: M.E.eq_dec => [EQ|nEQ].
  + by move/mnmc_eq_seqP/eqP: EQ <-; rewrite eqxx.
  + by rewrite eq_sym; move/mnmc_eq_seqP/negbTE: nEQ ->.
Qed.

Global Instance param_mpvar_eff :
  param (Logic.eq ==> Logic.eq ==> Rord ==> Reffmpoly (T := T) (n := n))
  mpvar (mpvar_eff (n := n)).
Proof.
apply param_abstr => c c' param_c; apply param_abstr => d d' param_d.
rewrite !paramE in param_c, param_d; rewrite -{}param_c -{}param_d {c' d'}.
apply param_abstr => i i' param_i.
rewrite paramE in param_i; rewrite -{}param_i {i'}.
assert (Hmnmd : Rseqmultinom (mnmd i d) (@mnmd_seq n i d)).
{ apply paramP; eapply param_apply; [|by apply param_eq_refl].
  by eapply param_apply; [apply param_mnmd|apply trivial_param]. }
rewrite paramE; apply refines_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  move/(@MProps.singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refines_size _ (mnmd i d)); rewrite paramE. }
move=> m m' Hm; rewrite mcoeffZ mcoeffX.
rewrite (Rseqmultinom_eq Hmnmd Hm) eq_sym.
case_eq (m' == (@mnmd_seq n i d)).
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite MProps.F.add_eq_o; [rewrite GRing.mulr1|apply M.E.eq_refl]. }
move=> Hm'; rewrite MProps.F.add_neq_o /=; [by rewrite GRing.mulr0|].
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Qed.

Arguments mpolyC {n R} c.
Global Instance param_mpolyC_eff :
  param (Logic.eq ==> Reffmpoly (T := T) (n := n))
  mpolyC (mpolyC_eff (n := n)).
Proof.
apply param_abstr => c c' param_c.
rewrite !paramE in param_c; rewrite -{}param_c {c'}.
rewrite paramE; apply refines_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  by move/(@MProps.singleton_mapsto T)=> [-> _]; rewrite size_nseq eqxx. }
move=> m m' Hm; rewrite mcoeffC.
have Hm0 := @param_mnm0 n; rewrite paramE in Hm0.
rewrite (Rseqmultinom_eq Hm Hm0).
case_eq (m' == @mnm0_seq n).
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite MProps.F.add_eq_o; [rewrite GRing.mulr1|apply M.E.eq_refl]. }
move=> Hm'; rewrite MProps.F.add_neq_o /=; [by rewrite GRing.mulr0|].
by apply/mnmc_eq_seqP; move: Hm'; rewrite eq_sym =>->.
Qed.

Arguments mpolyX {n R} m.
Global Instance param_mpolyX_eff :
  param (Rseqmultinom ==> Reffmpoly (T := T) (n := n))
  mpolyX mpolyX_eff.
Proof.
apply param_abstr => m m' param_m; rewrite paramE in param_m.
rewrite paramE; apply refines_effmpolyP.
{ move=> m'' [e Hme]; move: Hme; rewrite /mpolyX_eff.
  move/(@MProps.singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refines_size _ m); rewrite paramE. }
move=> m'' m''' Hm; rewrite mcoeffX.
rewrite (Rseqmultinom_eq param_m Hm) eq_sym.
case_eq (m''' == m').
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite MProps.F.add_eq_o /=; [|by apply M.E.eq_refl]. }
move=> Hm'; rewrite MProps.F.add_neq_o //=.
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Qed.

Arguments mpoly_scale {n R} c p.
Global Instance param_mpoly_scale_eff :
  param (Logic.eq ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_scale mpoly_scale_eff.
Admitted. (* Erik *)

Arguments mpoly_add {n R} p q.
Global Instance param_mpoly_add_eff :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_add mpoly_add_eff.
Admitted. (* Erik *)

Definition mpoly_sub (p : {mpoly T[n]}) q := mpoly_add p (mpoly_opp q).

Global Instance param_mpoly_sub_eff :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_sub mpoly_sub_eff.
Admitted. (* Erik *)

Arguments mpoly_mul {n R} p q.
Global Instance param_mpoly_mul_eff :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_mul mpoly_mul_eff.
Admitted. (* Erik *)

Definition mpoly_exp (p : {mpoly T[n]}) (n : nat) := (p ^+ n)%R.

Global Instance param_mpoly_exp_eff :
  param (Reffmpoly ==> Logic.eq ==> Reffmpoly (T := T) (n := n))
  mpoly_exp mpoly_exp_eff.
Admitted. (* Erik/Pierre *)

Definition seq_Reffmpoly k (lq : k.-tuple {mpoly T[n]}) (lq' : seq (effmpoly T)) :=
  size lq' = k /\ forall i, Reffmpoly lq`_i (nth mp0_eff lq' i).

Lemma param_comp_monomial_eff k :
  param (Rseqmultinom ==> Logic.eq ==> @seq_Reffmpoly k ==> Reffmpoly)
  (fun m c lq => mpolyC c * mmap1 (tnth lq) m) (comp_monomial_eff (n:= n)).
Proof.
apply param_abstr => m m' param_m.
apply param_abstr => c c' param_c.
rewrite paramE in param_c; rewrite -{}param_c {c'}.
apply param_abstr => lq lq' param_lq.
rewrite mul_mpolyC /comp_monomial_eff; eapply param_apply.
{ eapply param_apply; [apply param_mpoly_scale_eff|apply param_eq_refl]. }
move: param_lq; rewrite paramE /seq_Reffmpoly; move => [sz_lq param_lq].
move: m m' param_m lq lq' sz_lq param_lq.
elim: k => [|k IHk] m m' param_m lq lq' sz_lq param_lq.
{ rewrite /mmap1 bigop.big_ord0.
  move: (size0nil sz_lq) => ->; rewrite /zipwith /=; apply param_mp1_eff. }
move: sz_lq; case_eq lq' => //= q0 lqt' Hlq' sz_lq.
move: (@refines_size _ _ _ param_m); case_eq m' => //= m0 mt' Hm' sz_m'.
rewrite /foldr /= -/(foldr _ _) /mmap1 bigop.big_ord_recl.
eapply param_apply; [eapply param_apply; [by apply param_mpoly_mul_eff|]|].
{ move: (@refines_nth _ _ _ ord0 param_m); rewrite Hm' /= => <-.
  eapply param_apply; [|by apply param_eq_refl].
  eapply param_apply; [by apply param_mpoly_exp_eff|]; rewrite paramE.
  replace (tnth _ _) with (lq`_O); [|by case lq, tval].
  change q0 with (nth mp0_eff (q0 :: lqt') O); rewrite -Hlq'; apply param_lq. }
injection sz_lq => {sz_lq} sz_lq; injection sz_m' => {sz_m'} sz_m'.
assert (param_mt : param Rseqmultinom (multinom_of_seqmultinom_val k mt') mt').
{ by rewrite paramE; apply /refines_multinom_of_seqmultinom_val /eqP. }
assert (Hlq_lq' : forall i : nat,
                    Reffmpoly [tuple of behead lq]`_i (nth mp0_eff lqt' i)).
{ by move=> i; move: (param_lq i.+1); rewrite Hlq' /=; case tval; elim i. }
move: (IHk _ _ param_mt [tuple of behead lq] _ sz_lq Hlq_lq').
rewrite paramE /Reffmpoly /ofun_hrel => ->; f_equal.
apply bigop.eq_big => // i _; f_equal.
{ rewrite tnth_behead; f_equal.
  by apply ord_inj; rewrite inordK //; move: (ltn_ord i). }
move /eqP in sz_m'; move: (refines_multinom_of_seqmultinom_val sz_m') => Hmt'.
apply trivial_param in Hmt'; move: (@refines_nth _ _ _ i Hmt') => <-.
move: (@refines_nth _ _ _ (inord i.+1) param_m); rewrite Hm' /=.
rewrite inordK /=; [|by rewrite ltnS]; move=> ->; apply f_equal.
by apply ord_inj; rewrite inordK //; move: (ltn_ord i).
Qed.

Arguments comp_mpoly {n R k} lq p.
Global Instance param_comp_mpoly_eff k :
  param (@seq_Reffmpoly k ==> Reffmpoly ==> Reffmpoly)
  comp_mpoly (comp_mpoly_eff (n:= n)).
Proof.
apply param_abstr => lq lq' param_lq.
apply param_abstr => p p' param_p.
(*
rewrite paramE; apply refines_effmpolyP.
{ move=> m; rewrite /comp_mpoly_eff.
  apply MProps.fold_rec; [by move=> _ _; rewrite MFacts.empty_in_iff|].
  move=> k' e p'' m' m''.
*)
Admitted. (* Pierre *)

End seqmpoly_theory.
