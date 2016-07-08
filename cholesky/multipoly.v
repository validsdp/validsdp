Require Import FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype ssralg bigop.
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

Section effmpoly_generic.

(** Monomials *)

(* TODO: may be refactored by using mnm1, mnm_add, mnm_muln *)
Definition mnmd {n} (i : 'I_n) (d : nat) :=
  [multinom (if (i == j :> nat) then d else 0%N) | j < n].

Definition mpvar {T : ringType} {n} (c : T) d i : {mpoly T[n]} :=
  c *: 'X_[mnmd i d].

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

End effmpoly_generic.

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

(*Module M := FMapList.Make MultinomOrd.*)
Module M := FMapAVL.Make MultinomOrd.

Arguments M.empty {elt}.

Definition effmpoly := M.t.

Module MFacts := Facts M.

Module MProps.

Include Properties M.

Definition singleton T key (val : T) := M.add key val M.empty.

Lemma singleton_mapsto {T} k k' (e e' : T) :
  M.MapsTo k e (singleton k' e') -> (k = k' /\ e = e').
Proof.
rewrite F.add_mapsto_iff; elim; move=> [Hk He]; [split; [|by[]]|].
{ by move: Hk; move /mnmc_eq_seqP/eqP. }
by move: He; rewrite F.empty_mapsto_iff.
Qed.

Lemma singleton_in_iff {T} y k (e : T) :
  M.In y (singleton k e) <-> M.E.eq y k.
Proof.
split; [move/MFacts.add_in_iff|move=> H; apply/MFacts.add_in_iff].
by intuition; move/MFacts.empty_in_iff in H.
by left; symmetry.
Qed.

End MProps.

Section effmpoly_generic_2.

(* FIXME: ensure that [effmpoly_of_list] won't overwrite duplicate monomials *)
Definition effmpoly_of_list : forall T, seq (seqmultinom * T) -> effmpoly T :=
  MProps.of_list.

Definition list_of_effmpoly : forall T, effmpoly T -> seq (seqmultinom * T) :=
  M.elements.

Context {T : Type} `{!one T, !add T, !opp T, !sub T, !mul T} {n : nat}.

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
    | Some c, _ => Some c
    | _, Some c => Some (- c)%C
    | None, None => None
    end).

Definition mult_monomial_eff (m : seqmultinom) (c : T) (p : effmpoly T) : effmpoly T :=
  M.fold (fun m' c' (*acc*) => M.add (mnm_add_seq m m') (c * c')%C (*acc*)) p M.empty.

Definition mpoly_mul_eff (p q : effmpoly T) : effmpoly T :=
  M.fold (fun m c => mpoly_add_eff (mult_monomial_eff m c q)) p mp0_eff.

(* TODO: fast exponentiation *)
Definition mpoly_exp_eff (p : effmpoly T) (n : nat) := iterop n mpoly_mul_eff p mp1_eff.

Definition comp_monomial_eff (m : seqmultinom) (c : T) (lq : seq (effmpoly T)) : effmpoly T :=
  let mq := zipwith mpoly_exp_eff lq m in
  mpoly_scale_eff c (foldr mpoly_mul_eff mp1_eff mq).

Definition comp_mpoly_eff (lq : seq (effmpoly T)) (p : effmpoly T) : effmpoly T :=
  M.fold (fun m c => mpoly_add_eff (comp_monomial_eff m c lq)) p mp0_eff.

End effmpoly_generic_2.

(** ** Part II: Proofs for proof-oriented types and programs *)

Section effmpoly_theory.

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

Lemma refines_seqmultinom_of_multinom (n : nat) (m : 'X_{1..n}) :
  Rseqmultinom m (seqmultinom_of_multinom m).
Proof. by rewrite /Rseqmultinom /ofun_hrel seqmultinom_of_multinomK. Qed.

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

Global Instance param_mnm_add n :
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

Definition mpoly_of_effmpoly_val (T : ringType) n (p' : effmpoly T) : mpoly n T :=
  odflt (0%R) (mpoly_of_effmpoly n p').

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
  { apply InA_cons_hd; change (M.eq_key _ _) with (M.E.eq x.1 h.1).
    move: Hh => /eqP ->; apply M.E.eq_refl. }
  by apply InA_cons_tl, Hind. }
elim s => [|h t Hind]; [by rewrite InA_nil|].
rewrite InA_cons; elim.
{ change (M.eq_key _ _) with (M.E.eq x.1 h.1).
  by move/mnmc_eq_seqP/eqP =>->; rewrite inE eqxx. }
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
  forall m m', Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p').
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
  (forall m m', Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p')) ->
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
Instance : one T := 1%R.
Instance : add T := +%R.
Instance : opp T := -%R.
Instance : sub T := fun a b => (a - b)%R.
Instance mul_instR : mul T := *%R.

Global Instance param_mp0_eff n : param (@Reffmpoly T n) 0%R mp0_eff.
Proof.
rewrite paramE.
apply: refines_effmpolyP.
- by move=> m /MProps.F.empty_in_iff Hm.
- by move=> m m' param_m; rewrite MFacts.empty_o mcoeff0.
Qed.

Global Instance param_mp1_eff n : param (@Reffmpoly T n) 1%R (mp1_eff (n := n)).
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

Global Instance param_mpvar_eff n :
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
Global Instance param_mpolyC_eff n :
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
Global Instance param_mpolyX_eff n :
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

Lemma MapsTo_mcoeff {n} m m' p p' a :
  (Reffmpoly (T := T) (n := n)) p p' ->
  Rseqmultinom m m' ->
  M.MapsTo m' a p' -> p@_m = a.
(* the converse may be wrong if [a = 0] *)
Proof.
move=> Hp Hm HMT.
move/MFacts.find_mapsto_iff in HMT.
by rewrite (refines_find_mpoly Hp Hm) /odflt /oapp HMT.
Qed.

Lemma not_In_mcoeff {n} m m' p p' :
  (Reffmpoly (T := T) (n := n)) p p' ->
  Rseqmultinom m m' ->
  ~ M.In m' p' -> p@_m = 0.
Proof.
move=> Hp Hm Hin.
rewrite (refines_find_mpoly Hp Hm).
by move/MFacts.not_find_in_iff: Hin ->.
Qed.

Arguments mpoly_scale {n R} c p.
Global Instance param_mpoly_scale_eff n :
  param (Logic.eq ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_scale mpoly_scale_eff.
Proof.
apply param_abstr => c c' param_c.
apply param_abstr => p p' param_p.
rewrite /mpoly_scale_eff paramE; apply: refines_effmpolyP.
{ move=> m /M.map_2 Hm; exact: refines_size_mpoly param_p _ _. }
move=> m m' param_m; rewrite mcoeffZ.
case Es: (M.find _ _) => [s|] /=.
{ have /MFacts.find_mapsto_iff/MFacts.map_mapsto_iff [a [-> Ha2 /=]] := Es.
  rewrite (param_eq param_c).
  congr *%R.
  rewrite paramE in param_p; apply: MapsTo_mcoeff param_p param_m Ha2. }
move/MFacts.not_find_in_iff in Es.
suff->: p@_m = 0 by rewrite GRing.mulr0.
rewrite paramE in param_p.
apply: not_In_mcoeff param_p param_m _.
move=> K; apply: Es.
exact/MFacts.map_in_iff.
Qed.

Arguments mpoly_add {n R} p q.
Global Instance param_mpoly_add_eff n :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_add mpoly_add_eff.
Proof.
apply param_abstr => p p' param_p.
apply param_abstr => q q' param_q.
rewrite paramE /mpoly_add_eff.
apply: refines_effmpolyP.
{ move=> m /MFacts.in_find_iff Hm.
  have [Hip'|Hiq'] : M.In m p' \/ M.In m q'.
    rewrite !MFacts.in_find_iff.
    rewrite MFacts.map2_1bis // in Hm.
    case: M.find Hm; case: M.find; try by[left|left|right|].
  exact: refines_size_mpoly Hip'.
  exact: refines_size_mpoly Hiq'. }
move=> m m' Hm.
rewrite mcoeffD MFacts.map2_1bis //.
rewrite paramE in param_p param_q.
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff param_p Hm Ep) (MapsTo_mcoeff param_q Hm Eq).
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff param_p Hm Ep) (not_In_mcoeff param_q Hm Eq)
  GRing.addr0.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff param_p Hm Ep) (MapsTo_mcoeff param_q Hm Eq)
  GRing.add0r.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff param_p Hm Ep) (not_In_mcoeff param_q Hm Eq)
  GRing.addr0.
Qed.

Definition mpoly_sub {n} (p : {mpoly T[n]}) q := mpoly_add p (mpoly_opp q).

Global Instance param_mpoly_sub_eff n :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_sub mpoly_sub_eff.
apply param_abstr => p p' param_p.
apply param_abstr => q q' param_q.
rewrite paramE /mpoly_add_eff.
apply: refines_effmpolyP.
{ move=> m /MFacts.in_find_iff Hm.
  have [Hip'|Hiq'] : M.In m p' \/ M.In m q'.
    rewrite !MFacts.in_find_iff.
    rewrite MFacts.map2_1bis // in Hm.
    case: M.find Hm; case: M.find; try by[left|left|right|].
  exact: refines_size_mpoly Hip'.
  exact: refines_size_mpoly Hiq'. }
move=> m m' Hm.
rewrite mcoeffB MFacts.map2_1bis //.
rewrite paramE in param_p param_q.
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff param_p Hm Ep) (MapsTo_mcoeff param_q Hm Eq).
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff param_p Hm Ep) (not_In_mcoeff param_q Hm Eq)
  GRing.subr0.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff param_p Hm Ep) (MapsTo_mcoeff param_q Hm Eq)
  GRing.sub0r.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff param_p Hm Ep) (not_In_mcoeff param_q Hm Eq)
  GRing.subr0.
Qed.

Lemma rem_mpoly_eff n (q p' : effmpoly T) (k' : seqmultinom) (e : T)
  (p : mpoly n T) (k : 'X_{1..n}) :
  ~ M.In k' q -> MProps.Add k' e q p' -> Reffmpoly p p' ->
  Rseqmultinom k k' -> Reffmpoly (p - p@_k *: 'X_[k]) q.
Proof.
move=> Hin Hadd Hp Hk.
apply refines_effmpolyP.
{ move=> m'' [c' Hc']; move: (Hadd m''); rewrite MFacts.add_o.
  case M.E.eq_dec.
  { move/mnmc_eq_seqP/eqP <-; rewrite -MFacts.find_mapsto_iff => Hm.
    by apply (@refines_size_mpoly _ _ _ _ (trivial_param Hp)); exists e. }
  rewrite (proj1 (MFacts.find_mapsto_iff q m'' c')) // => _ H.
  apply (@refines_size_mpoly _ _ _ _ (trivial_param Hp)).
  by exists c'; move: H; rewrite -MFacts.find_mapsto_iff. }
move=> mm mm' param_mm; move: (Hadd mm'); rewrite MFacts.add_o.
rewrite mcoeffB mcoeffZ mcoeffX.
case M.E.eq_dec.
{ move/mnmc_eq_seqP/eqP => Hmm'; rewrite -Hmm'.
  have Hmm : k = mm.
  { by apply/eqP; rewrite (Rseqmultinom_eq Hk param_mm); apply/eqP. }
  rewrite (proj1 (MFacts.not_find_in_iff _ _) Hin) -Hmm eqxx GRing.mulr1.
  by rewrite (refines_find_mpoly Hp Hk) => ->; rewrite GRing.subrr. }
move=> Hmm' <-.
have Hmm : ~ k = mm.
{ move=> Hmmm; apply/Hmm'/mnmc_eq_seqP.
  by rewrite -(Rseqmultinom_eq Hk param_mm); apply/eqP. }
rewrite (refines_find_mpoly Hp param_mm).
by have ->: (k == mm = false); [apply/eqP|rewrite GRing.mulr0 GRing.subr0].
Qed.

Lemma param_mpoly_sum_eff n k f f' (p : mpoly k T) p' :
  (forall m, f m 0 = 0) ->
  param (Rseqmultinom ==> Logic.eq ==> Reffmpoly (T:=T) (n:=n)) f f' ->
  param Reffmpoly p p' ->
  param Reffmpoly (\sum_(m <- msupp p) f m p@_m)
                  (M.fold (fun m c => mpoly_add_eff (f' m c)) p' mp0_eff).
Proof.
move=> Hf param_f; move: p; rewrite paramE.
apply MProps.fold_rec.
{ move=> q' Eq' q Hq.
  suff -> : q = 0; [by rewrite msupp0 big_nil; apply param_mp0_eff|].
  apply /mpolyP => m.
  rewrite (refines_find_mpoly Hq (refines_seqmultinom_of_multinom m)).
  rewrite mcoeff0; case_eq (M.find (seqmultinom_of_multinom m) q') => [s|->]//.
  rewrite -MFacts.find_mapsto_iff MFacts.elements_mapsto_iff.
  by rewrite -in_InA_eq_key_elt_iff (proj1 (MProps.elements_Empty _ ) Eq'). }
move=> m' c p'' q q' Hp'' Hq Hq' IH p Hp.
pose m := multinom_of_seqmultinom_val k m'; pose cm := c *: 'X_[m].
have param_m : Rseqmultinom m m'.
{ apply refines_multinom_of_seqmultinom_val.
  move: (Hq' m'); rewrite MFacts.add_eq_o; [|by apply/mnmc_eq_seqP]; move=> Hm'.
  apply (@refines_size_mpoly _ _ _ _ (trivial_param Hp)).
  by exists c; apply M.find_2. }
have Hc : p@_m = c.
{ rewrite (refines_find_mpoly Hp param_m) (Hq' m') MFacts.add_eq_o //.
  apply M.E.eq_refl. }
pose pmcm := p - cm.
have Hpmcm : pmcm@_m = 0.
{ by rewrite mcoeffB mcoeffZ mcoeffX eqxx Hc GRing.mulr1 GRing.subrr. }
have -> : \sum_(m <- msupp p) f m p@_m
  = f m c + \sum_(m <- msupp pmcm) f m pmcm@_m.
{ case_eq (m \in msupp p) => Hmsuppp.
  { rewrite (big_rem _ Hmsuppp) /= Hc; f_equal.
    rewrite /pmcm /cm -Hc -(eq_big_perm _ (msupp_rem p m)) /=.
    apply eq_big_seq => i.
    rewrite mcoeffB mcoeffZ mcoeffX.
    rewrite mcoeff_msupp Hc -/cm -/pmcm -Hpmcm.
    case (@eqP _ m i) => [->|]; [by rewrite eqxx|].
    by rewrite GRing.mulr0 GRing.subr0. }
  move: Hmsuppp; rewrite /pmcm /cm mcoeff_msupp Hc; move/eqP ->.
  by rewrite Hf GRing.add0r GRing.scale0r GRing.subr0. }
eapply param_apply.
{ eapply param_apply; [by apply param_mpoly_add_eff|].
  eapply param_apply; [|by apply param_eq_refl].
  eapply param_apply; [apply param_f|rewrite paramE; apply param_m]. }
apply IH.
rewrite /pmcm /cm -Hc.
apply (rem_mpoly_eff Hq Hq' Hp param_m).
Qed.

Lemma Rseqmultinom_iff {n} l l' :
  (Rseqmultinom (n := n)) l l' <-> l = l' :> seq nat.
Proof.
split => Hmain.
{ apply eq_from_nth with (x0 := O).
  { by rewrite size_tuple refines_size. }
  move=> i Hi.
  rewrite size_tuple in Hi.
  case: n l Hmain Hi => // n l Hmain Hi.
  by rewrite -(inordK Hi) refines_nth -tnth_nth.
}
apply: refines_seqmultinomP.
{ by rewrite -Hmain size_tuple. }
case: n l Hmain => [|n] l Hmain i; first by case: i.
by rewrite (mnm_nth O) Hmain.
Qed.

Lemma param_Madd_mnm_add {n} (m : 'X_{1.. n}) m' (c : T) p p' :
  param Rseqmultinom m m' ->
  param Reffmpoly p p' ->
  m \notin msupp p ->
  param Reffmpoly (+%R (c *: 'X_[m]) p) (M.add m' c p').
Proof.
move=> Hm Hp Hnotin.
rewrite paramE.
rewrite paramE in Hm.
apply: refines_effmpolyP.
{ move=> k /MFacts.add_in_iff [Hk|Hk].
  - move/mnmc_eq_seqP/eqP: Hk <-.
    move/Rseqmultinom_iff: Hm <-.
    by rewrite size_tuple.
  - exact: refines_size_mpoly. }
move=> l l' Hl; rewrite mcoeffD mcoeffZ mcoeffX.
case: (boolP (m == l)) => Heq /=.
{ rewrite GRing.mulr1.
  rewrite MFacts.add_eq_o /=; last first.
  { apply/mnmc_eq_seqP.
    move/Rseqmultinom_iff: Hm <-.
    move/eqP: Heq ->.
    by move/Rseqmultinom_iff: Hl ->. }
  move/eqP in Heq; rewrite Heq in Hnotin.
  by rewrite memN_msupp_eq0 // GRing.addr0.
}
rewrite GRing.mulr0 GRing.add0r.
rewrite MFacts.add_neq_o /=; last first.
{ apply/mnmc_eq_seqP.
  move/Rseqmultinom_iff: Hm <-.
  by move/Rseqmultinom_iff: Hl <-.
}
rewrite paramE in Hp.
exact: refines_find_mpoly.
Qed.

Lemma refines_size_add n (k' : seqmultinom) (e : T)
  (p : mpoly n T) (p' : effmpoly T) (q : effmpoly T) :
  MProps.Add k' e q p' -> Reffmpoly p p' ->
  Rseqmultinom (multinom_of_seqmultinom_val n k') k'.
Proof.
move=> Hadd Hp.
apply refines_multinom_of_seqmultinom_val.
apply (@refines_size_mpoly _ _ _ _ (trivial_param Hp)).
exists e; move: (Hadd k'); rewrite MFacts.add_eq_o; [|by apply M.E.eq_refl].
apply M.find_2.
Qed.

Lemma param_Madd_mnm_add_sum n m m' c (p : mpoly n T) p' :
   param Rseqmultinom m m' ->
   param (Reffmpoly (T := T) (n := n)) p p' ->
   param Reffmpoly (\sum_(i2 <- msupp p) (c * p@_i2) *: 'X_[m + i2])
         (M.fold (fun (l' : M.key) (c' : T) => M.add (mnm_add_seq m' l') (c * c')%C) p' M.empty).
Proof.
move=> param_m; move: p; rewrite paramE.
apply MProps.fold_rec.
{ move=> q' Eq' q Hq.
  match goal with
  | [  |- Reffmpoly ?pol M.empty ] => suff ->: pol = 0
  end.
  { by apply paramP, param_mp0_eff. }
  apply /mpolyP => l.
  rewrite big1 ?mcoeff0 //.
  move=> i _.
  rewrite (refines_find_mpoly Hq (refines_seqmultinom_of_multinom i)) /=.
  case_eq (M.find (seqmultinom_of_multinom i) q') =>[s|/=].
  - rewrite -MFacts.find_mapsto_iff MFacts.elements_mapsto_iff.
    by rewrite -in_InA_eq_key_elt_iff (proj1 (MProps.elements_Empty _ ) Eq').
  - by move=> _; rewrite GRing.mulr0 GRing.scale0r.
}
move=> k' e q p'' p''' Hmap Hin Hadd Hind p param_p.
pose k := multinom_of_seqmultinom_val n k'.
have Hk : Rseqmultinom k k'; [by apply (refines_size_add Hadd param_p)|].
have Hp : p@_k = e.
{ rewrite (refines_find_mpoly param_p Hk) Hadd MFacts.add_eq_o //.
  exact: M.E.eq_refl. }
pose p0 := (c * e) *: 'X_[m + k].
pose pmpk := p - p@_k *: 'X_[k].
have Hpmpk : pmpk@_k = 0.
{ by rewrite mcoeffB mcoeffZ mcoeffX eqxx Hp GRing.mulr1 GRing.subrr. }
set sum := \sum_(_ <- _) _.
have->: sum = p0 + \big[+%R/0]_(i2 <- msupp pmpk) ((c * pmpk@_i2) *: 'X_[(m + i2)]).
{ rewrite /sum /pmpk /p0.
  case_eq (k \in msupp p) => Hmsuppp.
  { rewrite (big_rem _ Hmsuppp) /= Hp; f_equal.
    rewrite -Hp -(eq_big_perm _ (msupp_rem p k)) /=.
    apply eq_big_seq => i.
    rewrite mcoeffB mcoeffZ mcoeffX.
    rewrite mcoeff_msupp Hp -Hpmpk.
    case (boolP (k == i)).
    { move/eqP<-; rewrite Hpmpk.
      by rewrite mcoeffB Hp mcoeffZ mcoeffX eqxx GRing.mulr1 GRing.subrr eqxx. }
    by rewrite GRing.mulr0 GRing.subr0. }
  move: Hmsuppp; rewrite mcoeff_msupp Hp; move/eqP ->.
  by rewrite GRing.mulr0 GRing.scale0r GRing.add0r GRing.scale0r GRing.subr0. }
apply paramP; rewrite /p0.
apply param_Madd_mnm_add.
{ eapply param_apply; first by eapply param_apply; tc.
  rewrite paramE /k.
  apply refines_multinom_of_seqmultinom_val.
  apply (@refines_size_mpoly _ _ _ _ (trivial_param param_p)).
  red in Hadd.
  apply/MFacts.in_find_iff.
  rewrite Hadd MFacts.add_eq_o //.
  exact/mnmc_eq_seqP.
}
{ rewrite paramE; apply: Hind.
  apply (rem_mpoly_eff Hin Hadd param_p Hk). }
rewrite mcoeff_msupp negbK.
set F' := fun i2 => (c *: 'X_[m]) * (pmpk@_i2 *: 'X_[i2]).
rewrite (eq_bigr F').
{ rewrite -big_distrr /= -mpolyE.
  rewrite (mcoeff_poly_mul _ _ (k:=(mdeg (m + k)).+1)) //.
  rewrite big1 // => k0.
  case (boolP (m == k0.1)).
  { by move/eqP<-; rewrite eqm_add2l; move/eqP <-; rewrite Hpmpk GRing.mulr0. }
  by rewrite mcoeffZ mcoeffX; move /negbTE ->; rewrite GRing.mulr0 GRing.mul0r. }
move=> m'' _; rewrite /F'; rewrite mpolyXD.
rewrite -GRing.scalerAl -GRing.scalerA; f_equal.
by rewrite -[RHS]commr_mpolyX -GRing.scalerAl commr_mpolyX.
Qed.

Arguments mpoly_mul {n R} p q.
Global Instance param_mpoly_mul_eff n :
  param (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_mul mpoly_mul_eff.
Proof.
apply param_abstr => q q' param_q.
apply param_abstr => p p' param_p.
rewrite [mpoly_mul q p]mpolyME -ssrcomplements.pair_bigA_seq_curry /=.
rewrite /mpoly_mul_eff.
pose f m c := \big[+%R/0]_(i2 <- msupp p) ((c * p@_i2) *: 'X_[(m + i2)]).
pose f' m c := @mult_monomial_eff _ mul_instR m c p'.
now_show (param Reffmpoly (\sum_(m <- msupp q) f m q@_m)
  (M.fold (fun m c => mpoly_add_eff (f' m c)) q' M.empty)).
apply(*:*) param_mpoly_sum_eff =>//.
- by move=> m; rewrite /f big1 // => m2 _; rewrite GRing.mul0r GRing.scale0r.
- apply param_abstr => m m' param_m.
  apply param_abstr => c c' param_c.
  rewrite /f /f' /mult_monomial_eff.
  rewrite {param_c}(param_eq param_c).
  by apply param_Madd_mnm_add_sum.
Qed.

Definition mpoly_exp {n} (p : {mpoly T[n]}) (n : nat) := (p ^+ n)%R.

Global Instance param_mpoly_exp_eff n :
  param (Reffmpoly ==> Logic.eq ==> Reffmpoly (T := T) (n := n))
  mpoly_exp (mpoly_exp_eff (n:=n)).
Proof.
apply param_abstr => p p' param_p.
apply param_abstr => n' n''; rewrite paramE => <- {n''}.
rewrite /mpoly_exp /mpoly_exp_eff.
elim: n' => [|n' IHn]; [by rewrite GRing.expr0; apply param_mp1_eff|].
rewrite GRing.exprS /=; case_eq n'; [by rewrite GRing.expr0 GRing.mulr1|].
move=> _ <-; eapply param_apply; [|exact IHn].
by eapply param_apply; [apply param_mpoly_mul_eff|].
Qed.

Definition seq_Reffmpoly n k (lq : k.-tuple {mpoly T[n]}) (lq' : seq (effmpoly T)) :=
  size lq' = k /\ forall i, Reffmpoly lq`_i (nth mp0_eff lq' i).

Lemma param_comp_monomial_eff n k :
  param (Rseqmultinom ==> Logic.eq ==> @seq_Reffmpoly n k ==> Reffmpoly)
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
Global Instance param_comp_mpoly_eff n k :
  param (@seq_Reffmpoly n k ==> Reffmpoly ==> Reffmpoly)
  comp_mpoly (comp_mpoly_eff (n:= n)).
Proof.
apply param_abstr => lq lq' param_lq.
apply param_abstr => p p' param_p.
rewrite /comp_mpoly /mmap /comp_mpoly_eff.
pose f := fun m c => c%:MP_[n] * mmap1 (tnth lq) m.
rewrite (eq_bigr (fun m => f m p@_m)) //.
apply param_mpoly_sum_eff.
{ by move=> m; rewrite /f mpolyC0 GRing.mul0r. }
{ apply param_abstr => m m' param_m.
  apply param_abstr => c c'; rewrite paramE /f => <-.
  change (_ * _) with ((fun lq => c%:MP_[n] * mmap1 (tnth lq) m) lq).
  eapply param_apply; [|by apply param_lq].
  change (fun _ => _) with ((fun c lq => c%:MP_[n] * mmap1 (tnth lq) m) c).
  eapply param_apply; [|by apply param_eq_refl].
  change (fun _ => _) with ((fun m (c : T) lq => c%:MP_[n] * mmap1 (tnth lq) m) m).
  eapply param_apply; [apply param_comp_monomial_eff|apply param_m]. }
apply param_p.
Qed.

End effmpoly_theory.

(** ** Part III: Parametricity *)

Section effmpoly_parametricity.

Context (A : ringType) (C : Type) (rAC : A -> C -> Prop).

Definition M_hrel (m : M.t A) (m' : M.t C) : Prop :=
  (forall k, M.In k m <-> M.In k m')
  /\ forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> rAC e e'.

Definition ReffmpolyA {n} := (@Reffmpoly A n \o M_hrel)%rel.

Context `{one C, opp C, add C, sub C, mul C}.

Context `{!param rAC 1%R 1%C}.
Context `{!param (rAC ==> rAC) -%R -%C}.
Context `{!param (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!param (rAC ==> rAC ==> rAC) (fun x y => x + -y) sub_op}.
Context `{!param (rAC ==> rAC ==> rAC) *%R *%C}.

Lemma param_M_hrel_empty : param M_hrel M.empty M.empty.
Proof.
rewrite paramE; split.
{ by move=> k; rewrite !MFacts.empty_in_iff. }
by move=> k e e'; rewrite MFacts.empty_mapsto_iff.
Qed.

Lemma param_M_hrel_add :
  param (Logic.eq ==> rAC ==> M_hrel ==> M_hrel) (@M.add A) (@M.add C).
Proof.
rewrite paramE; split.
{ by move=> k; rewrite !MFacts.add_in_iff H4; split;
  (elim; [by left|right]); [rewrite -(proj1 H6 k)|rewrite (proj1 H6 k)]. }
move=> k e e'; rewrite !MFacts.add_mapsto_iff H4.
elim=> [[Hy <-]|[Hy He]].
{ move: Hy; move/mnmc_eq_seqP/eqP->.
  by elim=>[[_ <-]|] //; rewrite M.E.eq_refl; elim. }
by elim; [elim=> H'; elim (Hy H')|elim=>_; apply (proj2 H6)].
Qed.

Lemma param_M_hrel_singleton :
  param (Logic.eq ==> rAC ==> M_hrel)
     (@MProps.singleton A) (@MProps.singleton C).
Proof.
apply param_abstr => k k'; rewrite paramE => <-.
apply param_abstr => e e' param_e.
rewrite /MProps.singleton.
eapply param_apply; [|by apply param_M_hrel_empty].
eapply param_apply; [|exact param_e].
eapply param_apply; [apply param_M_hrel_add|apply param_eq_refl].
Qed.

Lemma param_M_hrel_map :
  param ((rAC ==> rAC) ==> M_hrel ==> M_hrel) (@M.map A A) (@M.map C C).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => m m' param_m.
rewrite paramE; split.
{ move=> k; rewrite !MProps.F.map_in_iff.
  move: param_m; rewrite paramE => H'; apply H'. }
move=> k e e'.
rewrite !MFacts.map_mapsto_iff => [[a Ha] [a' Ha']].
rewrite (proj1 Ha) (proj1 Ha').
apply paramP; eapply param_apply; [by apply param_f|].
move: param_m (proj2 Ha) (proj2 Ha'); rewrite !paramE => param_m.
apply (proj2 param_m).
Qed.

Lemma param_M_hrel_find :
  param (Logic.eq ==> M_hrel ==> ohrel rAC) (@M.find A) (@M.find C).
Proof.
apply param_abstr => k k'; rewrite paramE => <-.
apply param_abstr => m m'; rewrite paramE => param_m.
rewrite paramE; case_eq (M.find k m') => [e'|]; case_eq (M.find k m) => [e|].
{ rewrite -!MFacts.find_mapsto_iff /=; apply (proj2 param_m). }
{ rewrite -MFacts.not_find_in_iff /= => H' H''; apply H'.
  by apply (proj1 param_m); rewrite MFacts.in_find_iff H''. }
{ rewrite -MFacts.not_find_in_iff /= => H' H''; apply H''.
  by apply (proj1 param_m); rewrite MFacts.in_find_iff H'. }
by [].
Qed.
  
Lemma param_M_hrel_map2 :
  param ((ohrel rAC ==> ohrel rAC ==> ohrel rAC) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.map2 A A A) (@M.map2 C C C).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => m1 m1' param_m1.
apply param_abstr => m2 m2' param_m2.
have Hf : forall k, ohrel rAC (f (M.find k m1) (M.find k m2))
                      (f' (M.find k m1') (M.find k m2')).
{ move=> k; apply paramP; eapply param_apply; [eapply param_apply|].
  { apply param_f. }
  { eapply param_apply; [|by apply param_m1].
    eapply param_apply; [apply param_M_hrel_find|apply param_eq_refl]. }
  eapply param_apply; [|by apply param_m2].
  eapply param_apply; [apply param_M_hrel_find|apply param_eq_refl]. }
rewrite paramE; rewrite paramE in param_m1, param_m2; split.
{ move=> k; split.
  { move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
    apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
    move: (Hf k); rewrite He; case_eq (f' (M.find k m1') (M.find k m2')) => //.
    move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
    by destruct Hor as [Hk|Hk]; [left; apply param_m1|right; apply param_m2]. }
  move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
  apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
  move: (Hf k); rewrite He; case_eq (f (M.find k m1) (M.find k m2)) => //.
  move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
  by destruct Hor as [Hk|Hk]; [left; apply param_m1|right; apply param_m2]. }
move=> k e e' He He'; move: (M.find_1 He) (M.find_1 He') (Hf k).
case_eq (M.find k m1) => [e1|] He1.
{ rewrite M.map2_1; [|by left; exists e1; apply M.find_2].
  rewrite M.map2_1; [|by left; apply param_m1; exists e1; apply M.find_2].
  by rewrite He1 => -> ->. }
case_eq (M.find k m2) => [e2|] He2.
{ rewrite M.map2_1; [|by right; exists e2; apply M.find_2].
  rewrite M.map2_1; [|by right; apply param_m2; exists e2; apply M.find_2].
  by rewrite He1 He2 => -> ->. }
elim (@M.map2_2 _ _ _ m1 m2 k f); [| |by exists e].
{ by move=> [e'1 He'1]; apply M.find_1 in He'1; rewrite He'1 in He1. }
by move=> [e'2 He'2]; apply M.find_1 in He'2; rewrite He'2 in He2.
Qed.

Lemma Sorted_InA_not_lt_hd B (ke h : M.key * B) t :
  Sorted (M.lt_key (elt:=B)) (h :: t) ->
  InA (M.eq_key_elt (elt:=B)) ke (h :: t) ->
  ~ M.lt_key ke h.
Proof.
move: h; elim t => [|h' t' IH] h.
{ move=> _ Hin; inversion Hin; move=> Hlt.
  { by move: (proj1 H5); apply M.E.lt_not_eq. }
  inversion H5. }
move=> HS Hin Hlt.
have Hh := proj2 (Sorted_inv HS); inversion Hh.
inversion Hin; [by move: Hlt (proj1 H8); apply M.E.lt_not_eq|].
have HS' := proj1 (Sorted_inv HS).
by apply (IH _ HS' H8); move: H5; apply M.E.lt_trans.
Qed.

Lemma Sorted_InA_tl_lt B (ke h : M.key * B) t :
  Sorted (M.lt_key (elt:=B)) (h :: t) ->
  InA (M.eq_key_elt (elt:=B)) ke t ->
  M.lt_key h ke.
Proof.
move: h; elim t => [|h' t' IH] h; [by move=> _ Hin; inversion Hin|].
move=> HS Hin.
have Hh := proj2 (Sorted_inv HS); inversion Hh.
inversion Hin; [|by apply (M.E.lt_trans H5), IH; [apply (Sorted_inv HS)|]].
change (M.lt_key _ _) with (M.E.lt h.1 ke.1).
by move: (proj1 H8); move/mnmc_eq_seqP/eqP => ->.
Qed.

Lemma param_M_hrel_elements :
  param (M_hrel ==> seq_hrel (fun x y => M.E.eq x.1 y.1 /\ rAC x.2 y.2))
    (@M.elements A) (@M.elements C).
Proof.
apply param_abstr => m m'; rewrite !paramE => param_m.
set em := M.elements m; set em' := M.elements m'.
have: (forall k, (exists e, InA (M.eq_key_elt (elt:=A)) (k, e) em)
                 <-> (exists e', InA (M.eq_key_elt (elt:=C)) (k, e') em'))
  /\ (forall k e e', InA (M.eq_key_elt (elt:=A)) (k, e) em ->
                     InA (M.eq_key_elt (elt:=C)) (k, e') em' -> rAC e e').
{ split.
  { move=> k; split.
    { move=> [e He].
      have Hkm : M.In k m; [by exists e; apply M.elements_2|].
      elim (proj1 (proj1 param_m _) Hkm) => e' He'; exists e'.
      by apply M.elements_1. }
    move=> [e' He'].
    have Hkm' : M.In k m'; [by exists e'; apply M.elements_2|].
    elim (proj2 (proj1 param_m _) Hkm') => e He; exists e.
    by apply M.elements_1. }
  move=> k e e' He He'.
  move: (M.elements_2 He) (M.elements_2 He'); apply (proj2 param_m). }
move: (M.elements_3 m) (M.elements_3 m'); rewrite -/em -/em'.
clearbody em em'; move: {m m' param_m} em em'.
elim=> [|h t IH]; case=> [|h' t'] //.
{ move=> _ _ [Heq _]; move: (proj2 (Heq h'.1)); elim.
  { by move=> h'2; rewrite InA_nil. }
  by exists h'.2; apply InA_cons_hd; split; [apply M.E.eq_refl|]. }
{ move=> _ _ [Heq _]; move: (proj1 (Heq h.1)); elim.
  { by move=> h2; rewrite InA_nil. }
  by exists h.2; apply InA_cons_hd; split; [apply M.E.eq_refl|]. }
move=> Sht Sht' [Hht1 Hht2].
have St := proj1 (Sorted_inv Sht); have St' := proj1 (Sorted_inv Sht').
have Hhh' : M.E.eq h.1 h'.1.
{ apply MultinomOrd.intro_eq; apply/negbTE/negP.
  { move=> Hhh'1.
    have Hh1 : exists e, InA (M.eq_key_elt (elt:=A)) (h.1, e) (h :: t).
    { by exists h.2; apply InA_cons_hd; split; [apply M.E.eq_refl|]. }
    move: (proj1 (Hht1 _) Hh1) => [e' He'].
    have Hhh'1' : M.lt_key (h.1, e') h'; [by simpl|].
    by apply (Sorted_InA_not_lt_hd Sht' He'). }
  move=> Hh'h1.
  have Hh1 : exists e, InA (M.eq_key_elt (elt:=C)) (h'.1, e) (h' :: t').
  { by exists h'.2; apply InA_cons_hd; split; [apply M.E.eq_refl|]. }
  move: (proj2 (Hht1 _) Hh1) => [e He].
  have Hh'h1' : M.lt_key (h'.1, e) h; [by simpl|].
  by apply (Sorted_InA_not_lt_hd Sht He). }
simpl; split; [split; [exact Hhh'|]|apply (IH _ St St')].
{ apply (Hht2 h.1); apply InA_cons_hd.
  { by split; [apply M.E.eq_refl|]. }
  by move: Hhh' => /mnmc_eq_seqP/eqP->; split; [apply M.E.eq_refl|]. }
split=> k; specialize (Hht1 k); specialize (Hht2 k).
{ split.
  { move=> [e He].
    have Ht1 : exists e, InA (M.eq_key_elt (elt:=A)) (k, e) (h :: t).
    { by exists e; apply InA_cons_tl. }
    elim (proj1 Hht1 Ht1) => e' He'.
    inversion He'; [|by exists e'].
    move: (Sorted_InA_tl_lt Sht He); move /M.E.lt_not_eq.
    move: Hhh'; move/mnmc_eq_seqP/eqP-> => Heq; exfalso; apply Heq.
    move: (proj1 H5); move/mnmc_eq_seqP/eqP => /= ->; apply M.E.eq_refl. }
  move=> [e' He'].
  have Ht1 : exists e', InA (M.eq_key_elt (elt:=C)) (k, e') (h' :: t').
  { by exists e'; apply InA_cons_tl. }
  elim (proj2 Hht1 Ht1) => e He.
  inversion He; [|by exists e].
  move: (Sorted_InA_tl_lt Sht' He'); move /M.E.lt_not_eq.
  move: Hhh'; move/mnmc_eq_seqP/eqP<- => Heq; exfalso; apply Heq.
  move: (proj1 H5); move/mnmc_eq_seqP/eqP => /= ->; apply M.E.eq_refl. }
by move=> e e' He He'; apply Hht2; apply InA_cons_tl.
Qed.
  
Lemma param_M_hrel_fold :
  param
    ((Logic.eq ==> rAC ==> M_hrel ==> M_hrel) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.fold A _) (@M.fold C _).
Proof.
apply param_abstr => f f' param_f.
apply param_abstr => m m' param_m.
apply param_abstr => i i' param_i.
move: (param_apply param_M_hrel_elements param_m); rewrite !M.fold_1 !paramE.
move: i i' param_i; generalize (M.elements m), (M.elements m').
elim=> [|h t IHt]; case=> //=; [by move=> i i'; rewrite paramE|].
move=> h' t' i i' param_i; elim; elim=> Hh1 Hh2 Ht; move: Ht; apply IHt.
eapply param_apply; [|by apply param_i].
eapply param_apply; [|by rewrite paramE; apply Hh2].
eapply param_apply; [by apply param_f|].
move: Hh1; move/mnmc_eq_seqP/eqP<-; apply param_eq_refl.
Qed.

Global Instance ReffmpolyA_mp0_eff (n : nat) :
  param (@ReffmpolyA n) 0 (@mp0_eff C).
Proof.
eapply param_trans; [by apply composable_comp|by apply param_mp0_eff|].
apply set_param, param_M_hrel_empty.
Qed.

Global Instance ReffmpolyA_mp1_eff (n : nat) :
  param (@ReffmpolyA n) 1 (mp1_eff (n:=n)).
Proof.
eapply param_trans; [by apply composable_comp|by apply param_mp1_eff|].
apply set_param; rewrite /mp1_eff; eapply param_apply; [|by tc].
by eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl].
Qed.

Global Instance ReffmpolyA_mpvar_eff (n : nat) :
  param (rAC ==> Logic.eq ==> Rord ==> @ReffmpolyA n)
    mpvar (mpvar_eff (n:=n)).
Proof.
eapply param_trans; [|by apply param_mpvar_eff|].
{ do 2 apply composable_imply_id1.
  rewrite -{2}(comp_eqr Rord); apply composable_imply, composable_comp. }
apply set_param; rewrite /mpvar_eff.
apply param_abstr => c c' param_c.
apply param_abstr => d d'; rewrite paramE => <-.
apply param_abstr => i i'; rewrite paramE => <-.
eapply param_apply; [|by apply param_c].
eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl].
Qed.

Global Instance ReffmpolyA_mpolyC_eff (n : nat) :
  param (rAC ==> ReffmpolyA) (@mpolyC n A) (mpolyC_eff (n:=n)).
Proof.
eapply (param_trans (rAB:=(Logic.eq ==> Reffmpoly)%rel)
                    (rBC:=(rAC ==> M_hrel)%rel)); [|by apply param_mpolyC_eff|].
{ rewrite -{2}(comp_eql rAC); apply composable_imply, composable_comp. }
apply set_param; rewrite /mpolyC_eff.
apply param_abstr => c c' param_c.
eapply param_apply; [|by apply param_c].
eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl].
Qed.

Global Instance ReffmpolyA_mpolyX_eff (n : nat) :
  param (Rseqmultinom ==> ReffmpolyA) (@mpolyX n A) mpolyX_eff.
Proof.
eapply param_trans; [|by apply param_mpolyX_eff|].
{ rewrite -{2}(comp_eqr Rseqmultinom).
  apply composable_imply, composable_comp. }
apply set_param; rewrite /mpolyX_eff.
apply param_abstr => m m' param_m.
eapply param_apply; [|by tc].
eapply param_apply; [apply param_M_hrel_singleton|apply param_m].
Qed.

Lemma param_M_hrel_mpoly_scale_eff :
  param (rAC ==> M_hrel ==> M_hrel)
    (@mpoly_scale_eff A *%R) mpoly_scale_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_scale_eff (n : nat) :
  param (rAC ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_scale n A) mpoly_scale_eff.
Proof.
Admitted. (* Érik *)

Lemma param_M_hrel_mpoly_add_eff :
  param (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_add_eff A +%R) mpoly_add_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_add_eff (n : nat) :
  param (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_add n A) mpoly_add_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_sub_eff (n : nat) :
  param (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_sub A n) mpoly_sub_eff.
Proof.
Admitted. (* Érik *)

Lemma param_M_hrel_mpoly_mul_eff :
  param (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_mul_eff A +%R *%R) mpoly_mul_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_mul_eff (n : nat) :
  param (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_mul n A) mpoly_mul_eff.
Proof.
Admitted. (* Érik *)

Lemma param_M_hrel_mpoly_exp_eff n :
  param (M_hrel ==> Logic.eq ==> M_hrel)
    (@mpoly_exp_eff _ 1%R +%R *%R n) (mpoly_exp_eff (n:=n)).
Proof.
rewrite /mpoly_exp_eff.
apply param_abstr => m m' param_m.
apply param_abstr => k k'; rewrite paramE => <- {k'}.
elim k => [|k' IHk] /=.
{ rewrite /mp1_eff; eapply param_apply; [|by tc].
  eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl]. }
case_eq k' => // _ <-; eapply param_apply; [|by apply IHk].
eapply param_apply; [|by apply param_m].
apply param_M_hrel_mpoly_mul_eff.
Qed.

Global Instance ReffmpolyA_mpoly_exp_eff (n : nat) :
  param (ReffmpolyA ==> Logic.eq ==> ReffmpolyA)
    (@mpoly_exp A n) (mpoly_exp_eff (n:=n)).
Proof.
eapply param_trans; [|by apply param_mpoly_exp_eff|].
{ apply composable_imply, composable_imply_id1, composable_comp. }
apply set_param, param_M_hrel_mpoly_exp_eff.
Qed.

Definition seq_ReffmpolyA n k := (@seq_Reffmpoly A n k \o seq_hrel M_hrel)%rel.

Lemma param_M_hrel_comp_monomial_eff n :
  param (Logic.eq ==> rAC ==> seq_hrel M_hrel ==> M_hrel)
    (@comp_monomial_eff A 1%R +%R *%R n) (comp_monomial_eff (n:=n)).
Proof.
apply param_abstr => m m'; rewrite paramE => <-.
apply param_abstr => c c' param_c.
apply param_abstr => lq lq' param_lq.
rewrite /comp_monomial_eff.
eapply param_apply.
{ eapply param_apply; [apply param_M_hrel_mpoly_scale_eff|apply param_c]. }
move: lq lq' param_lq m.
elim=> [|hlq tlq IH]; case=> [|hlq' tlq']; rewrite paramE //.
{ move=> _ m /=; rewrite /mp1_eff; eapply param_apply; [|by tc].
  eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl]. }
move=> [Hhlq Htlq]; case=> [|hm tm] /=.
{ rewrite /mp1_eff; eapply param_apply; [|by tc].
  eapply param_apply; [apply param_M_hrel_singleton|apply param_eq_refl]. }
eapply param_apply; [eapply param_apply|].
{ by apply param_M_hrel_mpoly_mul_eff. }
{ eapply param_apply; [|by apply param_eq_refl].
  eapply param_apply; [|by apply (trivial_param Hhlq)].
  apply param_M_hrel_mpoly_exp_eff. }
by apply IH; rewrite paramE.
Qed.
  
Global Instance ReffmpolyA_comp_mpoly_eff (n k : nat) :
  param (seq_ReffmpolyA (k:=k) ==> ReffmpolyA ==> ReffmpolyA)
    (comp_mpoly (k:=n)) (comp_mpoly_eff (n:=n)).
Proof.
eapply (param_trans
          (rAB:=(@seq_Reffmpoly _ n k ==> Reffmpoly ==> Reffmpoly)%rel));
  [|by apply param_comp_mpoly_eff|].
{ apply composable_imply, composable_imply, composable_comp. }
apply set_param; rewrite /comp_mpoly_eff.
apply param_abstr => lq lq' param_lq.
apply param_abstr => p p' param_p.
eapply param_apply; [|by apply param_M_hrel_empty].
eapply param_apply; [|by apply param_p].
eapply param_apply; [by apply param_M_hrel_fold|].
apply param_abstr => m m' param_m.
apply param_abstr => c c' param_c.
eapply param_apply; [by apply param_M_hrel_mpoly_add_eff|].
eapply param_apply; [|by apply param_lq].
eapply param_apply; [|by apply param_c].
eapply param_apply; [apply param_M_hrel_comp_monomial_eff|apply param_m].
Qed.

End effmpoly_parametricity.
