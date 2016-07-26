Require Import ZArith FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype ssralg bigop.
(* tests with multipolys from
   git clone https://github.com/math-comp/multinomials.git *)
From SsrMultinomials Require Import mpoly freeg.
From CoqEAL Require Import hrel.
From CoqEAL Require Import refinements.
From CoqEAL Require Import param binord seqmx (* for zipwith and eq_seq *).
Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Arguments refines A%type B%type R%rel _ _.  (* TODO: il y a un preoblème de scope sur refine *)

Definition iffT (A B : Type) : Type := ((A -> B) * (B -> A))%type.
Infix "<=>" := iffT : type_scope.

Hint Resolve list_R_nil_R.

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

Definition mnmd_seq {n} (i : nat) (d : nat) :=
  nseq i 0%N ++ [:: d] ++ nseq (n - i - 1) 0%N.

(** Multiplication of multinomials *)
Definition mnm_add_seq m1 m2 := map2 addn m1 m2.

Definition mdeg_eff := foldl addn 0%N.

Fixpoint mnmc_lt_seq_aux (s1 s2 : seq nat) {struct s1} : bool :=
  match s1, s2 with
    | [::], [::] => false
    | [::], _ => true
    | x1 :: s1', [::] => false
    | x1 :: s1', x2 :: s2' =>
      (x1 < x2)%N || (x1 == x2)%N && mnmc_lt_seq_aux s1' s2'
  end.
Definition mnmc_lt_seq (s1 s2 : seq nat) : bool :=
  mnmc_lt_seq_aux (mdeg_eff s1 :: s1) (mdeg_eff s2 :: s2).

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
rewrite /mnmc_lt_seq /=.
case Hlt : (_ < _)=>//=; case Hlt' : (_ < _)=>//=; move: Hlt Hlt'.
rewrite !ltnNge !negb_false_iff !eqn_leq =>->->/=.
elim: x y => [|hx tx Hind]; case=> // hy ty.
rewrite /lt /=; case (ltnP hx hy) => //= Hxy; case (ltnP hy hx) => //= Hyx.
have Exy : hx == hy; [by apply/eqP /anti_leq; rewrite Hyx|].
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
move=> x y z; rewrite /lt /mnmc_lt_seq.
set x' := _ :: x; set y' := _ :: y; set z' := _ :: z.
clearbody x' y' z'; clear x y z; move: x' y' z'.
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
move=> x y; rewrite /lt /mnmc_lt_seq /=; move/orP; elim.
{ move=> Hlt Heq; move: Heq Hlt; move/mnmc_eq_seqP/eqP->.
  by rewrite ltnn. }
move/andP; case=>_.
move=> Hlt /mnmc_eq_seqP/eqP Heq; move: Hlt; rewrite Heq.
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

Definition list_of_mpoly {T : ringType} {n} (p : {mpoly T[n]}) :
  seq ('X_{1..n} * T) := [seq (m, p@_m) | m <- path.sort mnmc_le (msupp p)].

(* TODO: remove, not used
Definition effmpoly_of_list : forall T, seq (seqmultinom * T) -> effmpoly T :=
  MProps.of_list. *)

Context {T : Type} `{!zero_of T, !one_of T}.
Context `{!add_of T, !opp_of T, !sub_of T, !mul_of T, !eq_of T}.
Context {n : nat}.

Definition list_of_mpoly_eff (p : effmpoly T) : seq (seqmultinom * T) :=
  [seq mc <- M.elements p | negb (mc.2 == 0)%C].

Definition mp0_eff : effmpoly T := M.empty.

Definition mp1_eff  := MProps.singleton (@mnm0_seq n) (1%C : T).

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

Derive Inversion inv_InA with
  (forall (A : Type) (eqA : A -> A -> Prop) (x : A) (s : seq A), @InA A eqA x s) Sort Prop.

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
  `{ref_mm' : !refines Rseqmultinom m m'} :
  size m' = n.
Proof.
move: ref_mm'.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf _.
exact/eqP.
Qed.

Lemma refines_nth_def
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) x0 :
  refines Rseqmultinom m m' -> nth x0 m' i = m i.
Proof.
move=> rMN; move: (rMN).
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf [] <-.
by rewrite multinomE /= (tnth_nth x0).
Qed.

Lemma refines_nth
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) :
  refines Rseqmultinom m m' -> nth 0%N m' i = m i.
Proof. exact: refines_nth_def. Qed.

Lemma refines_seqmultinomP
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom) :
  size m' = n ->
  (forall i : 'I_n, nth 0%N m' i = m i) ->
  refines Rseqmultinom m m'.
Proof.
move=> eq_sz eq_nth.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb => [prf|].
  congr Some; apply: val_inj; simpl.
  by apply: eq_from_tnth => i; rewrite (tnth_nth 0%N) /= eq_nth.
by rewrite eq_sz eqxx.
Qed.

Lemma refines_seqmultinom_of_multinom (n : nat) (m : 'X_{1..n}) :
  refines Rseqmultinom m (seqmultinom_of_multinom m).
Proof.
by rewrite refinesE /Rseqmultinom /ofun_hrel seqmultinom_of_multinomK.
Qed.

Lemma refines_multinom_of_seqmultinom_val (n : nat) (m : seqmultinom) :
  size m == n ->
  refines Rseqmultinom (multinom_of_seqmultinom_val n m) m.
Proof.
move=> Hsz.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom_val /ofun_hrel.
case_eq (multinom_of_seqmultinom n m) => //.
by rewrite /multinom_of_seqmultinom; case sumb => //; rewrite Hsz.
Qed.

Lemma refines_mnm0 n : refines Rseqmultinom (@mnm0 n) (@mnm0_seq n).
Proof.
apply refines_seqmultinomP.
  by rewrite size_nseq.
move=> i; rewrite nth_nseq if_same multinomE (tnth_nth 0%N) nth_map //=.
by rewrite size_enum_ord.
Qed.

Lemma refines_mnmd {n1 n2} {rn : nat_R n1 n2} :
  refines (Rord rn ==> eq ==> Rseqmultinom) (@mnmd n1) (@mnmd_seq n2).
Proof.
(* First, ensure that n1 > 0, else 'I_n1 would be empty *)
case: rn => {n1 n2} [|n1 n2 rn]; first by rewrite refinesE => -[].
eapply refines_abstr => i i' ref_i.
eapply refines_abstr => j j' ref_j.
rewrite -(refines_eq ref_j).
rewrite refinesE in ref_i.
have->: i' = i :> nat by apply: refinesP; tc.
apply: refines_seqmultinomP.
  rewrite /mnmd_seq !(size_cat,size_nseq) /= -subnDA addnA addn1 subnKC //.
    by congr S; symmetry; apply: nat_R_eq.
  by rewrite -(nat_R_eq rn).
move=> k.
rewrite /mnmd_seq /mnmd multinomE (tnth_nth 0%N) /=.
rewrite !(nth_cat,nth_nseq).
rewrite (nth_map ord0); last by rewrite size_enum_ord.
case: ifP.
  rewrite if_same size_nseq nth_enum_ord //.
  move=> Hic; rewrite ifF //.
  apply/negP; move/eqP => Keq.
  by rewrite -Keq ltnn in Hic.
move/negbT; rewrite size_nseq -ltnNge ltnS => Hi.
rewrite nth_enum_ord //.
case: ifP; first by move/eqP->; rewrite subnn.
move/negbT/eqP => Hneq.
case: (ltnP i k) => Hci.
  by rewrite -(@prednK (k - i)) ?subn_gt0 //= nth_nseq if_same.
by exfalso; apply/Hneq/anti_leq; rewrite Hi.
Qed.

Global Instance refines_mnm_add n :
  refines (Rseqmultinom ==> Rseqmultinom ==> Rseqmultinom)
  (@mnm_add n) mnm_add_seq.
Proof.
apply refines_abstr => mnm1 mnm1' refines_mnm1.
apply refines_abstr => mnm2 mnm2' refines_mnm2.
apply/refines_seqmultinomP.
  by rewrite /mnm_add_seq size_map2 !refines_size minnn.
move=> i; rewrite /mnm_add_seq (nth_map2 _ (da := O) (db := O)) //; last first.
  by rewrite !refines_size.
by rewrite mnmDE !refines_nth.
Qed.

Global Instance refines_mnmc_lt n :
  refines (Rseqmultinom ==> Rseqmultinom ==> Logic.eq)
    (@mnmc_lt n) (mnmc_lt_seq).
Proof.
Admitted.  (* TODO: after migration *)

(** Multivariate polynomials *)

Definition mpoly_of_effmpoly (T : ringType) n (p' : effmpoly T) : option (mpoly n T) :=
  if MProps.for_all (fun k _ => size k == n)%N p' then
    Some [mpoly [freeg [seq (a.2, multinom_of_seqmultinom_val n a.1) |
                        a <- M.elements p']]]
  else None.

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
inversion Hnd as [x|h' t' H1 H2].
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
  refines Rseqmultinom x x' ->
  refines Rseqmultinom y y' ->
  (x == y) = (x' == y').
Proof.
move=> Hx Hy; apply/idP/idP => H.
{ have Sx' := @refines_size _ _ _ Hx.
  have Sy' := @refines_size _ _ _ Hy.
  apply/eqP.
  move: H Hy Hx; rewrite refinesE /Rseqmultinom /ofun_hrel; move/eqP=>-><-.
  by apply multinom_of_seqmultinom_inj. }
apply/eqP; move: H Hx Hy.
rewrite refinesE /Rseqmultinom /ofun_hrel; move/eqP=>->->.
by move=> H; inversion H.
Qed.

Lemma refines_size_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T)
  `{ref_pp' : !refines Reffmpoly p p'} :
  forall m, M.In m p' -> size m == n.
Proof.
move: ref_pp'.
rewrite refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
set t := MProps.for_all _ _; case_eq t => //.
rewrite /t (MProps.for_all_iff _); [|by move=> m _ /mnmc_eq_seqP /eqP <-].
by move=> H _ m [e Hme]; apply (H m e).
Qed.

Lemma refines_find_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T) :
  refines Reffmpoly p p' ->
  forall m m', refines Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p').
Proof.
rewrite !refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
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
  (forall m m', refines Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p')) ->
  refines Reffmpoly p p'.
Proof.
move=> eq_sz eq_monom.
assert (Hsz : MProps.for_all (fun (k : M.key) (_ : T) => size k == n) p').
{ rewrite /is_true (MProps.for_all_iff _) => k e Hke.
  { by apply eq_sz; exists e. }
  by move=> _ _ _; move: Hke; move/mnmc_eq_seqP/eqP ->. }
rewrite refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel ifT //; f_equal.
apply mpolyP => m.
pose m' := seqmultinom_of_multinom m.
have Hm' : refines Rseqmultinom m m'.
  by rewrite refinesE; apply seqmultinom_of_multinomK.
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
Instance : zero_of T := 0%R.
Instance : one_of T := 1%R.
Instance : add_of T := +%R.
Instance : opp_of T := -%R.
Instance : sub_of T := fun x y => (x - y)%R.
Instance mul_instR : mul_of T := *%R.
Instance : eq_of T := fun x y => x == y.

Lemma refines_seq_multinom_coeff n (s : seq ('X_{1..n} * T)) s' :
  all (fun mc => size mc.1 == n) s' ->
  s = [seq (multinom_of_seqmultinom_val n mc.1, mc.2) |mc <- s'] ->
  refines (list_R (fun x y => refines Rseqmultinom x.1 y.1 * (x.2 = y.2))%type) s s'.
Proof.
rewrite refinesE.
elim: s' s=> [|h' t' IH]; case=> [//|h t] //=.
(* by move=> *; apply: list_R_nil_R.
   (* OK thanks to [Hint Resolve list_R_nil_R.] *)
*)
case/andP => Hsh Hst [Hh Ht]; constructor.
{ move: Hh; rewrite {1}(surjective_pairing h)=>[] [-> ->]; split=>//.
  by apply refines_multinom_of_seqmultinom_val. }
by apply IH.
Qed.

Lemma in_InA_iff mc l : mc \in l <-> InA (M.eq_key_elt (elt:=T)) mc l.
Proof.
elim l=> [|h t IH]; [by split=>// H; inversion H|].
rewrite in_cons; split.
{ move=>/orP []; [by move/eqP->; left; rewrite eq_key_elt_eq|].
  by move=> Hmc; right; apply IH. }
move=> H; inversion H as [mc' l' Hmc [Hmc' Hl']|mc' l' Hmc [Hmc' Hl']].
{ by apply/orP; left; apply/eqP; apply eq_key_elt_eq. }
by apply/orP; right; rewrite IH.
Qed.

Lemma uniq_map_filter (T' T'' : eqType) (s : seq T') C (E : T' -> T'') :
  uniq [seq E i | i <- s] -> uniq [seq E i | i <- s & C i].
Proof.
elim s=> [//|h t IH] /= /andP [] Hh Ht.
case (C h)=>/=; [|by apply IH]; apply/andP; split; [|by apply IH].
apply/negP=>H; move/negP in Hh; apply Hh; apply/mapP.
move: H; move/mapP=> [] x Hx Hx'; exists x=>//; move: Hx.
by rewrite mem_filter=>/andP [].
Qed.

Global Instance refines_list_of_mpoly_eff n :
  refines (Reffmpoly ==>
    list_R (fun x y => refines Rseqmultinom x.1 y.1 * (x.2 = y.2))%type)
    (@list_of_mpoly T n) list_of_mpoly_eff.
Proof.
apply refines_abstr => p p' rp.
rewrite /list_of_mpoly_eff.
have Hs : all (fun mc : seq nat * T => size mc.1 == n)
            [seq mc <- M.elements p' | ~~ (mc.2 == 0)%C].
{ apply/allP=> mc; rewrite mem_filter; move/andP=> [] _ Hmc.
  apply (refines_size_mpoly (ref_pp' := rp)).
  rewrite MFacts.elements_in_iff; exists mc.2.
  by rewrite -in_InA_iff -surjective_pairing. }
apply refines_seq_multinom_coeff=> //; rewrite /list_of_mpoly.
suff : path.sort mnmc_le (msupp p)
  = [seq multinom_of_seqmultinom_val n mc.1 |
     mc <- M.elements p' & ~~ (mc.2 == 0)].
{ set l := path.sort _ _; set l' := filter _ _.
  move=> H; apply (eq_from_nth (x0:=(0%MM, 0))).
  { by rewrite size_map H !size_map. }
  move=> i; rewrite size_map=> Hi.
  have Hi' : i < size l'; [by move: Hi; rewrite H size_map|].
  rewrite (nth_map 0%MM) // H !(nth_map (@mnm0_seq n, 0)) //; f_equal.
  set mc := nth _ _ _.
  erewrite (refines_find_mpoly (p' := p') (m':=mc.1) rp). (* erewrite?! *)
  { rewrite (M.find_1 (e:=mc.2)) // MFacts.elements_mapsto_iff -in_InA_iff.
    rewrite -surjective_pairing.
    suff: mc \in l'; [by rewrite mem_filter=>/andP []|by apply mem_nth]. }
  apply refines_multinom_of_seqmultinom_val; move: Hs; move/allP; apply.
  rewrite -/l' /mc; apply (mem_nth (mnm0_seq, 0) Hi'). }
apply (path.eq_sorted (leT:=mnmc_le)).
{ apply lemc_trans. }
{ apply lemc_antisym. }
{ apply path.sort_sorted, lemc_total. }
{ have Se := M.elements_3 p'.
  pose lef := fun x y : _ * T => mnmc_lt_seq x.1 y.1.
  pose l := [seq mc <- M.elements p' | mc.2 != 0]; rewrite -/l.
  have : path.sorted lef l.
  { apply path.sorted_filter; [by move=> x y z; apply M.E.lt_trans|].
    clear l; move: Se; set l := _ p'; elim l=> [//|h t IH].
    move=> H; inversion H as [|h' t' Ht Hht [Hh' Ht']]; move {H h' t' Hh' Ht'}.
    rewrite /path.sorted; case_eq t=>[//|h' t'] Ht' /=; apply /andP; split.
    { by rewrite Ht' in Hht; inversion Hht. }
    by rewrite -/(path.sorted _ (h' :: t')) -Ht'; apply IH. }
  case_eq l=> [//|h t Hl] /= /(path.pathP (@mnm0_seq n, 0)) H.
  apply/(path.pathP 0%MM)=> i; rewrite size_map=> Hi.
  rewrite /mnmc_le poset.lex_eqVlt -/(mnmc_lt _ _); apply/orP; right.
  rewrite (nth_map (@mnm0_seq n, 0)) //; move/allP in Hs.
  move: (H _ Hi); rewrite /lef/is_true=><-; apply refinesP.
  eapply refines_apply; [eapply refines_apply; [by apply refines_mnmc_lt|]|].
  { case: i Hi=> /= [|i'] Hi; [|apply ltnW in Hi].
    { apply refines_multinom_of_seqmultinom_val, Hs.
      by rewrite -/l Hl in_cons eqxx. }
    rewrite (nth_map (@mnm0_seq n, 0)) //.
    apply refines_multinom_of_seqmultinom_val, Hs.
    by rewrite -/l Hl in_cons; apply/orP; right; rewrite mem_nth. }
  apply refines_multinom_of_seqmultinom_val, Hs.
  by rewrite -/l Hl in_cons; apply/orP; right; rewrite mem_nth. }
apply uniq_perm_eq.
{ rewrite path.sort_uniq; apply msupp_uniq. }
{ change (fun _ => multinom_of_seqmultinom_val _ _)
  with ((fun m => multinom_of_seqmultinom_val n m) \o (fst (B:=T))).
  rewrite map_comp map_inj_in_uniq.
  { apply (@uniq_map_filter _ _ (M.elements p')).
    apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
  move=> m m' Hm Hm'; apply multinom_of_seqmultinom_val_inj.
  { by move/allP in Hs; move: Hm=>/mapP [x Hx] ->; apply/eqP /Hs. }
  by move/allP in Hs; move: Hm'=>/mapP [x Hx] ->; apply/eqP /Hs. }
move=> m; rewrite path.mem_sort; apply/idP/idP.
{ pose m' := seqmultinom_of_multinom m.
  rewrite mcoeff_msupp=>Hin; apply/mapP; exists (m', p@_m).
  { rewrite mem_filter /= Hin /= in_InA_iff; apply M.elements_1, M.find_2.
    move: Hin; erewrite (@refines_find_mpoly _ _ _ _ rp _ m').
    { by case (M.find _ _)=>//; rewrite eqxx. }
    apply refines_seqmultinom_of_multinom. }
  by rewrite /= /m' /multinom_of_seqmultinom_val seqmultinom_of_multinomK. }
move/mapP=> [] mc; rewrite mem_filter=>/andP [] Hmc2; rewrite in_InA_iff.
rewrite {1}(surjective_pairing mc) -MFacts.elements_mapsto_iff.
rewrite MFacts.find_mapsto_iff mcoeff_msupp=> Hmc1 ->.
erewrite (@refines_find_mpoly _ _ _ _ rp _ mc.1); [by rewrite Hmc1|].
apply refines_multinom_of_seqmultinom_val; move/allP in Hs; apply Hs.
rewrite mem_filter Hmc2 /= in_InA_iff (surjective_pairing mc).
by rewrite -MFacts.elements_mapsto_iff; apply M.find_2.
Qed.

Global Instance refines_mp0_eff n : refines (@Reffmpoly T n) 0%R mp0_eff.
Proof.
apply: refines_effmpolyP.
- by move=> m /MProps.F.empty_in_iff Hm.
- by move=> m m' refines_m; rewrite MFacts.empty_o mcoeff0.
Qed.

Global Instance refines_mp1_eff n : refines (@Reffmpoly T n) 1%R (mp1_eff (n := n)).
Proof.
apply refines_effmpolyP.
- rewrite /mp1_eff => k /MProps.singleton_in_iff/mnmc_eq_seqP/eqP ->.
  by rewrite size_nseq.
- move=> m m' Hm; rewrite mcoeff1 MProps.F.add_o.
  have H0 := refines_mnm0 n.
  rewrite (Rseqmultinom_eq Hm H0).
  case: M.E.eq_dec => [EQ|nEQ].
  + by move/mnmc_eq_seqP/eqP: EQ <-; rewrite eqxx.
  + by rewrite eq_sym; move/mnmc_eq_seqP/negbTE: nEQ ->.
Qed.

Global Instance refines_mpvar_eff {n1 n2} {rn : nat_R n1 n2} :
  refines (Logic.eq ==> Logic.eq ==> Rord rn ==> Reffmpoly (T := T) (n := n1))
  mpvar (mpvar_eff (n := n2)).
Proof.
case: rn => {n1 n2} [|n1 n2 rn].
  by rewrite refinesE; move=> p p' Hp q q' Hq [] i' Hi.
apply refines_abstr => c c' refines_c; apply refines_abstr => d d' refines_d.
rewrite !refinesE in refines_c, refines_d; rewrite -{}refines_c -{}refines_d {c' d'}.
apply refines_abstr => i i' ref_i.
rewrite refinesE in ref_i.
have->: i' = i :> nat by apply refinesP; tc.
assert (Hmnmd : refines Rseqmultinom (mnmd i d) (@mnmd_seq n2.+1 i d)).
{ eapply refines_apply; [eapply refines_apply|].
  Fail eapply refines_mnmd.
  admit. admit. admit. }
apply refines_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  move/(@MProps.singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refines_size _ (mnmd i d)). }
move=> m m' Hm; rewrite mcoeffZ mcoeffX.
rewrite (Rseqmultinom_eq Hmnmd Hm) eq_sym.
case_eq (m' == (@mnmd_seq n2.+1 i d)).
{ move/eqP => Hm'; rewrite Hm'.
  rewrite MProps.F.add_eq_o; last exact: M.E.eq_refl.
  by rewrite GRing.mulr1. }
move=> Hm'; rewrite MProps.F.add_neq_o /=; [by rewrite GRing.mulr0|].
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Admitted.

Arguments mpolyC {n R} c.
Global Instance refines_mpolyC_eff n :
  refines (Logic.eq ==> Reffmpoly (T := T) (n := n))
  mpolyC (mpolyC_eff (n := n)).
Proof.
apply refines_abstr => c c' refines_c.
rewrite !refinesE in refines_c; rewrite -{}refines_c {c'}.
apply refines_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  by move/(@MProps.singleton_mapsto T)=> [-> _]; rewrite size_nseq eqxx. }
move=> m m' Hm; rewrite mcoeffC.
have Hm0 := @refines_mnm0 n.
rewrite (Rseqmultinom_eq Hm Hm0).
case_eq (m' == @mnm0_seq n).
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite MProps.F.add_eq_o; [rewrite GRing.mulr1|apply M.E.eq_refl]. }
move=> Hm'; rewrite MProps.F.add_neq_o /=; [by rewrite GRing.mulr0|].
by apply/mnmc_eq_seqP; move: Hm'; rewrite eq_sym =>->.
Qed.

Arguments mpolyX {n R} m.
Global Instance refines_mpolyX_eff n :
  refines (Rseqmultinom ==> Reffmpoly (T := T) (n := n))
  mpolyX mpolyX_eff.
Proof.
apply refines_abstr => m m' refines_m.
apply refines_effmpolyP.
{ move=> m'' [e Hme]; move: Hme; rewrite /mpolyX_eff.
  move/(@MProps.singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refines_size _ m). }
move=> m'' m''' Hm; rewrite mcoeffX.
rewrite (Rseqmultinom_eq refines_m Hm) eq_sym.
case_eq (m''' == m').
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite MProps.F.add_eq_o /=; [|by apply M.E.eq_refl]. }
move=> Hm'; rewrite MProps.F.add_neq_o //=.
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Qed.

Lemma MapsTo_mcoeff {n} m m' p p' a :
  refines (Reffmpoly (T := T) (n := n)) p p' ->
  refines Rseqmultinom m m' ->
  M.MapsTo m' a p' -> p@_m = a.
(* the converse may be wrong if [a = 0] *)
Proof.
move=> Hp Hm HMT.
move/MFacts.find_mapsto_iff in HMT.
by rewrite (refines_find_mpoly Hp Hm) /odflt /oapp HMT.
Qed.

Lemma not_In_mcoeff {n} m m' p p' :
  refines (Reffmpoly (T := T) (n := n)) p p' ->
  refines Rseqmultinom m m' ->
  ~ M.In m' p' -> p@_m = 0.
Proof.
move=> Hp Hm Hin.
rewrite (refines_find_mpoly Hp Hm).
by move/MFacts.not_find_in_iff: Hin ->.
Qed.

Arguments mpoly_scale {n R} c p.
Global Instance refines_mpoly_scale_eff n :
  refines (Logic.eq ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_scale mpoly_scale_eff.
Proof.
apply refines_abstr => c c' refines_c.
apply refines_abstr => p p' refines_p.
rewrite /mpoly_scale_eff; apply: refines_effmpolyP.
{ move=> m /M.map_2 Hm; exact: refines_size_mpoly refines_p _ _. }
move=> m m' refines_m; rewrite mcoeffZ.
case Es: (M.find _ _) => [s|] /=.
{ have /MFacts.find_mapsto_iff/MFacts.map_mapsto_iff [a [-> Ha2 /=]] := Es.
  rewrite (refines_eq refines_c).
  congr *%R.
  apply: MapsTo_mcoeff refines_p refines_m Ha2. }
move/MFacts.not_find_in_iff in Es.
suff->: p@_m = 0 by rewrite GRing.mulr0.
apply: not_In_mcoeff refines_p refines_m _.
move=> K; apply: Es.
exact/MFacts.map_in_iff.
Qed.

Arguments mpoly_add {n R} p q.
Global Instance refines_mpoly_add_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_add mpoly_add_eff.
Proof.
apply refines_abstr => p p' refines_p.
apply refines_abstr => q q' refines_q.
rewrite /mpoly_add_eff.
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
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff refines_p Hm Ep) (MapsTo_mcoeff refines_q Hm Eq).
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff refines_p Hm Ep) (not_In_mcoeff refines_q Hm Eq)
  GRing.addr0.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff refines_p Hm Ep) (MapsTo_mcoeff refines_q Hm Eq)
  GRing.add0r.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff refines_p Hm Ep) (not_In_mcoeff refines_q Hm Eq)
  GRing.addr0.
Qed.

Definition mpoly_sub {n} (p : {mpoly T[n]}) q := mpoly_add p (mpoly_opp q).

Global Instance refines_mpoly_sub_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_sub mpoly_sub_eff.
apply refines_abstr => p p' refines_p.
apply refines_abstr => q q' refines_q.
rewrite /mpoly_add_eff.
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
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff refines_p Hm Ep) (MapsTo_mcoeff refines_q Hm Eq).
- move/MFacts.find_mapsto_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff refines_p Hm Ep) (not_In_mcoeff refines_q Hm Eq)
  GRing.subr0.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff refines_p Hm Ep) (MapsTo_mcoeff refines_q Hm Eq)
  GRing.sub0r.
- move/MFacts.not_find_in_iff in Ep;
  move/MFacts.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff refines_p Hm Ep) (not_In_mcoeff refines_q Hm Eq)
  GRing.subr0.
Qed.

Lemma rem_mpoly_eff n (q p' : effmpoly T) (k' : seqmultinom) (e : T)
  (p : mpoly n T) (k : 'X_{1..n}) :
  ~ M.In k' q -> MProps.Add k' e q p' -> refines Reffmpoly p p' ->
  refines Rseqmultinom k k' -> refines Reffmpoly (p - p@_k *: 'X_[k]) q.
Proof.
move=> Hin Hadd Hp Hk.
apply refines_effmpolyP.
{ move=> m'' [c' Hc']; move: (Hadd m''); rewrite MFacts.add_o.
  case M.E.eq_dec.
  { move/mnmc_eq_seqP/eqP <-; rewrite -MFacts.find_mapsto_iff => Hm.
    by apply (@refines_size_mpoly _ _ _ _ (Hp)); exists e. }
  rewrite (proj1 (MFacts.find_mapsto_iff q m'' c')) // => _ H.
  apply (@refines_size_mpoly _ _ _ _ (Hp)).
  by exists c'; move: H; rewrite -MFacts.find_mapsto_iff. }
move=> mm mm' refines_mm; move: (Hadd mm'); rewrite MFacts.add_o.
rewrite mcoeffB mcoeffZ mcoeffX.
case M.E.eq_dec.
{ move/mnmc_eq_seqP/eqP => Hmm'; rewrite -Hmm'.
  have Hmm : k = mm.
  { by apply/eqP; rewrite (Rseqmultinom_eq Hk refines_mm); apply/eqP. }
  rewrite (proj1 (MFacts.not_find_in_iff _ _) Hin) -Hmm eqxx GRing.mulr1.
  by rewrite (refines_find_mpoly Hp Hk) => ->; rewrite GRing.subrr. }
move=> Hmm' <-.
have Hmm : ~ k = mm.
{ move=> Hmmm; apply/Hmm'/mnmc_eq_seqP.
  by rewrite -(Rseqmultinom_eq Hk refines_mm); apply/eqP. }
rewrite (refines_find_mpoly Hp refines_mm).
by have ->: (k == mm = false); [apply/eqP|rewrite GRing.mulr0 GRing.subr0].
Qed.

Lemma refines_mpoly_sum_eff n k f f' (p : mpoly k T) p' :
  (forall m, f m 0 = 0) ->
  refines (Rseqmultinom ==> Logic.eq ==> Reffmpoly (T:=T) (n:=n)) f f' ->
  refines Reffmpoly p p' ->
  refines Reffmpoly (\sum_(m <- msupp p) f m p@_m)
                  (M.fold (fun m c => mpoly_add_eff (f' m c)) p' mp0_eff).
Proof.
move=> Hf refines_f; move: p.
apply MProps.fold_rec.
{ move=> q' Eq' q Hq.
  suff -> : q = 0; [by rewrite msupp0 big_nil; apply refines_mp0_eff|].
  apply /mpolyP => m.
  rewrite (refines_find_mpoly Hq (refines_seqmultinom_of_multinom m)).
  rewrite mcoeff0; case_eq (M.find (seqmultinom_of_multinom m) q') => [s|->]//.
  rewrite -MFacts.find_mapsto_iff MFacts.elements_mapsto_iff.
  by rewrite -in_InA_eq_key_elt_iff (proj1 (MProps.elements_Empty _ ) Eq'). }
move=> m' c p'' q q' Hp'' Hq Hq' IH p Hp.
pose m := multinom_of_seqmultinom_val k m'; pose cm := c *: 'X_[m].
have refines_m : refines Rseqmultinom m m'.
{ apply refines_multinom_of_seqmultinom_val.
  move: (Hq' m'); rewrite MFacts.add_eq_o; [|by apply/mnmc_eq_seqP]; move=> Hm'.
  apply (@refines_size_mpoly _ _ _ _ Hp).
  by exists c; apply M.find_2. }
have Hc : p@_m = c.
{ rewrite (refines_find_mpoly Hp refines_m) (Hq' m') MFacts.add_eq_o //.
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
eapply refines_apply.
{ eapply refines_apply; [by apply refines_mpoly_add_eff|].
  eapply refines_apply; [|by apply trivial_refines; symmetry].
  eapply refines_apply; [eapply refines_f|apply refines_m]. }
apply IH.
rewrite /pmcm /cm -Hc.
apply (rem_mpoly_eff Hq Hq' Hp refines_m).
Qed.

Lemma Rseqmultinom_iff {n} :
  (refines (Rseqmultinom (n := n)) <=> @eq (seq nat))%rel.
Proof.
split => l l' Hmain.
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

Lemma refines_Madd_mnm_add {n} (m : 'X_{1.. n}) m' (c : T) p p' :
  refines Rseqmultinom m m' ->
  refines Reffmpoly p p' ->
  m \notin msupp p ->
  refines Reffmpoly (+%R (c *: 'X_[m]) p) (M.add m' c p').
Proof.
move=> Hm Hp Hnotin.
apply: refines_effmpolyP.
{ move=> k /MFacts.add_in_iff [Hk|Hk].
  - move/mnmc_eq_seqP/eqP: Hk <-.
    apply Rseqmultinom_iff in Hm.
    by rewrite -Hm size_tuple.
  - exact: refines_size_mpoly. }
move=> l l' Hl; rewrite mcoeffD mcoeffZ mcoeffX.
case: (boolP (m == l)) => Heq /=.
{ rewrite GRing.mulr1.
  rewrite MFacts.add_eq_o /=; last first.
  { apply/mnmc_eq_seqP.
    apply Rseqmultinom_iff in Hm; rewrite -Hm.
    move/eqP: Heq ->.
    by apply Rseqmultinom_iff in Hl; rewrite Hl. }
  move/eqP in Heq; rewrite Heq in Hnotin.
  by rewrite memN_msupp_eq0 // GRing.addr0.
}
rewrite GRing.mulr0 GRing.add0r.
rewrite MFacts.add_neq_o /=; last first.
{ apply/mnmc_eq_seqP.
  apply Rseqmultinom_iff in Hm; rewrite -Hm.
  by apply Rseqmultinom_iff in Hl; rewrite -Hl.
}
rewrite refinesE in Hp.
exact: refines_find_mpoly.
Qed.

Lemma refines_size_add n (k' : seqmultinom) (e : T)
  (p : mpoly n T) (p' : effmpoly T) (q : effmpoly T) :
  MProps.Add k' e q p' -> refines Reffmpoly p p' ->
  refines Rseqmultinom (multinom_of_seqmultinom_val n k') k'.
Proof.
move=> Hadd Hp.
apply refines_multinom_of_seqmultinom_val.
apply (@refines_size_mpoly _ _ _ _ Hp).
exists e; move: (Hadd k'); rewrite MFacts.add_eq_o; [|by apply M.E.eq_refl].
apply M.find_2.
Qed.

Lemma refines_Madd_mnm_add_sum n m m' c (p : mpoly n T) p' :
   refines Rseqmultinom m m' ->
   refines (Reffmpoly (T := T) (n := n)) p p' ->
   refines Reffmpoly (\sum_(i2 <- msupp p) (c * p@_i2) *: 'X_[m + i2])
         (M.fold (fun (l' : M.key) (c' : T) => M.add (mnm_add_seq m' l') (c * c')%C) p' M.empty).
Proof.
move=> refines_m; move: p.
apply MProps.fold_rec.
{ move=> q' Eq' q Hq.
  match goal with
  | [  |- refines Reffmpoly ?pol M.empty ] => suff ->: pol = 0
  end.
  { by apply refines_mp0_eff. }
  apply /mpolyP => l.
  rewrite big1 ?mcoeff0 //.
  move=> i _.
  rewrite (refines_find_mpoly Hq (refines_seqmultinom_of_multinom i)) /=.
  case_eq (M.find (seqmultinom_of_multinom i) q') =>[s|/=].
  - rewrite -MFacts.find_mapsto_iff MFacts.elements_mapsto_iff.
    by rewrite -in_InA_eq_key_elt_iff (proj1 (MProps.elements_Empty _ ) Eq').
  - by move=> _; rewrite GRing.mulr0 GRing.scale0r.
}
move=> k' e q p'' p''' Hmap Hin Hadd Hind p refines_p.
pose k := multinom_of_seqmultinom_val n k'.
have Hk : refines Rseqmultinom k k'; [by apply (refines_size_add Hadd refines_p)|].
have Hp : p@_k = e.
{ rewrite (refines_find_mpoly refines_p Hk) Hadd MFacts.add_eq_o //.
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
rewrite /p0.
apply refines_Madd_mnm_add.
{ eapply refines_apply; first by eapply refines_apply; tc.
  rewrite /k.
  apply refines_multinom_of_seqmultinom_val.
  apply (@refines_size_mpoly _ _ _ _ refines_p).
  red in Hadd.
  apply/MFacts.in_find_iff.
  rewrite Hadd MFacts.add_eq_o //.
  exact/mnmc_eq_seqP.
}
{ eapply Hind.
  apply (rem_mpoly_eff Hin Hadd refines_p Hk). }
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
Global Instance refines_mpoly_mul_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_mul mpoly_mul_eff.
Proof.
apply refines_abstr => q q' refines_q.
apply refines_abstr => p p' refines_p.
rewrite [mpoly_mul q p]mpolyME -ssrcomplements.pair_bigA_seq_curry /=.
rewrite /mpoly_mul_eff.
pose f m c := \big[+%R/0]_(i2 <- msupp p) ((c * p@_i2) *: 'X_[(m + i2)]).
pose f' m c := @mult_monomial_eff _ mul_instR m c p'.
now_show (refines Reffmpoly (\sum_(m <- msupp q) f m q@_m)
  (M.fold (fun m c => mpoly_add_eff (f' m c)) q' M.empty)).
apply(*:*) refines_mpoly_sum_eff =>//.
- by move=> m; rewrite /f big1 // => m2 _; rewrite GRing.mul0r GRing.scale0r.
- apply refines_abstr => m m' refines_m.
  apply refines_abstr => c c' refines_c.
  rewrite /f /f' /mult_monomial_eff.
  rewrite {refines_c}(refines_eq refines_c).
  by apply refines_Madd_mnm_add_sum.
Qed.

Definition mpoly_exp {n} (p : {mpoly T[n]}) (n : nat) := (p ^+ n)%R.

Global Instance refines_mpoly_exp_eff n :
  refines (Reffmpoly ==> Logic.eq ==> Reffmpoly (T := T) (n := n))
  mpoly_exp (mpoly_exp_eff (n:=n)).
Proof.
apply refines_abstr => p p' refines_p.
apply refines_abstr => n' n''; rewrite refinesE => <- {n''}.
rewrite /mpoly_exp /mpoly_exp_eff.
elim: n' => [|n' IHn]; [by rewrite GRing.expr0; apply refines_mp1_eff|].
rewrite GRing.exprS /=; case_eq n'; [by rewrite GRing.expr0 GRing.mulr1|].
move=> _ <-; eapply refines_apply; [|exact IHn].
by eapply refines_apply; [apply refines_mpoly_mul_eff|].
Qed.

Definition seq_Reffmpoly n k (lq : k.-tuple {mpoly T[n]}) (lq' : seq (effmpoly T)) :=
  ((size lq' = k) * forall i, Reffmpoly lq`_i (nth mp0_eff lq' i))%type.

Lemma refines_comp_monomial_eff n k :
  refines (Rseqmultinom ==> Logic.eq ==> @seq_Reffmpoly n k ==> Reffmpoly)
  (fun m c lq => mpolyC c * mmap1 (tnth lq) m) (comp_monomial_eff (n:= n)).
Proof.
apply refines_abstr => m m' refines_m.
apply refines_abstr => c c' refines_c.
rewrite refinesE in refines_c; rewrite -{}refines_c {c'}.
apply refines_abstr => lq lq' refines_lq.
rewrite mul_mpolyC /comp_monomial_eff; eapply refines_apply.
{ eapply refines_apply; [apply refines_mpoly_scale_eff|by apply trivial_refines]. }
move: refines_lq; rewrite refinesE /seq_Reffmpoly; move => [sz_lq refines_lq].
move: m m' refines_m lq lq' sz_lq refines_lq.
elim: k => [|k IHk] m m' refines_m lq lq' sz_lq refines_lq.
{ rewrite /mmap1 bigop.big_ord0.
  move: (size0nil sz_lq) => ->; rewrite /zipwith /=; apply refines_mp1_eff. }
move: sz_lq; case_eq lq' => //= q0 lqt' Hlq' sz_lq.
move: (@refines_size _ _ _ refines_m); case_eq m' => //= m0 mt' Hm' sz_m'.
rewrite /foldr /= -/(foldr _ _) /mmap1 bigop.big_ord_recl.
eapply refines_apply; [eapply refines_apply; [by apply refines_mpoly_mul_eff|]|].
{ move: (@refines_nth _ _ _ ord0 refines_m); rewrite Hm' /= => <-.
  eapply refines_apply; [|by apply trivial_refines; symmetry].
  eapply refines_apply; [by apply refines_mpoly_exp_eff|]; rewrite refinesE.
  replace (tnth _ _) with (lq`_O); [|by case lq, tval].
  change q0 with (nth mp0_eff (q0 :: lqt') O); rewrite -Hlq'; apply refines_lq. }
injection sz_lq => {sz_lq} sz_lq; injection sz_m' => {sz_m'} sz_m'.
assert (refines_mt : refines Rseqmultinom (multinom_of_seqmultinom_val k mt') mt').
{ by apply /refines_multinom_of_seqmultinom_val /eqP. }
assert (Hlq_lq' : forall i : nat,
                    Reffmpoly [tuple of behead lq]`_i (nth mp0_eff lqt' i)).
{ by move=> i; move: (refines_lq i.+1); rewrite Hlq' /=; case tval; elim i. }
move: (IHk _ _ refines_mt [tuple of behead lq] _ sz_lq Hlq_lq').
rewrite refinesE /Reffmpoly /ofun_hrel => ->; f_equal.
apply bigop.eq_big => // i _; f_equal.
{ rewrite tnth_behead; f_equal.
  by apply ord_inj; rewrite inordK //; move: (ltn_ord i). }
move /eqP in sz_m'; move: (refines_multinom_of_seqmultinom_val sz_m') => Hmt'.
move: (@refines_nth _ _ _ i Hmt') => <-.
move: (@refines_nth _ _ _ (inord i.+1) refines_m); rewrite Hm' /=.
rewrite inordK /=; [|by rewrite ltnS]; move=> ->; apply f_equal.
by apply ord_inj; rewrite inordK //; move: (ltn_ord i).
Qed.

Arguments comp_mpoly {n R k} lq p.
Global Instance refines_comp_mpoly_eff n k :
  refines (@seq_Reffmpoly n k ==> Reffmpoly ==> Reffmpoly)
  comp_mpoly (comp_mpoly_eff (n:= n)).
Proof.
apply refines_abstr => lq lq' refines_lq.
apply refines_abstr => p p' refines_p.
rewrite /comp_mpoly /mmap /comp_mpoly_eff.
pose f := fun m c => c%:MP_[n] * mmap1 (tnth lq) m.
rewrite (eq_bigr (fun m => f m p@_m)) //.
apply refines_mpoly_sum_eff.
{ by move=> m; rewrite /f mpolyC0 GRing.mul0r. }
{ apply refines_abstr => m m' refines_m.
  apply refines_abstr => c c'; rewrite refinesE /f => <-.
  change (_ * _) with ((fun lq => c%:MP_[n] * mmap1 (tnth lq) m) lq).
  eapply refines_apply; [|by apply refines_lq].
  change (fun _ => _) with ((fun c lq => c%:MP_[n] * mmap1 (tnth lq) m) c).
  eapply refines_apply; [|by apply trivial_refines; symmetry].
  change (fun _ => _) with ((fun m (c : T) lq => c%:MP_[n] * mmap1 (tnth lq) m) m).
  eapply refines_apply; [apply refines_comp_monomial_eff|apply refines_m]. }
apply refines_p.
Qed.

End effmpoly_theory.

(** ** Part III: Parametricity *)

Derive Inversion inv_HdRel with
  (forall (A : Type) (eqA : A -> A -> Prop) (x : A) (s : seq A), @HdRel A eqA x s) Sort Prop.

Section effmpoly_parametricity.

Context (A : ringType) (C : Type) (rAC : A -> C -> Type).

Definition M_hrel (m : M.t A) (m' : M.t C) : Type :=
  ((forall k, M.In k m <-> M.In k m')
  * forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> rAC e e')%type.

Definition ReffmpolyA {n} := (@Reffmpoly A n \o M_hrel)%rel.

Context `{one_of C, opp_of C, add_of C, sub_of C, mul_of C}.

Context `{!refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) (fun x y => x + -y) sub_op}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.

Context (C2A : C -> A).

Hypothesis C2A_correct : forall c : C, rAC (C2A c) c.

Lemma refines_M_hrel_empty : refines M_hrel M.empty M.empty.
Proof.
rewrite refinesE; split.
{ by move=> k; rewrite !MFacts.empty_in_iff. }
by move=> k e e' K; exfalso; apply MFacts.empty_mapsto_iff in K.
Qed.

Lemma refines_M_hrel_add :
  refines (Logic.eq ==> rAC ==> M_hrel ==> M_hrel) (@M.add A) (@M.add C).
Proof.
rewrite refinesE; split.
{ move=> k; rewrite !MFacts.add_in_iff H4 (* FIXME *); split;
  (elim; [by left|right]); by [rewrite -(fst X0 k)|rewrite (fst X0 k)]. }
move=> k e e'.
rewrite H4; move/MFacts.add_mapsto_iff => HH /MFacts.add_mapsto_iff HHH.
move: HH HHH.
Fail elim=> [[Hy <-]|[Hy He]].
Admitted. (*
{ move: Hy; move/mnmc_eq_seqP/eqP->.
  by elim=>[[_ <-]|] //; rewrite M.E.eq_refl; elim. }
by elim; [elim=> H'; elim (Hy H')|elim=>_; apply (snd X)].
Qed.
*)

Lemma refines_M_hrel_singleton :
  refines (Logic.eq ==> rAC ==> M_hrel)
     (@MProps.singleton A) (@MProps.singleton C).
Proof.
apply refines_abstr => k k'; rewrite refinesE => <-.
apply refines_abstr => e e' refines_e.
rewrite /MProps.singleton.
eapply refines_apply; [|by apply refines_M_hrel_empty].
eapply refines_apply; [|exact refines_e].
eapply refines_apply; [apply refines_M_hrel_add|by rewrite refinesE].
Qed.

Lemma refines_M_hrel_map :
  refines ((rAC ==> rAC) ==> M_hrel ==> M_hrel) (@M.map A A) (@M.map C C).
Proof.
apply refines_abstr => f f' refines_f.
apply refines_abstr => m m' refines_m.
rewrite refinesE; split.
{ move=> k; rewrite !MProps.F.map_in_iff.
  move: refines_m; rewrite refinesE => H'; apply H'. }
move=> k e e'.
Admitted. (*
rewrite !MFacts.map_mapsto_iff => [[a Ha] [a' Ha']].
rewrite (proj1 Ha) (proj1 Ha').
apply refinesP; eapply refines_apply; [by apply refines_f|].
move: refines_m (proj2 Ha) (proj2 Ha'); rewrite !refinesE => refines_m.
apply (snd refines_m).
Qed.
*)

(* Missing in new CoqEAL *)
Fixpoint ohrel {A B : Type} (rAB : A -> B -> Type) sa sb : Type :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

Lemma refines_M_hrel_find :
  refines (Logic.eq ==> M_hrel ==> ohrel rAC) (@M.find A) (@M.find C).
Proof.
apply refines_abstr => k k'; rewrite refinesE => <-.
apply refines_abstr => m m'; rewrite refinesE => refines_m.
rewrite refinesE; case_eq (M.find k m') => [e'|]; case_eq (M.find k m) => [e|] /=.
Admitted. (*
{ rewrite -!MFacts.find_mapsto_iff /=; apply (snd refines_m). }
{ rewrite -MFacts.not_find_in_iff /= => H' H''; apply H'.
  by apply (fst refines_m); rewrite MFacts.in_find_iff H''. }
{ rewrite -MFacts.not_find_in_iff /= => H' H''; apply H''.
  by apply (fst refines_m); rewrite MFacts.in_find_iff H'. }
done.
Qed.
*)

Lemma refines_M_hrel_map2 :
  refines ((ohrel rAC ==> ohrel rAC ==> ohrel rAC) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.map2 A A A) (@M.map2 C C C).
Proof.
apply refines_abstr => f f' refines_f.
apply refines_abstr => m1 m1' refines_m1.
apply refines_abstr => m2 m2' refines_m2.
have Hf : forall k, ohrel rAC (f (M.find k m1) (M.find k m2))
                      (f' (M.find k m1') (M.find k m2')).
{ move=> k; apply refinesP; eapply refines_apply; [eapply refines_apply|].
  { apply refines_f. }
  { eapply refines_apply; [|by apply refines_m1].
    eapply refines_apply; [apply refines_M_hrel_find|by apply trivial_refines]. }
  eapply refines_apply; [|by apply refines_m2].
  eapply refines_apply; [apply refines_M_hrel_find|by apply trivial_refines]. }
rewrite refinesE; rewrite refinesE in refines_m1, refines_m2; split.
{ move=> k; split.
  { move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
    apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
    move: (Hf k); rewrite He; case_eq (f' (M.find k m1') (M.find k m2')) => //.
    move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
    by destruct Hor as [Hk|Hk]; [left; apply refines_m1|right; apply refines_m2]. }
  move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
  apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
  move: (Hf k); rewrite He; case_eq (f (M.find k m1) (M.find k m2)) => //.
  move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
  by destruct Hor as [Hk|Hk]; [left; apply refines_m1|right; apply refines_m2]. }
move=> k e e' He He'; move: (M.find_1 He) (M.find_1 He') (Hf k).
case_eq (M.find k m1) => [e1|] He1.
{ rewrite M.map2_1; [|by left; exists e1; apply M.find_2].
  rewrite M.map2_1; [|by left; apply refines_m1; exists e1; apply M.find_2].
  by rewrite He1 => -> ->. }
case_eq (M.find k m2) => [e2|] He2.
{ rewrite M.map2_1; [|by right; exists e2; apply M.find_2].
  rewrite M.map2_1; [|by right; apply refines_m2; exists e2; apply M.find_2].
  by rewrite He1 He2 => -> ->. }
Admitted. (*
elim (@M.map2_2 _ _ _ m1 m2 k f); [| |by exists e].
{ by move=> [e'1 He'1]; apply M.find_1 in He'1; rewrite He'1 in He1. }
by move=> [e'2 He'2]; apply M.find_1 in He'2; rewrite He'2 in He2.
Qed.
*)

Lemma Sorted_InA_not_lt_hd B (ke h : M.key * B) t :
  Sorted (M.lt_key (elt:=B)) (h :: t) ->
  InA (M.eq_key_elt (elt:=B)) ke (h :: t) ->
  ~ M.lt_key ke h.
Proof.
move: h; elim t => [|h' t' IH] h.
{ move=> _ Hin.
  eapply inv_InA; [move=> _ y l Hy Hlt| |exact: Hin].
  by case: Hlt =><- _ => K; move: (proj1 Hy); apply M.E.lt_not_eq.
  by move=> _ y l K [_ Hl]; rewrite Hl in K; inversion K. }
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
have Hh := proj2 (Sorted_inv HS).
eapply inv_HdRel; last exact: Hh; [done|move=> _ b l Hbl [Hb _]].
rewrite Hb in Hbl.
eapply inv_InA; last exact: Hin; move=> _ y l' Hy [Hy' Hl'].
{ change (M.lt_key _ _) with (M.E.lt h.1 ke.1).
  by rewrite Hy' in Hy; move: (proj1 Hy); move/mnmc_eq_seqP/eqP => ->. }
apply (M.E.lt_trans Hbl), IH; first by apply (Sorted_inv HS).
by rewrite -Hl'.
Qed.

Lemma refines_M_hrel_elements :
  refines (M_hrel ==> list_R (fun x y => M.E.eq x.1 y.1 * rAC x.2 y.2)%type)
    (@M.elements A) (@M.elements C).
Proof.
apply refines_abstr => m m'; rewrite !refinesE => refines_m.
set em := M.elements m; set em' := M.elements m'.
have: ((forall k, (exists e, InA (M.eq_key_elt (elt:=A)) (k, e) em)
                 <-> exists e', InA (M.eq_key_elt (elt:=C)) (k, e') em')
  * (forall k e e', InA (M.eq_key_elt (elt:=A)) (k, e) em ->
                     InA (M.eq_key_elt (elt:=C)) (k, e') em' -> rAC e e'))%type.
{ split.
  { move=> k; split.
    { move=> [e He].
      have Hkm : M.In k m; [by exists e; apply M.elements_2|].
      elim (proj1 (fst refines_m _) Hkm) => e' He'; exists e' ;
      by apply M.elements_1. }
    move=> [e' He'].
    have Hkm' : M.In k m'; [by exists e'; apply M.elements_2|].
    elim (proj2 (fst refines_m _) Hkm') => e He; exists e.
    by apply M.elements_1. }
  move=> k e e' He He'.
  move: (M.elements_2 He) (M.elements_2 He'); apply (snd refines_m). }
move: (M.elements_3 m) (M.elements_3 m'); rewrite -/em -/em'.
clearbody em em'; move: {m m' refines_m} em em'.
elim=> [|h t IH]; case=> [|h' t'] //=.
{ Fail move=> _ _ [Heq _]; move: (proj2 (Heq h'.1)); elim.
Admitted. (*
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
    eapply inv_InA; last exact: He'; move=> _ y l Hl0 [Hy Hl];
      last by exists e'; rewrite -Hl.
    move: (Sorted_InA_tl_lt Sht He); move /M.E.lt_not_eq.
    move: Hhh'; move/mnmc_eq_seqP/eqP-> => Heq; exfalso; apply Heq.
    move: (proj1 Hl0); move/mnmc_eq_seqP/eqP => /= ->.
    by rewrite Hy; apply M.E.eq_refl. }
  move=> [e' He'].
  have Ht1 : exists e', InA (M.eq_key_elt (elt:=C)) (k, e') (h' :: t').
  { by exists e'; apply InA_cons_tl. }
  elim (proj2 Hht1 Ht1) => e He.
  eapply inv_InA; last exact: He; move=> _ y l Hl0 [Hy Hl];
    last by exists e; rewrite -Hl.
  move: (Sorted_InA_tl_lt Sht' He'); move /M.E.lt_not_eq.
  move: Hhh'; move/mnmc_eq_seqP/eqP<- => Heq; exfalso; apply Heq.
  move: (proj1 Hl0); move/mnmc_eq_seqP/eqP => /= ->.
  by rewrite Hy; apply M.E.eq_refl. }
by move=> e e' He He'; apply Hht2; apply InA_cons_tl.
Qed.
*)

Lemma refines_M_hrel_fold :
  refines
    ((Logic.eq ==> rAC ==> M_hrel ==> M_hrel) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.fold A _) (@M.fold C _).
Proof.
apply refines_abstr => f f' refines_f.
apply refines_abstr => m m' refines_m.
apply refines_abstr => i i' refines_i.
move: (refines_apply refines_M_hrel_elements refines_m); rewrite !M.fold_1 !refinesE.
move: i i' refines_i; generalize (M.elements m), (M.elements m').
elim=> [|h t IHt]; case=> //=.
- by move=> i i'; rewrite refinesE.
- by move=> a l i i' _ K; inversion K.
- by move=> i i' _ K; inversion K.
move=> h' t' i i' refines_i; elim.
Admitted. (*
move=> *; apply IHt.
eapply refines_apply; [|by apply refines_i].
eapply refines_apply; [|by rewrite refinesE; apply Hh2].
eapply refines_apply; [by apply refines_f|].
move: Hh1; move/mnmc_eq_seqP/eqP<-; apply refines_eq_refl.
Qed.
*)

Global Instance ReffmpolyA_mp0_eff (n : nat) :
  refines (@ReffmpolyA n) 0 (@mp0_eff C).
Proof.
eapply refines_trans; [by apply composable_comp|by apply refines_mp0_eff|].
Admitted. (*
apply set_refines, refines_M_hrel_empty.
Qed.
*)

Global Instance ReffmpolyA_mp1_eff (n : nat) :
  refines (@ReffmpolyA n) 1 (mp1_eff (n:=n)).
Proof.
eapply refines_trans; [by apply composable_comp|by apply refines_mp1_eff|].
Admitted. (*
apply set_refines; rewrite /mp1_eff; eapply refines_apply; [|by tc].
by eapply refines_apply; [apply refines_M_hrel_singleton|apply refines_eq_refl].
Qed.
*)

Global Instance ReffmpolyA_mpvar_eff {n1 n2 : nat} (rn : nat_R n1 n2) :
  refines (rAC ==> Logic.eq ==> Rord rn ==> @ReffmpolyA n1)
    mpvar (mpvar_eff (n:=n2)).
Proof.
eapply refines_trans; [|by eapply refines_mpvar_eff|].
{ do 2 apply composable_imply_id1.
  Fail rewrite -{2}(comp_eqr (Rord rn)); apply composable_imply, composable_comp.
  admit. }
Admitted. (*
apply set_refines; rewrite /mpvar_eff.
apply refines_abstr => c c' refines_c.
apply refines_abstr => d d'; rewrite refinesE => <-.
apply refines_abstr => i i'; rewrite refinesE => <-.
eapply refines_apply; [|by apply refines_c].
eapply refines_apply; [apply refines_M_hrel_singleton|apply refines_eq_refl].
Qed.
*)

Global Instance ReffmpolyA_mpolyC_eff (n : nat) :
  refines (rAC ==> ReffmpolyA) (@mpolyC n A) (mpolyC_eff (n:=n)).
Proof.
eapply (refines_trans (rAB:=(Logic.eq ==> Reffmpoly)%rel)
                    (rBC:=(rAC ==> M_hrel)%rel)); [|by apply refines_mpolyC_eff|].
{ admit; rewrite -{2}(@comp_eql _ _ rAC); apply composable_imply, composable_comp. }
Admitted. (*
apply set_refines; rewrite /mpolyC_eff.
apply refines_abstr => c c' refines_c.
eapply refines_apply; [|by apply refines_c].
eapply refines_apply; [apply refines_M_hrel_singleton|apply refines_eq_refl].
Qed.
*)

Global Instance ReffmpolyA_mpolyX_eff (n : nat) :
  refines (Rseqmultinom ==> ReffmpolyA) (@mpolyX n A) mpolyX_eff.
Proof.
eapply refines_trans; [|by apply refines_mpolyX_eff|].
{ Fail rewrite -{2}(comp_eqr Rseqmultinom).
  admit; apply composable_imply, composable_comp. }
Admitted. (*
apply set_refines; rewrite /mpolyX_eff.
apply refines_abstr => m m' refines_m.
eapply refines_apply; [|by tc].
eapply refines_apply; [apply refines_M_hrel_singleton|apply refines_m].
Qed.
*)

Lemma refines_M_hrel_mpoly_scale_eff :
  refines (rAC ==> M_hrel ==> M_hrel)
    (@mpoly_scale_eff A *%R) mpoly_scale_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_scale_eff (n : nat) :
  refines (rAC ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_scale n A) mpoly_scale_eff.
Proof.
Admitted. (* Érik *)

Lemma refines_M_hrel_mpoly_add_eff :
  refines (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_add_eff A +%R) mpoly_add_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_add_eff (n : nat) :
  refines (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_add n A) mpoly_add_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_sub_eff (n : nat) :
  refines (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_sub A n) mpoly_sub_eff.
Proof.
Admitted. (* Érik *)

Lemma refines_M_hrel_mpoly_mul_eff :
  refines (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_mul_eff A +%R *%R) mpoly_mul_eff.
Proof.
Admitted. (* Érik *)

Global Instance ReffmpolyA_mpoly_mul_eff (n : nat) :
  refines (ReffmpolyA ==> ReffmpolyA ==> ReffmpolyA)
    (@mpoly_mul n A) mpoly_mul_eff.
Proof.
Admitted. (* Érik *)

Lemma refines_M_hrel_mpoly_exp_eff n :
  refines (M_hrel ==> Logic.eq ==> M_hrel)
    (@mpoly_exp_eff _ 1%R +%R *%R n) (mpoly_exp_eff (n:=n)).
Proof.
rewrite /mpoly_exp_eff.
apply refines_abstr => m m' refines_m.
apply refines_abstr => k k'; rewrite refinesE => <- {k'}.
elim k => [|k' IHk] /=.
{ rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refines_M_hrel_singleton|by apply trivial_refines]. }
case_eq k' => // _ <-; eapply refines_apply; [|by apply IHk].
eapply refines_apply; [|by apply refines_m].
apply refines_M_hrel_mpoly_mul_eff.
Qed.

Global Instance ReffmpolyA_mpoly_exp_eff (n : nat) :
  refines (ReffmpolyA ==> Logic.eq ==> ReffmpolyA)
    (@mpoly_exp A n) (mpoly_exp_eff (n:=n)).
Proof.
eapply refines_trans; [|by apply refines_mpoly_exp_eff|].
{ apply composable_imply, composable_imply_id1, composable_comp. }
Admitted. (*
apply set_refines, refines_M_hrel_mpoly_exp_eff.
Qed.
*)

Definition seq_ReffmpolyA n k := (@seq_Reffmpoly A n k \o list_R M_hrel)%rel.

Lemma refines_M_hrel_comp_monomial_eff n :
  refines (Logic.eq ==> rAC ==> list_R M_hrel ==> M_hrel)
    (@comp_monomial_eff A 1%R +%R *%R n) (comp_monomial_eff (n:=n)).
Proof.
apply refines_abstr => m m'; rewrite refinesE => <-.
apply refines_abstr => c c' refines_c.
apply refines_abstr => lq lq' refines_lq.
rewrite /comp_monomial_eff.
eapply refines_apply.
{ eapply refines_apply; [apply refines_M_hrel_mpoly_scale_eff|apply refines_c]. }
move: lq lq' refines_lq m.
elim=> [|hlq tlq IH]; case=> [|hlq' tlq']; rewrite refinesE //=.
{ move=> _ m /=; rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refines_M_hrel_singleton|by apply trivial_refines]. }
by move=> K; inversion K.
by move=> K; inversion K.
move=> K; inversion K. (* [|Hhlq Htlq] *)
 case=> [|hm tm] /=.
{ rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refines_M_hrel_singleton|by apply trivial_refines]. }
eapply refines_apply; [eapply refines_apply|].
{ by apply refines_M_hrel_mpoly_mul_eff. }
{ eapply refines_apply; [|by apply trivial_refines; symmetry].
  eapply refines_apply; first by apply refines_M_hrel_mpoly_exp_eff.
  apply trivial_refines.
  done. }
by apply IH; rewrite refinesE.
Qed.

Global Instance ReffmpolyA_comp_mpoly_eff (n k : nat) :
  refines (seq_ReffmpolyA (k:=k) ==> ReffmpolyA ==> ReffmpolyA)
    (comp_mpoly (k:=n)) (comp_mpoly_eff (n:=n)).
Proof.
eapply (refines_trans
          (rAB:=(@seq_Reffmpoly _ n k ==> Reffmpoly ==> Reffmpoly)%rel));
  [|by apply refines_comp_mpoly_eff|].
{ apply composable_imply, composable_imply, composable_comp. }
Admitted. (*
apply set_refines; rewrite /comp_mpoly_eff.
apply refines_abstr => lq lq' refines_lq.
apply refines_abstr => p p' refines_p.
eapply refines_apply; [|by apply refines_M_hrel_empty].
eapply refines_apply; [|by apply refines_p].
eapply refines_apply; [by apply refines_M_hrel_fold|].
apply refines_abstr => m m' refines_m.
apply refines_abstr => c c' refines_c.
eapply refines_apply; [by apply refines_M_hrel_mpoly_add_eff|].
eapply refines_apply; [|by apply refines_lq].
eapply refines_apply; [|by apply refines_c].
eapply refines_apply; [apply refines_M_hrel_comp_monomial_eff|apply refines_m].
Qed.
*)

End effmpoly_parametricity.
