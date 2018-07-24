Require Import Reals.
Require Import ZArith Psatz.
Require Import Fourier_util.


Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
induction n; [easy|simpl].
now rewrite SuccNat2Pos.id_succ.
Qed.

(* TODO: refaire sans les fonctions, mais avec trois arguments n x x^n *)
Lemma powerRZ_ind (P : Z -> (R -> R) -> Prop) :
  P 0%Z (fun x => 1) ->
  (forall n, P (Z.of_nat n) (fun x => x ^ n)) ->
  (forall n, P ((-(Z.of_nat n))%Z) (fun x => / x ^ n)) ->
  (forall f g, (forall x, f x = g x) -> forall n, P n f -> P n g) ->
  forall (m : Z), P m (fun x => powerRZ x m).
Proof.
intros H0 Hpos Hneg Hext m.
destruct m.
- now simpl.
- rewrite <-positive_nat_Z.
  eapply Hext.
    intro x.
    now rewrite (pow_powerRZ x ).
  apply Hpos.
- unfold powerRZ; eapply Hext.
    intro x.
    reflexivity.
  rewrite <-Pos2Z.opp_pos.
  rewrite <-positive_nat_Z.
  apply Hneg.
Qed.

Lemma powerRZ_inv x alpha : (x <> 0) -> powerRZ (/ x) alpha = / powerRZ x alpha.
Proof.
intros Hx.
apply (powerRZ_ind (fun alpha f => forall x, x<>0 -> f (/ x) = / powerRZ (x) (alpha))).
- now intros x0 Hx0; simpl; field.
- intros n x0 Hx0.
  now rewrite <-pow_powerRZ; rewrite ?Rinv_pow; rewrite ?pow_powerRZ.
- induction n.
    intros x0 Hx0; now simpl.
  intros x0 Hx0; rewrite <-Nat.add_1_r; rewrite Nat2Z.inj_add.
  rewrite Z.opp_add_distr; rewrite powerRZ_add; trivial. simpl; rewrite pow_add.
  rewrite Rinv_mult_distr; try (apply pow_nonzero); try (apply Rinv_neq_0_compat; trivial).
  rewrite IHn ; simpl; try field; trivial.
  now split; try lra; try apply powerRZ_NOR.
- intros f g Hfg n Hf x0 Hx0.
  now rewrite <-Hfg; rewrite Hf.
- easy.
Qed.

Lemma powerRZ_inv_neg x alpha : (x <> 0) -> powerRZ x alpha = powerRZ (/ x) (- alpha).
Proof.
  intros Hx.
apply (powerRZ_ind (fun alpha f => forall x, x<>0 -> f x = powerRZ (/ x) (- alpha))); try easy.
- intros n. induction n.
    now intros x0 Hx0; simpl.
  intros x0 Hx0.
  unfold pow; fold pow.
  rewrite IHn; try easy.
  assert(x0 = powerRZ (/ x0) (-1)).
  now simpl; field.
  rewrite H at 1.
  rewrite <-powerRZ_add.
  assert((-1 + - Z.of_nat n) = (- Z.of_nat (S n)))%Z.
    now rewrite <-Nat.add_1_r; rewrite Nat2Z.inj_add; ring.
  now rewrite H0.
  now apply Rinv_neq_0_compat.
- intros n x0 Hx0; rewrite pow_powerRZ; rewrite Z.opp_involutive.
  now rewrite <-pow_powerRZ; rewrite ?Rinv_pow; rewrite ?pow_powerRZ.
- intros f g Hfg n Hf x0 Hx0.
  now rewrite <-Hfg;rewrite Hf.
Qed.

Lemma powerRZ_neg_inv x alpha : (x <> 0) -> powerRZ (/ x) alpha = powerRZ x (- alpha).
Proof.
intros Hx.
assert( alpha = - - alpha)%Z.
  now rewrite Z.opp_involutive .
now rewrite H; rewrite <-powerRZ_inv_neg, ?Z.opp_involutive.
Qed.

(* Lemma powerRZ_mult : forall m x y, ((m >= 0)%Z \/ (x * y <> 0)) -> powerRZ (x*y) m = powerRZ x m * powerRZ y m. *)
(* Proof. *)
(* intros m x0 y0 Hmxy. *)
(* apply (powerRZ_ind (fun z f => forall x y, ((z >= 0)%Z \/ (x * y <> 0)) -> f (x * y) = powerRZ x z * powerRZ y z)); try easy. *)
(* - intros x y; simpl; now rewrite Rmult_1_l. *)
(* - intros n x y. *)
(*   now rewrite Rpow_mult_distr; rewrite !pow_powerRZ. *)
(* - intros n x y H. *)
(*   destruct H as [H|H]. *)
(*     rewrite H. simpl. *)
(*     assert(n = 0)%nat. *)
(*     rewrite Z.eq_opp_l, Z.opp_0 in H. *)
(*     apply Nat2Z.inj; now apply H. *)
(*     now rewrite H0; simpl; rewrite Rinv_1,Rmult_1_l. *)
(*   assert (x <> 0). *)
(*     now intros Habs; apply H; rewrite Habs, Rmult_0_l. *)
(*   assert (y <> 0). *)
(*     now intros Habs; apply H; rewrite Habs, Rmult_0_r. *)
(*   assert(/ x <> 0). *)
(*     intros Habs; apply H. *)
(*     now exfalso; apply (Rinv_neq_0_compat x H0 Habs). *)
(*   assert(/ y <> 0). *)
(*     intros Habs; apply H. *)
(*     now exfalso; apply (Rinv_neq_0_compat y H1 Habs). *)
(*     induction n. *)
(*     now rewrite pow_O; rewrite Rinv_1; simpl; rewrite Rmult_1_l. *)
(*   unfold pow; fold pow. *)
(*   rewrite Rinv_mult_distr; try apply pow_nonzero; try easy. *)
(*   rewrite IHn, <-!powerRZ_neg_inv; try easy. *)
(*   rewrite !Nat2Z.inj_succ, <-!Z.add_1_r, !powerRZ_add; try easy. *)
(*   assert(forall x0, (x0 <> 0) -> / x0 = powerRZ (/ x0) 1). *)
(*     now intros x1 Hx1; simpl; field. *)
(*   rewrite <-!H4; try easy. *)
(*   field; split; easy. *)
(* - intros f g Hfg n Hf x y Hnxy. *)
(*   rewrite <-Hfg. rewrite Hf; easy. *)
(* -  *)
(* Qed *).