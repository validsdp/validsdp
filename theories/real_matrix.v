(** * Basic results about real matrices.

    Dot product, Euclidean norm, Cauchy-Schwarz inequality, componentwise
    orders and absolute value, definition of positive definiteness. *)

Require Import Reals Flocq.Core.Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.algebra.ssralg mathcomp.algebra.matrix mathcomp.ssreflect.bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory.

(** ** Miscellaneous lemmas about 1x1 matrices and transposition. *)
Section Misc.

Lemma eq_scalar (R : Type) (A B : 'M[R]_1) :
  A = B <-> A ord0 ord0 = B ord0 ord0.
Proof.
split; move=> HAB; [by rewrite HAB|].
by rewrite -matrixP => i j; rewrite (ord_1_0 i) (ord_1_0 j).
Qed.

Lemma Mmul_scalar (R : ringType) (A B : 'M[R]_1) :
  A *m B = (A ord0 ord0 * B ord0 ord0)%:M.
Proof.
rewrite -matrixP => i j.
rewrite (ord_1_0 i) (ord_1_0 j) !mxE eqE /= /GRing.natmul /=.
by rewrite big_ord_recl big_ord0 GRing.addr0.
Qed.

Lemma trmx_scalar (R : Type) (x : 'M[R]_1) : x^T = x.
Proof.
rewrite -matrixP /eqrel => i j.
by rewrite /trmx mxE (ord_1_0 i) (ord_1_0 j).
Qed.

Lemma scale_trmx (R : ringType) (s : R) (n m : nat) (A : 'M[R]_(n, m)) :
  ((s *: A)^T = s *: A^T)%Ri.
Proof. by rewrite -matrixP => i j; rewrite !mxE. Qed.

Lemma add_trmx (R : ringType) n m (A B : 'M[R]_(n, m)) : (A + B)^T = A^T + B^T.
Proof. by rewrite -matrixP => i j; rewrite !mxE. Qed.

Lemma mulmx_sum_sum n (P : 'M[R]_n) (SymP : P^T = P) (x y : 'cV[R]_n) :
  (x + y)^T *m P *m (x + y)
  = x^T *m P *m x + y^T *m P *m y + 2 *: (x^T *m P *m y).
Proof.
rewrite add_trmx !mulmxDl !mulmxDr GRing.scalerDl GRing.scale1r.
rewrite (GRing.addrC (y^T *m P *m x)).
rewrite GRing.addrA -(GRing.addrA (x^T *m P *m x) (x^T *m P *m y)).
rewrite (GRing.addrC (x^T *m P *m y)) !GRing.addrA.
apply f_equal2; [by []|].
rewrite -{1}(trmxK P) -trmx_mul -{1}(trmxK x) -trmx_mul.
by rewrite trmx_scalar SymP mulmxA.
Qed.

End Misc.

(** ** Pointwise Rabs, Rle and Rlt. *)
Section Mabs_order_def.

Variable n m : nat.

Definition Mabs n m (A: 'M_(n, m)) := map_mx Rabs A.

Definition Mle (A B : 'M_(n, m)) := forall i j, A i j <= B i j.

Definition Mlt (A B : 'M_(n, m)) := forall i j, A i j < B i j.

End Mabs_order_def.

(** Notations for pointwise Rle and Rlt. *)
Infix "<=m:" := Mle (at level 70) : R_scope.
Infix "<m:" := Mlt (at level 70) : R_scope.

(** *** Lemmas about pointwise Rabs, Rle and Rlt.

    Mostly lifting of lemmas on reals, trying to keep the same names
    with prefix [M] instead of [R]. *)
Section Mabs_order_prop.

Lemma Mle_scalar (A B : 'M_1) :
  (A <=m: B)%Re <-> (A ord0 ord0 <= B ord0 ord0)%Re.
Proof.
split; rewrite /Mle => H // => i j.
by rewrite (ord_1_0 i) (ord_1_0 j).
Qed.

Lemma Mlt_scalar (A B : 'M_1) :
  (A <m: B)%Re <-> (A ord0 ord0 < B ord0 ord0)%Re.
Proof.
split; rewrite /Mle => H // => i j.
by rewrite (ord_1_0 i) (ord_1_0 j).
Qed.

Variable n m : nat.

Lemma Mle_scalar_mx (r1 r2 : R) :
  (r1%:M : 'M_n.+1) <=m: r2%:M <-> (r1 <= r2)%Re.
Proof.
split; move=> Hr12.
{ by move: (Hr12 ord0 ord0); rewrite !mxE. }
by move=> i j; rewrite !mxE; case eqP => _; rewrite /GRing.natmul /=; [|right].
Qed.

Lemma Mabs_no_0 (A : 'M_(n, m)) : A <> 0 -> Mabs A <> 0.
Proof.
move=> HA HMA; apply HA; move: HMA.
rewrite /Mabs /map_mx -matrixP => HMA; rewrite -matrixP => i j.
move: (HMA i j); rewrite !mxE; apply Rabs_0.
Qed.

Lemma Mabs_right (A : 'M_(n, m)) : 0 <=m: A -> Mabs A = A.
Proof.
move=> HA.
rewrite -matrixP => i j; rewrite mxE Rabs_pos_eq //.
by replace 0%Re with ((0 : 'M[R]_(n, m)) i j); [apply HA|rewrite mxE].
Qed.

Lemma Mle_tr (A B : 'M_(n, m)) : A <=m: B -> A^T <=m: B^T.
Proof. move=> HAB i j; rewrite !mxE; apply HAB. Qed.

Lemma Mlt_tr (A B : 'M_(n, m)) : A <m: B -> A^T <m: B^T.
Proof. move=> HAB i j; rewrite !mxE; apply HAB. Qed.

Lemma Mlt_le (A B : 'M_(n, m)) : A <m: B -> A <=m: B.
Proof. rewrite /Mlt /Mle => H i j; apply Rlt_le, H. Qed.

Lemma Mabs_pos (A : 'M_(n, m)) : 0 <=m: Mabs A.
Proof. move=> i j; rewrite !mxE; apply Rabs_pos. Qed.

Lemma Mabs_triang (A B : 'M_(n,m)) : (Mabs (A + B)) <=m: (Mabs A + Mabs B).
Proof. move=> i j; rewrite !mxE; apply Rabs_triang. Qed.

Lemma Mabs_opp (A : 'M_(n, m)) : Mabs (- A) = Mabs A.
Proof. by rewrite -matrixP => i j; rewrite !mxE Rabs_Ropp. Qed.

Lemma Mle_abs (A : 'M_(n, m)) : A <=m: Mabs A.
Proof. move=> i j; rewrite !mxE; apply Rle_abs. Qed.

Lemma Mge_opp_abs (A : 'M_(n, m)) : - Mabs A <=m: A.
Proof. move=> i j; rewrite !mxE; apply Rge_opp_abs. Qed.

Lemma Mle_refl (A : 'M_(n, m)) : A <=m: A.
Proof. by move=> i j; right. Qed.

Lemma Mle_trans (A B C : 'M_(n, m)) : A <=m: B -> B <=m: C -> A <=m: C.
Proof.
by rewrite /Mle => H1 H2 i j; apply (Rle_trans _ _ _ (H1 i j)).
Qed.

Lemma Mlt_trans (A B C : 'M_(n, m)) : A <m: B -> B <m: C -> A <m: C.
Proof.
by rewrite /Mle => H1 H2 i j; apply (Rlt_trans _ _ _ (H1 i j)).
Qed.

Lemma Mlt_le_trans (A B C : 'M_(n, m)) : A <m: B -> B <=m: C -> A <m: C.
Proof.
by rewrite /Mle => H1 H2 i j; apply (Rlt_le_trans _ _ _ (H1 i j)).
Qed.

Lemma Mle_lt_trans (A B C : 'M_(n, m)) : A <=m: B -> B <m: C -> A <m: C.
Proof.
by rewrite /Mle => H1 H2 i j; apply (Rle_lt_trans _ _ _ (H1 i j)).
Qed.

Lemma Madd_le_compat (A B C D : 'M_(n, m)) :
  A <=m: B -> C <=m: D -> A + C <=m: B + D.
Proof.
by rewrite /Mle => H1 H2 i j; rewrite !mxE; apply Rplus_le_compat.
Qed.

Lemma Madd_le_compat_l (A B C : 'M_(n, m)) : B <=m: C -> A + B <=m: A + C.
Proof.
by rewrite /Mle => H i j; rewrite !mxE; apply Rplus_le_compat_l.
Qed.

Lemma Madd_le_compat_r (A B C : 'M_(n, m)) : B <=m: C -> B + A <=m: C + A.
Proof.
by rewrite /Mle => H i j; rewrite !mxE; apply Rplus_le_compat_r.
Qed.

Lemma Madd_lt_compat_l (A B C : 'M_(n, m)) : B <m: C -> A + B <m: A + C.
Proof.
by rewrite /Mlt => H i j; rewrite !mxE; apply Rplus_lt_compat_l.
Qed.

Lemma Madd_lt_le_compat (A B C D : 'M_(n, m)) :
  A <m: B -> C <=m: D -> A + C <m: B + D.
Proof.
move=> HAB HCD i j.
rewrite !mxE; apply Rplus_lt_le_compat; [apply HAB|apply HCD].
Qed.

Lemma Mopp_le_contravar (A B : 'M_(n, m)) : A <=m: B -> - B <=m: - A.
Proof. rewrite /Mle => H i j; rewrite !mxE; apply Ropp_le_contravar, H. Qed.

Lemma Mopp_lt_contravar (A B : 'M_(n, m)) : A <m: B -> - B <m: - A.
Proof. rewrite /Mlt => H i j; rewrite !mxE; apply Ropp_lt_contravar, H. Qed.

Lemma Mscale_le_compat (r : R) (A B : 'M_(n, m)) :
  (0 <= r)%R -> A <=m: B -> r *: A <=m: r *: B.
Proof.
by move=> Hs HAB i j; rewrite !mxE; apply Rmult_le_compat_l; [|apply HAB].
Qed.

Lemma Mscale_lt_reg (r : R) (A B : 'M_n) :
  (0 < r)%Re -> r *: A <m: r *: B -> A <m: B.
Proof.
move=> Hs HsAsB i j.
apply (Rmult_lt_reg_l r _ _ Hs).
by move: (HsAsB i j); rewrite !mxE.
Qed.

Lemma Mle_sub (A B : 'M_(n, m)) : A <=m: B -> 0 <=m: B - A.
Proof. rewrite /Mle => HAB i j; rewrite !mxE; apply Rle_0_minus, HAB. Qed.

Lemma Msub_le (A B : 'M_(n, m)) : 0 <=m: B - A -> A <=m: B.
Proof.
rewrite /Mle => HAB i j.
move: {HAB} (HAB i j); rewrite !mxE => HAB.
apply Rge_le, Rminus_ge, Rle_ge, HAB.
Qed.

Lemma Mlt_sub (A B : 'M_(n, m)) : A <m: B -> 0 <m: B - A.
Proof. rewrite /Mlt => HAB i j; rewrite !mxE; apply Rlt_Rminus, HAB. Qed.

Lemma Msub_lt (A B : 'M_(n, m)) : 0 <m: B - A -> A <m: B.
Proof.
rewrite /Mlt => HAB i j.
move: {HAB} (HAB i j); rewrite !mxE => HAB.
apply Rgt_lt, Rminus_gt, HAB.
Qed.

(** **** Lemmas about matrix multiplication and Mabs, Mle and Mlt. *)
Variable p : nat.

(** Contrary to reals (c.f. [Rabs_mult]), we only have an inequality (which
    comes from the triangular inequality on Rabs [big_Rabs_triang]). *)
Lemma Mabs_mul (A : 'M_(n, p)) (B : 'M_(p, m)) :
  Mabs (A *m B) <=m: Mabs A *m Mabs B.
Proof.
move=> i j; rewrite !mxE.
apply (Rle_trans _ _ _ (big_Rabs_triang _)).
by right; apply /eq_bigr => k _; rewrite !mxE Rabs_mult.
Qed.

Lemma Mmul_le_compat_l (A : 'M_(n, p)) (B C : 'M_(p, m)) :
  0 <=m: A -> B <=m: C -> A *m B <=m: A *m C.
Proof.
move=> HA HBC i j; rewrite !mxE.
apply big_rec2; [by right|]; move=> k x1 x2 _ Hx12.
apply Rplus_le_compat; [|by []].
apply Rmult_le_compat_l; [|by apply HBC].
by move: (HA i k); rewrite mxE.
Qed.

Lemma Mmul_le_compat_r (A : 'M_(p, m)) (B C : 'M_(n, p)) :
  0 <=m: A -> B <=m: C -> B *m A <=m: C *m A.
Proof.
move=> HA HBC i j; rewrite !mxE.
apply big_rec2; [by right|]; move=> k x1 x2 _ Hx12.
apply Rplus_le_compat; [|by []].
apply Rmult_le_compat_r; [|by apply HBC].
by move: (HA k j); rewrite mxE.
Qed.

Lemma Mmul_le_compat (A B : 'M_(n, p)) (C D : 'M_(p, m)) :
  0 <=m: A -> 0 <=m: C -> A <=m: B -> C <=m: D -> A *m C <=m: B *m D.
Proof.
move=> HA HC HAB HCD i j; rewrite !mxE.
apply big_rec2; [by right|]; move=> k x1 x2 _ Hx12.
apply Rplus_le_compat; [|by []].
apply Rmult_le_compat; [| |by apply HAB|by apply HCD].
{ by move: (HA i k); rewrite mxE. }
by move: (HC k j); rewrite mxE.
Qed.

Lemma Mmul_le_pos (A : 'M_(n, p)) (B : 'M_(p, m)) :
  0 <=m: A -> 0 <=m: B -> 0 <=m: A *m B.
Proof. by move=> HA HB; rewrite -(mulmx0 _ A); apply Mmul_le_compat_l. Qed.

(** ** Positive (semi-)definite matrices. *)
End Mabs_order_prop.

Section Pos_def.

Variable n : nat.

Definition semipos (A : 'M_n) := forall (x : 'cV_n), 0 <=m: x^T *m A *m x.

Definition posdef (A : 'M_n) :=
  forall (x : 'cV_n), x <> 0 -> 0 <m: x^T *m A *m x.

Lemma posdef_semipos A : posdef A -> semipos A.
Proof.
rewrite /posdef /semipos => PA x.
case (x =P 0) => Hx.
{ by rewrite Hx mulmx0 => i j; right. }
by apply Mlt_le, PA.
Qed.

(** Any matrix of the form A^T A is positive semi-definite. *)
Lemma mxtrmx_semipos (A : 'M_n) : semipos (A^T *m A).
Proof.
move=> x.
rewrite mulmxA -mulmxA -trmx_mul Mle_scalar !mxE.
apply big_sum_pos_pos => i; rewrite mxE; apply Rle_0_sqr.
Qed.

(** Order on matrices defined by the positive definite cone (A <(=) B if 0 <(=) B - A). *)
Definition Mposdefle (A B : 'M_n) :=
  forall (x : 'cV_n), x^T *m A *m x <=m: x^T *m B *m x.

Definition Mposdeflt (A B : 'M_n) :=
  forall (x : 'cV_n), x <> 0 -> x^T *m A *m x <m: x^T *m B *m x.

End Pos_def.

(** Notations for this order. *)
Infix "<=m" := Mposdefle (at level 70) : R_scope.
Infix "<m" := Mposdeflt (at level 70) : R_scope.

(** ** Any positive definite matrix defines a dotproduct and a quadratic norm. *)

(** *** Lemmas holding also for a positive *semi*-definite matrix. *)
Section Dotprod_normP.

Variable n : nat.

(** A matrix P *)
Variable P : 'M[R]_n.

(** symmetric *)
Hypothesis SymP : P^T = P.

(** and positive semi-definite *)
Hypothesis PP : semipos P.

(** The dotproduct defined by P *)
Definition dotprodP (x y : 'cV_n) : R := (x^T *m P *m y) ord0 ord0.

Lemma dotprodP_pos (x : 'cV_n) : (0 <= dotprodP x x)%Re.
Proof.
replace 0%Re with ((0 : 'M[R]_(1,1)) ord0 ord0); [|by rewrite mxE].
case (x =P 0) => Hx.
{ by rewrite /dotprodP Hx mulmx0; right. }
rewrite -Mle_scalar; apply PP.
Qed.

Lemma dotprodP_sym (x y : 'cV_n) : dotprodP x y = dotprodP y x.
Proof.
rewrite /dotprodP.
by rewrite -{1}SymP -trmx_mul -{1}(trmxK y) -trmx_mul mulmxA trmx_scalar.
Qed.

Lemma dotprodP_0_r (x : 'cV_n) : (dotprodP x 0 = 0)%Re.
Proof. by rewrite /dotprodP mulmx0 mxE. Qed.

Lemma dotprodP_0_l (x : 'cV_n) : (dotprodP 0 x = 0)%Re.
Proof. by rewrite dotprodP_sym dotprodP_0_r. Qed.

Lemma dotprodP_linear_r (x y z : 'cV_n) :
  (dotprodP x (y + z) = dotprodP x y + dotprodP x z)%Re.
Proof. by rewrite /dotprodP mulmxDr mxE. Qed.

Lemma dotprodP_linear_l (x y z : 'cV_n) :
  (dotprodP (x + y) z = dotprodP x z + dotprodP y z)%Re.
Proof.
by rewrite dotprodP_sym (dotprodP_sym x) (dotprodP_sym y) dotprodP_linear_r.
Qed.

Lemma dotprodP_scale_r (r : R) (x y : 'cV_n) :
  (dotprodP x (r *: y) = r * dotprodP x y)%Re.
Proof. by rewrite /dotprodP -scalemxAr mxE. Qed.

Lemma dotprodP_scale_l (r : R) (x y : 'cV_n) :
  (dotprodP (r *: x) y = r * dotprodP x y)%Re.
Proof. by rewrite dotprodP_sym dotprodP_scale_r dotprodP_sym. Qed.

Lemma dotprodP_opp_r (x y : 'cV_n) : (dotprodP x (- y) = - dotprodP x y)%Re.
Proof.
replace (- y) with ((- 1) *: y).
{ by rewrite dotprodP_scale_r Ropp_mult_distr_l_reverse Rmult_1_l. }
by rewrite GRing.scaleN1r.
Qed.

Lemma dotprodP_opp_l (x y : 'cV_n) : (dotprodP (- x) y = - dotprodP x y)%Re.
Proof. by rewrite dotprodP_sym dotprodP_opp_r dotprodP_sym. Qed.

(** The quadratic norm defined by P *)
Definition normP (x : 'cV_n) := sqrt (dotprodP x x).

Lemma normP_sqr_dotprod (x : 'cV_n) : ((normP x)^2 = dotprodP x x)%Re.
Proof. rewrite /normP /= Rmult_1_r sqrt_def //; apply dotprodP_pos. Qed.

Lemma normP_pos (x : 'cV_n) : (0 <= normP x)%Re.
Proof. rewrite /normP; apply sqrt_pos. Qed.

Lemma normP_0 : normP (0 : 'cV_n) = 0.
Proof. by rewrite /normP dotprodP_0_l sqrt_0. Qed.

Lemma normP_opp (x : 'cV_n) : normP (- x) = normP x.
Proof. by rewrite /normP dotprodP_opp_l dotprodP_opp_r Ropp_involutive. Qed.

Lemma normP_scale (r : R) (x : 'cV_n) : (normP (r *: x) = Rabs r * normP x)%Re.
Proof.
rewrite /normP dotprodP_scale_l dotprodP_scale_r -Rmult_assoc.
rewrite sqrt_mult_alt; [|by apply sqr_ge_0].
by rewrite sqrt_Rsqr_abs.
Qed.

Lemma normP_scale_pos (r : R) (x : 'cV_n) :
  (0 <= r -> normP (r *: x) = r * normP x)%Re.
Proof. by move=> H; rewrite normP_scale Rabs_pos_eq. Qed.

(** Cauchy-Schwarz inequality. *)
Lemma cauchy_schwarzP (x y : 'cV_n) : (dotprodP x y <= normP x * normP y)%Re.
Proof.
case (Req_dec (normP y) 0) => Hny.
{ rewrite Hny Rmult_0_r.
  destruct (Req_dec (dotprodP x y) 0) as [Zxy|Nzxy]; [by right|].
  rewrite -(Ropp_involutive (dotprodP _ _)) -Ropp_0; apply Ropp_le_contravar.
  set (lambda := (- ((normP x)^2 / (2 * dotprodP x y) + / 2))%Re).
  replace (- _)%Re with ((normP (x + lambda *: y))^2)%Re; [by apply pow2_ge_0|].
  rewrite normP_sqr_dotprod dotprodP_linear_l !dotprodP_linear_r.
  rewrite !dotprodP_scale_l !dotprodP_scale_r (dotprodP_sym y x).
  rewrite -(normP_sqr_dotprod y) Hny /= Rmult_0_l !Rmult_0_r.
  rewrite -normP_sqr_dotprod /lambda; ring_simplify.
  rewrite Rinv_r; [rewrite Rmult_1_l|lra].
  rewrite (Rmult_comm 2) /Rdiv 2!Rmult_assoc Rinv_l; [ring|].
  by move=> H; apply Nzxy, (Rmult_eq_reg_l 2); [rewrite Rmult_0_r|lra]. }
apply Rabs_le_inv.
rewrite -(Rabs_pos_eq (_ * _)%Re); [|by apply Rmult_le_pos; apply normP_pos].
apply Rsqr_le_abs_0.
rewrite Rsqr_mult.
apply (Rmult_le_reg_r (/ (Rsqr (normP y))));
  [by apply Rinv_0_lt_compat, Rlt_0_sqr|].
rewrite Rmult_assoc Rinv_r; [rewrite Rmult_1_r|by apply Rgt_not_eq, Rlt_0_sqr].
rewrite /Rsqr Rmult_assoc.
set (t0 := (dotprodP x y * / (normP y * normP y))%Re).
apply (Rplus_le_reg_r (dotprodP x y * (- t0))%Re); ring_simplify.
replace (_ + _)%Re
with (normP (x + (- t0)%Re *: y)^2)%Re; [by apply pow2_ge_0|].
rewrite normP_sqr_dotprod.
rewrite dotprodP_linear_l !dotprodP_linear_r.
rewrite (Rplus_comm (- _ * t0)) Rplus_assoc normP_sqr_dotprod.
apply Rplus_eq_compat_l.
rewrite !dotprodP_scale_l !dotprodP_scale_r.
rewrite -!Rmult_plus_distr_l.
rewrite !Ropp_mult_distr_l_reverse; apply Ropp_eq_compat.
rewrite Rmult_comm; apply Rmult_eq_compat_r.
apply (Rplus_eq_reg_r (- dotprodP x y + t0 * dotprodP y y)); ring_simplify.
rewrite /t0 -normP_sqr_dotprod; field_simplify; [|by []].
by rewrite dotprodP_sym.
Qed.

Lemma cauchy_schwarzP_Rabs (x y : 'cV_n) :
  Rabs (dotprodP x y) <= normP x * normP y.
Proof.
apply Rabs_le; split; [|by apply cauchy_schwarzP].
rewrite -(Ropp_involutive (dotprodP _ _)); apply Ropp_le_contravar.
rewrite -dotprodP_opp_l -(normP_opp x); apply cauchy_schwarzP.
Qed.

(** Triangular inequality. *)
Lemma normP_triang (x y : 'cV[R]_n) : (normP (x + y) <= normP x + normP y)%Re.
Proof.
rewrite /normP.
apply Rsqr_incr_0_var; [|by apply Rplus_le_le_0_compat; apply sqrt_pos].
rewrite /Rsqr Rmult_plus_distr_l !Rmult_plus_distr_r.
repeat (try rewrite sqrt_def; [|by apply dotprodP_pos]).
rewrite dotprodP_linear_r !dotprodP_linear_l // dotprodP_sym //.
apply (Rplus_le_reg_r (- dotprodP x x - dotprodP y y)).
ring_simplify.
rewrite Rmult_assoc; apply Rmult_le_compat_l; [lra|].
by rewrite Rmult_comm; apply cauchy_schwarzP.
Qed.

End Dotprod_normP.

(** *** Lemmas holding only for a positive definite matrix. *)
Section Dotprod_normP_def.

Variable n : nat.

Variable P : 'M[R]_n.

Hypothesis SymP : P^T = P.

Hypothesis PP : posdef P.

Lemma dotprodP_def (x : 'cV_n) : dotprodP P x x = 0%Re -> x = 0.
Proof.
rewrite /dotprodP => Px.
case (x =P 0) => Hx //.
casetype False; apply (Rlt_irrefl 0); rewrite -{2}Px.
by replace 0%Re with ((0 : 'M[R]_(1,1)) ord0 ord0); [apply PP|rewrite mxE].
Qed.

Lemma normP_def (x : 'cV_n) : (normP P x = 0)%Re -> x = 0.
Proof.
move=> Hx.
apply dotprodP_def.
by rewrite -(normP_sqr_dotprod (posdef_semipos PP)) Hx /= Rmult_0_l.
Qed.

Lemma normP_def_contrap (x : 'cV_n) : x <> 0 -> (0 < normP P x)%Re.
Proof.
move=> Hx.
elim (normP_pos P x); [by []|move=> Hnx].
by casetype False; apply Hx, normP_def.
Qed.

End Dotprod_normP_def.

(** ** Canonical dotproduct *)
Section DotProd.

Variable n : nat.

Definition dotprod (x y : 'cV_n) : R := (x^T *m y) ord0 ord0.

Lemma dotprod_sum (x y : 'cV_n) :
  (dotprod x y = \sum_i (x i ord0 * y i ord0)%Re)%Re.
Proof.
by rewrite /dotprod /mulmx /trmx mxE; apply /eq_bigr => i; rewrite mxE.
Qed.

(** Link between matrix multiplication and the canonical dotproduct. *)
Lemma mulmx_dotprod m (A : 'M_(m, n)) (B : 'M_(n, m)) (i j : 'I_m) :
  (A *m B) i j = dotprod (col i A^T) (col j B).
Proof.
by rewrite /dotprod /col !mxE; apply /eq_bigr => k _; rewrite /trmx !mxE.
Qed.

(** Link between matrix vector multiplication and the canonical dotproduct. *)
Lemma mulmxv_dotprod m (A : 'M_(m, n)) (x : 'cV_n) (i : 'I_m) :
  (A *m x) i ord0 = dotprod (col i A^T) x.
Proof.
by rewrite /dotprod /col !mxE; apply /eq_bigr => k _; rewrite /trmx !mxE.
Qed.

(** The canonical dotproduct is the dotproduct defined by the identity matrix [M1]. *)
Definition M1 : 'M[R]_n := 1%:M.

Lemma SymM1 : M1^T = M1.
Proof. apply trmx1. Qed.

Lemma PdM1 : posdef M1.
Proof.
rewrite /posdef => x Hx; rewrite mulmx1 Mlt_scalar !mxE.
have H : (forall i, (0 <= x^T ord0 i * x i ord0)%Re).
{ move=> i'; rewrite mxE; apply Rle_0_sqr. }
have Ps : (0 <= \sum_i (x^T ord0 i * x i ord0)%Re)%Re by apply big_sum_pos_pos.
case (Req_dec (\sum_i (x^T ord0 i * x i ord0)%Re) 0) => Hs.
{ casetype False; apply Hx.
  rewrite -colP => i; rewrite mxE.
  by apply Rsqr_0_uniq; move: (big_sum_pos_eq_0 H Hs i); rewrite mxE. }
by apply Rnot_le_lt => H'; apply Hs, Rle_antisym.
Qed.

Lemma PM1 : semipos M1.
Proof. apply posdef_semipos, PdM1. Qed.

Lemma dotprodP1 (x y : 'cV_n) : dotprod x y = dotprodP M1 x y.
Proof. by rewrite /dotprod /dotprodP mulmx1. Qed.

(** We then get the same lemmas. *)
Lemma dotprod_pos (x : 'cV_n) : (0 <= dotprod x x)%Re.
Proof. rewrite dotprodP1; apply dotprodP_pos, PM1. Qed.

Lemma dotprod_def (x : 'cV_n) : dotprod x x = 0 -> x = 0.
Proof. rewrite dotprodP1; apply dotprodP_def, PdM1. Qed.

Lemma dotprod_sym (x y : 'cV_n) : dotprod x y = dotprod y x.
Proof. rewrite !dotprodP1; apply dotprodP_sym, SymM1. Qed.

Lemma dotprod_0_r (x : 'cV_n) : (dotprod x 0 = 0)%Re.
Proof. by rewrite /dotprod mulmx0 mxE. Qed.

Lemma dotprod_0_l (x : 'cV_n) : (dotprod 0 x = 0)%Re.
Proof. by rewrite dotprod_sym dotprod_0_r. Qed.

Lemma dotprod_linear_r (x y z : 'cV_n) :
  (dotprod x (y + z) = dotprod x y + dotprod x z)%Re.
Proof. by rewrite /dotprod mulmxDr mxE. Qed.

Lemma dotprod_linear_l (x y z : 'cV_n) :
  (dotprod (x + y) z = dotprod x z + dotprod y z)%Re.
Proof. rewrite !dotprodP1; apply dotprodP_linear_l, SymM1. Qed.

Lemma dotprod_scale_r (r : R) (x y : 'cV_n) :
  (dotprod x (r *: y) = r * dotprod x y)%Re.
Proof. by rewrite /dotprod -scalemxAr mxE. Qed.

Lemma dotprod_scale_l (r : R) (x y : 'cV_n) :
  (dotprod (r *: x) y = r * dotprod x y)%Re.
Proof. by rewrite dotprod_sym dotprod_scale_r dotprod_sym. Qed.

Lemma dotprod_opp_r (x y : 'cV_n) : (dotprod x (- y) = - dotprod x y)%Re.
Proof. rewrite !dotprodP1; apply dotprodP_opp_r. Qed.

Lemma dotprod_opp_l (x y : 'cV_n) : (dotprod (- x) y = - dotprod x y)%Re.
Proof. by rewrite dotprod_sym dotprod_opp_r dotprod_sym. Qed.

End DotProd.

(** *** Norm 1 and norm 2. *)
Definition norm1 n (x : 'cV_n) : R := \sum_i Rabs (x i ord0).

Definition norm2 n (x : 'cV_n) := sqrt (dotprod x x).

Notation "`|| x ||_1" := (norm1 x) (format "`|| x ||_1") : R_scope.
Notation "`|| x ||_2" := (norm2 x) (format "`|| x ||_2") : R_scope.

Section Norm2.

Variable n : nat.

(** The norm 2 is the quadratic norm defined by the identity matrix. *)
Lemma normP1 (x : 'cV_n) : norm2 x = normP (M1 n) x.
Proof. by rewrite /norm2 /normP dotprodP1. Qed.

(** We then get the same lemmas. *)
Lemma norm2_sqr_dotprod (x : 'cV_n) : (`||x||_2^2 = dotprod x x)%Re.
Proof. rewrite normP1 dotprodP1; apply normP_sqr_dotprod, PM1. Qed.

Lemma norm2_pos (x : 'cV_n) : (0 <= `||x||_2)%Re.
Proof. rewrite /norm2; apply sqrt_pos. Qed.

Lemma norm2_0 : `||0 : 'cV_n||_2 = 0.
Proof. by rewrite /norm2 dotprod_0_l sqrt_0. Qed.

Lemma norm2_def (x : 'cV_n) : (`||x||_2 = 0)%Re -> x = 0.
Proof. rewrite normP1; apply normP_def, PdM1. Qed.

Lemma norm2_def_contrap (x : 'cV_n) : x <> 0 -> (0 < `||x||_2)%Re.
Proof. rewrite normP1; apply normP_def_contrap, PdM1. Qed.

Lemma norm2_opp (x : 'cV_n) : `||- x||_2 = `||x||_2.
Proof. rewrite !normP1; apply normP_opp, SymM1. Qed.

Lemma norm2_scale (r : R) (x : 'cV_n) : (`||r *: x||_2 = Rabs r * `||x||_2)%Re.
Proof. rewrite !normP1; apply normP_scale, SymM1. Qed.

Lemma norm2_scale_pos (r : R) (x : 'cV_n) :
  (0 <= r -> `||r *: x||_2 = r * `||x||_2)%Re.
Proof. rewrite !normP1; apply normP_scale_pos, SymM1. Qed.

Lemma cauchy_schwarz (x y : 'cV_n) : (dotprod x y <= `||x||_2 * `||y||_2)%Re.
Proof.
rewrite !normP1 dotprodP1; apply cauchy_schwarzP; [apply SymM1|apply PM1].
Qed.

Lemma cauchy_schwarz_Rabs (x y : 'cV_n) :
  Rabs (dotprod x y) <= `||x||_2 * `||y||_2.
Proof.
rewrite !normP1 dotprodP1; apply cauchy_schwarzP_Rabs; [apply SymM1|apply PM1].
Qed.

Lemma norm2_triang (x y : 'cV[R]_n) : (`||x + y||_2 <= `||x||_2 + `||y||_2)%Re.
Proof. rewrite !normP1; apply normP_triang; [apply SymM1|apply PM1]. Qed.

(** The following lemmas don't generally hold for any quadratic norm but they
    do for [norm2].  *)
Lemma Mle_norm2 (x y : 'cV[R]_n) : Mabs x <=m: Mabs y -> (`||x||_2 <= `||y||_2)%Re.
Proof.
move=> Hxy.
rewrite /norm2 /dotprod.
apply sqrt_le_1; rewrite !mxE.
{ apply big_sum_pos_pos => i; rewrite mxE; apply Rle_0_sqr. }
{ apply big_sum_pos_pos => i; rewrite mxE; apply Rle_0_sqr. }
apply big_rec2; [by right|move=> i y1 y2 _ Hy12; rewrite !mxE].
by apply Rplus_le_compat;
  [apply Rsqr_le_abs_1; move: (Hxy i ord0); rewrite !mxE|].
Qed.

Lemma norm2_mabs (x : 'cV_n) : `||Mabs x||_2 = `||x||_2.
Proof.
rewrite /norm2; apply f_equal.
rewrite /dotprod !mxE; apply /eq_bigr => k _.
rewrite !mxE /GRing.mul /= -Rabs_mult; apply Rabs_pos_eq, sqr_ge_0.
Qed.

Lemma norm2_const : `||\col_(k < n) 1||_2 = sqrt (INR n).
Proof.
rewrite /norm2 dotprod_sum /=.
replace (\sum_i _ : R) with (\sum_(i < n) 1%Re);
  [|by apply /eq_bigr => i; rewrite mxE Rmult_1_l].
by rewrite big_sum_const Rmult_1_r.
Qed.

Lemma norm1_le_sqrt_norm2 (x : 'cV_n) : (`||x||_1 <= sqrt (INR n) * `||x||_2)%Re.
Proof.
replace (`||x||_1) with (dotprod (\col__ 1) (Mabs x));
  [|by rewrite /dotprod /norm1 mxE;
    apply /eq_bigr => i; rewrite !mxE /GRing.mul /= Rmult_1_l].
apply (Rle_trans _ _ _ (cauchy_schwarz _ _)).
by rewrite norm2_const norm2_mabs; right.
Qed.

End Norm2.

(** ** Frobenius norm for matrices. *)
Section FrobeniusNorm_def.

Variable n m : nat.

Definition normFrobenius (M : 'M[R]_(n, m)) :=
  sqrt (\sum_i \sum_j ((M i j) * (M i j))%Re).

End FrobeniusNorm_def.

Notation "`|| M ||_F" := (normFrobenius M) (format "`|| M ||_F") : R_scope.

Section FrobeniusNorm.

Variable n m : nat.

Lemma norm21_le_sqrt_normF (M : 'M[R]_(n, m)) :
  (`||\col_i (\sum_j Rabs (M i j))||_2 <= sqrt (INR m) * `||M||_F)%Re.
Proof.
apply (Rle_trans _ (`||\col_i (sqrt (INR m)
                              * sqrt (\sum_j (M i j) * (M i j)))%Re||_2)).
{ apply Mle_norm2 => i j; rewrite !mxE.
  rewrite Rabs_pos_eq; [|by apply big_sum_Rabs_pos].
  rewrite Rabs_pos_eq; [|by apply Rmult_le_pos; apply sqrt_pos].
  replace (\sum_j Rabs (M i j)) with (`||\col_j M i j||_1);
    [|by apply /eq_bigr => j'; rewrite mxE].
  replace (sqrt (\sum__ _)) with (`||\col_j M i j||_2);
    [|by rewrite /norm2 /dotprod mxE; apply f_equal;
      apply /eq_bigr => j'; rewrite !mxE].
  apply norm1_le_sqrt_norm2. }
right.
rewrite /norm2 /normFrobenius -sqrt_mult;
  [|by apply pos_INR
   |by apply big_sum_pos_pos => i; apply big_sum_pos_pos => j; apply Rle_0_sqr].
apply f_equal; rewrite big_distrr /= /dotprod mxE.
apply /eq_bigr => i _; rewrite !mxE.
rewrite -sqrt_mult;
  [|by apply pos_INR|by apply big_sum_pos_pos => i'; apply Rle_0_sqr].
rewrite /GRing.mul /= sqrt_def //; apply Rmult_le_pos; [by apply pos_INR|].
apply big_sum_pos_pos => i'; apply Rle_0_sqr.
Qed.

End FrobeniusNorm.

(** ** Some additional lemmas about strict pointwise order and matrix multiplication. *)
Section Mabs_order_mul_lt_prop.

Lemma dotprod_pos_eq_0_r n (x y : 'cV_n) :
  0 <m: x -> 0 <=m: y -> (dotprod x y = 0)%Re -> y = 0.
Proof.
move=> Hx Hy Hdp; rewrite -matrixP => i j; rewrite mxE (ord_1_0 j).
apply (Rmult_eq_reg_l (x i ord0)); [rewrite Rmult_0_r|].
{ move: Hdp i; rewrite dotprod_sum; apply big_sum_pos_eq_0 => i.
  apply Rmult_le_pos.
  { apply Rle_trans with ((0 : 'cV_n) i ord0); [by right; rewrite mxE|].
    apply Rlt_le, Hx. }
  apply Rle_trans with ((0 : 'cV_n) i ord0); [by right; rewrite mxE|].
  apply Hy. }
apply Rgt_not_eq, Rlt_gt.
apply Rle_lt_trans with ((0 : 'cV_n) i ord0); [by right; rewrite mxE|].
apply Hx.
Qed.

Lemma dotprod_pos_eq_0_l n (x y : 'cV_n) :
  0 <=m: x -> 0 <m: y -> (dotprod x y = 0)%Re -> x = 0.
Proof.
by move=> Hx Hy; rewrite dotprod_sym; apply dotprod_pos_eq_0_r.
Qed.

Lemma Mmulv_lt_compat_r n m (A : 'cV_m) (B C : 'M_(n, m)) :
  0 <=m: A -> A <> 0 -> B <m: C -> B *m A <m: C *m A.
Proof.
move=> HA1 HA2 HBC.
have H : (B *m A <=m: C *m A)%Re by apply Mmul_le_compat_r; [|apply Mlt_le].
move=> i j.
rewrite /Mle in H; move: {H} (H i j) => H.
destruct H; [by []|].
casetype False; apply HA2.
have H' : (((C - B) *m A) i j = 0)%Re.
{ by rewrite mulmxBl mxE -H !mxE; apply Rminus_diag_eq. }
move: H'; rewrite (ord_1_0 j) mulmxv_dotprod; apply dotprod_pos_eq_0_r.
{ move: HBC; rewrite /Mlt => HBC i' j'; rewrite !mxE.
  apply Rlt_Rminus, HBC. }
exact HA1.
Qed.

Lemma Mmulv_lt_compat_l n m (A : 'cV_m) (B C : 'M_(m, n)) :
  0 <=m: A -> A <> 0 -> B <m: C -> A^T *m B <m: A^T *m C.
Proof.
move=> HA1 HA2 HBC.
rewrite -(trmxK B) -(trmxK C) -!trmx_mul.
by apply Mlt_tr in HBC; apply Mlt_tr, Mmulv_lt_compat_r.
Qed.

(** Vectors of norm 1 are enough to test positive definiteness. *)
Lemma posdef_norm_eq_1 n (A : 'M_n) :
  (forall (x : 'cV_n), `||x||_2 = 1 -> 0 <m: x^T *m A *m x) -> posdef A.
Proof.
move=> HA x Hx.
have Hinx := Rinv_0_lt_compat _ (norm2_def_contrap Hx).
apply (Mscale_lt_reg Hinx); rewrite GRing.scaler0 scalemxAr.
apply (Mscale_lt_reg Hinx); rewrite GRing.scaler0 !scalemxAl -scale_trmx.
apply HA.
rewrite norm2_scale_pos; [|by apply Rlt_le].
by rewrite Rinv_l; [|apply Rgt_not_eq, norm2_def_contrap].
Qed.

End Mabs_order_mul_lt_prop.
