(** * Application: Impact of floating-point rounding errors on a Lyapunov stability proof. *)

Require Import Reals Fcore_Raux.

Require Import misc.

Require Import Psatz.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun ssralg matrix bigop.

Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import real_matrix.

Require Import gamma fsum fdotprod.

Section Fellipsoid_error.

Variable fs : Float_spec.

(** Sum [\sum a_i b_i] computed in float from left to right
    with a_i \in R, b_i \in F. *)
Definition fdotprod_l2r_fstr (k : nat) (a : R ^ k) (b : F fs ^ k) : F fs :=
  fdotprod_l2r [ffun i => frnd fs (a i)] b.

Lemma fdotprod_l2r_fstr_eq k (a1 : R ^ k) (b1 : F fs ^ k)
      (a2 : R ^ k) (b2 : F fs ^ k) :
  (forall i, a1 i = a2 i) -> (forall i, b1 i = b2 i :> R) ->
  fdotprod_l2r_fstr a1 b1 = fdotprod_l2r_fstr a2 b2 :> R.
Proof.
by move=> Ha Hb; apply fsum_l2r_eq => i; rewrite !ffunE /fmult Ha Hb.
Qed.

Lemma fdotprod_l2r_fstr_r k (a : R ^ k.+2) (b : F fs ^ k.+2) :
  fdotprod_l2r_fstr a b
  = fplus (fdotprod_l2r_fstr [ffun i : 'I_k.+1 => a (inord i)]
                             [ffun i : 'I_k.+1 => b (inord i)])
          (fmult (frnd fs (a (inord k.+1))) (b (inord k.+1))) :> R.
Proof.
rewrite /fdotprod_l2r_fstr fdotprod_l2r_r.
rewrite /fplus; do 2 apply f_equal; apply f_equal2.
{ by apply fsum_l2r_eq => i; rewrite !ffunE. }
by rewrite ffunE.
Qed.

Lemma fdotprod_l2r_fstr_err_gamma k (Hk : 2 * INR k.+1 * eps fs < 1)
      (a : R ^ k) (b : F fs ^ k) :
  exists oa : (b_gamma fs k.+1 * (b_eta fs * b_eta fs)) ^ k,
  (fdotprod_l2r_fstr a b
   = \sum_i (a i * b i + (oa i).1 * (a i * b i)
             + 2 * ((oa i).2.2 + (oa i).2.1 * b i))%Re :> R)%Re.
Proof.
case: k Hk a b => [|k] Hk a b.
{ exists [ffun=> (b_gamma_0 (bg_2 Hk), (eta_0 fs, eta_0 fs))].
  by rewrite big_ord0 /fdotprod_l2r_fstr /fdotprod_l2r /fsum_l2r. }
set (a' := [ffun i : 'I_k.+1 => frnd fs (a i)]).
have [oa Hoa] := fdotprod_l2r_err_gamma (bg_2S Hk) a' b.
set (F := fun i : 'I_k.+1 => (a' i * b i + (oa i).1 * (a' i * b i)
                              + 2 * (oa i).2)%Re).
set (F' := fun (i : 'I_k.+1) (ode : b_gamma fs k.+2 * (b_eta fs * b_eta fs)) =>
             (a i * b i + ode.1 * (a i * b i)
              + 2 * (ode.2.2 + ode.2.1 * b i))%Re).
have H : forall i, exists e, F i = F' i e.
{ move=> i.
  have [d [e Hde]] := frnd_spec fs (a i).
  have [o1 Ho1] := gammap1_mult_epsp1 Hk (oa i).1 d.
  have H : (Rabs (1 + (oa i).1) <= Rabs 2)%Re.
  { case (oa i).1 => oai Hoai /=.
    rewrite Rabs_pos_eq.
    { rewrite Rabs_right; [|lra].
      apply (Rplus_le_reg_r (- 1)); ring_simplify.
      apply Rlt_le, (Rle_lt_trans _ _ _ (proj2 (Rabs_le_inv _ _ Hoai))).
      by apply gamma_lt_1, bg_2S. }
    apply (Rplus_le_reg_r (- 1)); ring_simplify.
    apply Rle_trans with (- (gamma fs k.+1))%Re; [|by apply (Rabs_le_inv oai)].
    by apply Ropp_le_contravar, Rlt_le, gamma_lt_1, bg_2S. }
  have [o2 Ho2] := bounded_larger_factor (Rlt_le _ _ (eta_pos fs)) e H.
  exists (o1, (o2, (oa i).2)).
  rewrite /F /F' /a' ffunE Hde /=.
  replace (a i * _ + o1 * _)%Re with ((1 + o1) * (a i * b i))%Re by ring.
  replace (2 * (_ + _))%Re with (2 * (oa i).2 + o2 * 2 * b i)%Re by ring.
  rewrite -Ho1 -Ho2; ring. }
have [ea Hea] := big_exists 0%R +%R
                            (b_gamma_0 (bg_2 Hk), (eta_0 fs, eta_0 fs)) H.
exists ea.
by rewrite /F /F' in Hea; rewrite -Hea -Hoa.
Qed.

Lemma fdotprod_l2r_fstr_err k (Hk : 2 * INR k.+1 * eps fs < 1)
      (a : R ^ k) (b : F fs ^ k) :
  exists o : b_gamma fs k.+1, exists e : b_eta fs, exists e' : b_eta fs,
  (fdotprod_l2r_fstr a b
   = \sum_i (a i * b i)%Re + o * (\sum_i Rabs (a i * b i)%Re)
     + 2 * INR k * e + 2 * e' * (\sum_i Rabs (b i)) :> R)%Re.
Proof.
have [oa Hoa] := fdotprod_l2r_fstr_err_gamma Hk a b.
have [o' Ho'] := big_bounded_distrl (gamma_pos (bg_2 Hk)) [ffun i => (oa i).1]
                                    [ffun i => (a i * b i)%Re].
have [e He] := big_bounded_distrl (Rlt_le _ _ (eta_pos fs))
                                  [ffun i => (oa i).2.2] [ffun=> 2].
have [e' He'] := big_bounded_distrl (Rlt_le _ _ (eta_pos fs))
                                    [ffun i => (oa i).2.1]
                                    [ffun i => (2 * b i)%Re].
exists o'; exists e; exists e'.
replace (\sum__ (Rabs _)) with (\sum_i Rabs ([ffun i => (a i * b i)%Re] i));
  [|by apply /eq_bigr => i _; rewrite ffunE].
rewrite (Rmult_comm 2 e') (Rmult_assoc e') (big_distrr 2) /=.
replace (\sum__ (2 * Rabs _)%Re)
with (\sum_i Rabs ([ffun i => (2 * b i)%Re] i));
  [|by apply /eq_bigr => i _; rewrite ffunE Rabs_mult Rabs_right; [|lra]].
rewrite (Rmult_comm _ e) (Rmult_comm 2) -big_sum_const.
replace (\sum__ 2) with (\sum_(i < k) Rabs ([ffun=> 2] i));
  [|by apply /eq_bigr => i _; rewrite ffunE Rabs_right; [|lra]].
rewrite -Ho' -He -He'.
rewrite Hoa !big_split -big_distrr big_split /=.
rewrite GRing.mulrDr !(big_distrr 2) GRing.addrA /=.
apply f_equal2; [apply f_equal2; [apply f_equal2|]|]; apply /eq_bigr => i _;
(try rewrite !ffunE /GRing.mul /=); (try reflexivity); ring.
Qed.

Lemma lemma_2_aux1 n (x : 'cV_n.+1) (i : 'I_n.+1) :
  (Rabs (x i ord0) <= ||x||_2)%Re.
Proof.
apply Rsqr_incr_0_var; [|by apply norm2_pos].
replace (Rsqr ||x||_2) with (||x||_2^2); [|by rewrite /= Rmult_1_r].
rewrite norm2_sqr_dotprod dotprod_sum.
rewrite (bigD1 i) /= //.
rewrite -(Rplus_0_r (Rsqr _)) -Rsqr_abs; apply Rplus_le_compat_l.
apply big_sum_pred_pos_pos; move=> i' _; apply Rle_0_sqr.
Qed.

Lemma lemma_2_aux2 n (P : 'M_n.+1) : posdef P ->
  forall (s : R), 1%:M <=m s *: P -> 0 <= s.
Proof.
move=> PP s Hs.
case (Rle_or_lt 0 s) => Hs' //.
casetype False; apply (Rlt_irrefl 0).
set (x := \col_(i < n.+1) 1%Re); specialize (Hs x).
have Nzx : x <> 0.
{ rewrite -matrixP /x; move=> H.
  specialize (H ord0 ord0); move: H; rewrite !mxE; apply R1_neq_R0. }
apply (Rlt_le_trans _ ((x^T *m x) ord0 ord0)).
{ rewrite -/(dotprod x x) -norm2_sqr_dotprod.
  replace (_ ^ 2) with (Rsqr ||x||_2); [|by rewrite /= Rmult_1_r].
  by apply Rlt_0_sqr, Rgt_not_eq, norm2_def_contrap. }
move: Hs; rewrite mulmx1 Mle_scalar => Hs; apply (Rle_trans _ _ _ Hs).
rewrite /posdef in PP; specialize (PP x Nzx).
rewrite -scalemxAr -scalemxAl mxE.
apply Ropp_le_cancel; rewrite Ropp_0 -Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
{ by rewrite -Ropp_0; apply Ropp_le_contravar, Rlt_le. }
move: PP; rewrite Mlt_scalar mxE; apply Rlt_le.
Qed.

Lemma lemma_2_aux3 n (P : 'M_n) (PP : posdef P) (x : 'cV_n) (lambda : R) :
  (x^T *m P *m x <=m: lambda%:M)%Re -> (0 <= lambda)%Re.
Proof.
set (xPx := ((x^T *m P *m x) ord0 ord0)).
move=> Hlambda.
apply (Rle_trans _ xPx); [|by move: Hlambda; rewrite Mle_scalar -/xPx mxE].
case (x =P 0) => Hx.
{ by rewrite /xPx Hx mulmx0 mxE; right. }
replace 0%Re with ((0 : 'M[R]_(1,1)) ord0 ord0); [|by rewrite mxE].
by rewrite -Mle_scalar; specialize (PP x Hx); apply Mlt_le.
Qed.

Lemma lemma_2 n (P : 'M[R]_n) : posdef P ->
  forall s : R, 1%:M <=m s *: P ->
  forall (x : 'cV_n) (lambda : R),
  (x^T *m P *m x <=m: lambda%:M)%Re ->
  forall i : 'I_n, (Rabs (x i ord0) <= sqrt (s * lambda))%Re.
Proof.
case: n P => [|n] P PP s HP x lambda Hx i; [by case i|].
apply (Rle_trans _ _ _ (lemma_2_aux1 _ _)).
apply Rsqr_incr_0_var; [|by apply sqrt_pos].
rewrite /Rsqr sqrt_def.
{ apply (Rle_trans  _ ((x^T *m (s *: P) *m x) ord0 ord0)).
  { replace (_ * _)%Re with (||x||_2^2); [|by rewrite /= Rmult_1_r].
    by move: (HP x); rewrite mulmx1 norm2_sqr_dotprod -Mle_scalar. }
  rewrite -scalemxAr -scalemxAl mxE; apply Rmult_le_compat_l;
  [by apply (lemma_2_aux2 PP)|].
  replace lambda with (lambda%:M (@ord0 0) ord0); [|by rewrite mxE].
  by rewrite -Mle_scalar. }
by apply Rmult_le_pos; [apply (lemma_2_aux2 PP)|apply (lemma_2_aux3 PP Hx)].
Qed.

(** A x + B u computed in float (from left to right). *)
Definition fAxBu (n p : nat)
           (A : 'M[R]_n) (x : 'cV[F fs]_n)
           (B : 'M[R]_(n, p)) (u : 'cV[F fs]_p) :=
  \col_i (fdotprod_l2r_fstr
            [ffun k => row_mx A B i k] [ffun k => col_mx x u k ord0]).

Definition MF2R : forall m n : nat, 'M[F fs]_(m, n) -> 'M[R]_(m, n) :=
  map_mx (@F_val (format fs)).

Lemma lemma_3_aux1 n (x y z : 'cV_n) :
  (forall i : 'I_n, exists d : bounded 1,
     x i ord0 = y i ord0 + (d : R) * z i ord0) ->
  exists d : (bounded 1)^n, x = y + diag_mx (\row_i (d i : R)) *m z.
Proof.
elim: n x y z => [|n IHn] x y z Hxyz.
{ exists [ffun=> bounded_0 Rle_0_1].
  by rewrite -colP; case. }
set (x' := dsubmx (x : 'cV_(1+n))).
set (y' := dsubmx (y : 'cV_(1+n))).
set (z' := dsubmx (z : 'cV_(1+n))).
have H : forall i : 'I_n, exists d : bounded 1,
           x' i ord0 = y' i ord0 + (d : R) * z' i ord0.
{ move=> i.
  have [d Hd] := Hxyz (rshift 1 i).
  exists d.
  by rewrite !mxE. }
have [d' Hd'] := IHn x' y' z' H.
have [d0 Hd0] := Hxyz ord0.
exists [ffun i : 'I_(1+n) => match split i with
                               | inl _ => d0
                               | inr ir => d' ir end].
rewrite -colP => i.
rewrite mul_diag_mx !mxE ffunE.
case splitP => i' Hi'.
{ by replace i with (@ord0 n); [|apply ord_inj; rewrite Hi' (ord_1_0 i')]. }
move: Hd'; rewrite mul_diag_mx -colP => Hd'; specialize (Hd' i'); move: Hd'.
by replace i with (rshift 1 i'); [rewrite !mxE|apply ord_inj; rewrite Hi'].
Qed.

Lemma lemma_3_aux2_aux1 n (P : 'M[R]_n) : posdef P ->
  forall (x : 'cV[F fs]_n),
  forall (s lambda : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  1%:M <=m s *: P ->  
  exists b : bounded 1,
  (\big[+%R/0]_i Rabs (x i ord0) = b * INR n * sqrt (s * lambda))%Re.
Proof.
move=> PP x s lambda Hlambda Hs.
set (F := fun k : 'I_n => Rabs (x k ord0)).
set (F' := fun (k : 'I_n) (b : bounded 1) =>
             (b * [ffun=> sqrt (s * lambda)] k)%Re).
have HFx : forall k : 'I_n, exists b : bounded 1, F k = F' k b.
{ move=> k.
  have [b Hb] := bounded_le_1_abs (lemma_2 PP Hs Hlambda k).
  exists b.
  by rewrite /F /F' ffunE -Hb mxE. }
have [ba Hba] := big_exists 0%R +%R (bounded_0 Rle_0_1) HFx.
have [b Hb] := big_bounded_distrl Rle_0_1 ba [ffun=> sqrt (s * lambda)].
exists b.
rewrite Hba -(Rabs_pos_eq (sqrt _)); [|by apply sqrt_ge_0].
rewrite Hb Rmult_assoc -big_sum_const.
by apply /Rmult_eq_compat_l /eq_bigr => i _; rewrite ffunE.
Qed.

Lemma lemma_3_aux2_aux2 p (u : 'cV[F fs]_p) : Mabs (MF2R u) <=m: \col__ 1%Re ->
  exists b : bounded 1,
  (\big[+%R/0]_i Rabs (u i ord0) = b * INR p)%Re.
Proof.
move=> Hu.
set (F := fun k : 'I_p => Rabs (u k ord0)).
set (F' := fun (k : 'I_p) (b : bounded 1) => (b * [ffun=> 1%Re] k)%Re).
have HFu : forall k : 'I_p, exists b : bounded 1, F k = F' k b.
{ move=> k.
  move: (Hu k ord0); rewrite !mxE => Huk.
  have [b Hb] := bounded_le_1_abs Huk.
  exists b.
  by rewrite /F /F' Hb ffunE. }
have [ba Hba] := big_exists 0%R +%R (bounded_0 Rle_0_1) HFu.
have [b Hb] := big_bounded_distrl Rle_0_1 ba [ffun=> 1%Re].
exists b.
rewrite Hba Hb -(Rmult_1_r (INR p)) -big_sum_const.
by apply /Rmult_eq_compat_l /eq_bigr => i _; rewrite ffunE Rabs_right; [|lra].
Qed.

Lemma lemma_3_aux2 n p (Hnp : 2 * INR (n + p).+1 * eps fs < 1) :
  forall (P : 'M[R]_n), posdef P ->
  forall (A : 'M[R]_n) (B : 'M[R]_(n, p)) (x : 'cV[F fs]_n) (u : 'cV[F fs]_p),
  forall (s lambda : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  Mabs (MF2R u) <=m: \col__ 1%Re ->
  1%:M <=m s *: P ->
  exists b : bounded 1,
  (\big[+%R/0]_i Rabs ([ffun k => (col_mx x u) k ord0] i)
   = b * (sqrt (s * lambda) * INR n + INR p))%Re.
Proof.
move=> P PP A B x u s lambda Hlambda Hu Hs.
have [bx Hbx] := lemma_3_aux2_aux1 PP Hlambda Hs.
have [bu Hbu] := lemma_3_aux2_aux2 Hu.
have [b Hb] := bounded_distrl Rle_0_1
                              bx bu (sqrt (s * lambda) * INR n)%Re (INR p).
exists b.
rewrite big_split_ord /=.
rewrite -(Rabs_pos_eq (sqrt _ * _));
  [|by apply Rmult_le_pos; [apply sqrt_ge_0|apply pos_INR]].
rewrite -(Rabs_pos_eq (INR p)); [|by apply pos_INR].
rewrite -Hb; apply f_equal2.
{ rewrite (Rmult_comm (sqrt _)) -Rmult_assoc -Hbx.
  by apply /eq_bigr => i _; rewrite ffunE col_mxEu. }
by rewrite -Hbu; apply /eq_bigr => i _; rewrite ffunE col_mxEd.
Qed.

Lemma lemma_3_aux3_aux1 n (P : 'M[R]_n) : posdef P ->
  forall (A : 'M[R]_n) (x : 'cV[F fs]_n),
  forall (s lambda : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  1%:M <=m s *: P ->
  forall i : 'I_n,
  exists b : bounded 1,
  (\big[+%R/0]_k Rabs (A i k * x k ord0)
   = b * sqrt (s * lambda) * \sum_k Rabs (A i k))%Re.
Proof.
move=> PP A x s lambda Hlambda Hs i.
set (F := fun k : 'I_n => Rabs (A i k * x k ord0)).
set (F' := fun (k : 'I_n) (b : bounded 1) =>
             (b * [ffun k => (sqrt (s * lambda) * Rabs (A i k))%Re] k)%Re).
have HFx : forall k : 'I_n, exists b : bounded 1, F k = F' k b.
{ move=> k.
  have [b Hb] := bounded_le_1_abs (lemma_2 PP Hs Hlambda k).
  exists b.
  by rewrite /F /F' ffunE Rmult_comm -Rmult_assoc Rabs_mult -Hb mxE. }
have [ba Hba] := big_exists 0%R +%R (bounded_0 Rle_0_1) HFx.
have [b Hb] := big_bounded_distrl
                 Rle_0_1 ba
                 [ffun k => (sqrt (s * lambda) * Rabs (A i k))%Re].
exists b.
rewrite Hba -(Rabs_pos_eq (sqrt _)); [|by apply sqrt_ge_0].
rewrite Hb Rmult_assoc; apply Rmult_eq_compat_l.
rewrite big_distrr /=.
by apply /eq_bigr => i' _; rewrite ffunE Rabs_mult Rabs_Rabsolu.
Qed.

Lemma lemma_3_aux3_aux2 n p (B : 'M[R]_(n, p)) (u : 'cV[F fs]_p) :
  Mabs (MF2R u) <=m: \col__ 1%Re ->
  forall (i : 'I_n),
  exists b : bounded 1,
  (\big[+%R/0]_k Rabs (B i k * u k ord0) = b * \sum_k Rabs (B i k))%Re.
Proof.
move=> Hu i.
set (F := fun k : 'I_p => Rabs (B i k * u k ord0)).
set (F' := fun (k : 'I_p) (b : bounded 1) =>
             (b * [ffun k => Rabs (B i k)] k)%Re).
have HFu : forall k : 'I_p, exists b : bounded 1, F k = F' k b.
{ move=> k.
  move: (Hu k ord0); rewrite !mxE => Huk.
  have [b Hb] := bounded_le_1_abs Huk.
  exists b.
  by rewrite /F /F' ffunE Rabs_mult Hb Rmult_1_r Rmult_comm. }
have [ba Hba] := big_exists 0%R +%R (bounded_0 Rle_0_1) HFu.
have [b Hb] := big_bounded_distrl Rle_0_1 ba [ffun k => Rabs (B i k)].
exists b.
rewrite Hba Hb.
by apply /Rmult_eq_compat_l /eq_bigr => i' _; rewrite ffunE Rabs_Rabsolu.
Qed.

Lemma lemma_3_aux3 n p (Hnp : 2 * INR (n + p).+1 * eps fs < 1) (P : 'M[R]_n) :
  posdef P ->
  forall (A : 'M[R]_n) (B : 'M[R]_(n, p)) (x : 'cV[F fs]_n) (u : 'cV[F fs]_p),
  forall (s lambda : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  Mabs (MF2R u) <=m: \col__ 1 ->
  1%:M <=m s *: P ->
  forall (i : 'I_n),
  exists b : bounded 1,
  (\big[+%R/0]_i0 Rabs
    ([ffun k => (row_mx A B) i k] i0 * [ffun k => (col_mx x u) k ord0] i0)
   = b * (sqrt (s * lambda) * (\sum_k Rabs (A i k))
          + (\sum_k Rabs (B i k))))%Re.
Proof.
move=> PP A B x u s lambda Hlambda Hu Hs i.
have [bx Hbx] := lemma_3_aux3_aux1 PP A Hlambda Hs i.
have [bu Hbu] := lemma_3_aux3_aux2 B Hu i.
have [b Hb] := bounded_distrl
                 Rle_0_1 bx bu (sqrt (s * lambda) * \sum_k Rabs (A i k))%Re
                 (\sum_k Rabs (B i k)).
exists b.
rewrite big_split_ord /=.
rewrite -(Rabs_pos_eq (sqrt _ * _));
  [|by apply Rmult_le_pos; [apply sqrt_ge_0|apply big_sum_Rabs_pos]].
rewrite -(Rabs_pos_eq (\sum_k Rabs (B i k))); [|by apply big_sum_Rabs_pos].
rewrite -Hb; apply f_equal2.
{ rewrite -Rmult_assoc -Hbx.
  by apply /eq_bigr => i' _; rewrite !ffunE row_mxEl col_mxEu. }
by rewrite -Hbu; apply /eq_bigr => i' _; rewrite !ffunE row_mxEr col_mxEd.
Qed.

Lemma lemma_3 n p (Hnp : 2 * INR (n + p).+1 * eps fs < 1) (P : 'M[R]_n) :
  posdef P ->
  forall (A : 'M[R]_n) (B : 'M[R]_(n, p)) (x : 'cV[F fs]_n) (u : 'cV[F fs]_p),
  forall (s lambda : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  Mabs (MF2R u) <=m: \col__ 1%Re ->
  1%:M <=m s *: P ->
  exists d : (bounded 1)^n,
  MF2R (fAxBu A x B u)
  = A *m (MF2R x) + B *m (MF2R u)
    + diag_mx (\row_i (d i : R))
      *m ((sqrt lambda *: (sqrt s *: ((gamma fs (n + p).+1
                                             *: \col_i \sum_j Rabs (A i j))
                                      + (2 * INR n) *: \col__ (eta fs))))
          + (gamma fs (n + p).+1 *: \col_i \sum_j Rabs (B i j))
          + (2 * INR (n + 2 * p)) *: \col__ (eta fs)).
Proof.
case: n p Hnp P => [|n] p Hnp P PP A B x u s lambda Hlambda Hu Hs.
{ exists [ffun=> bounded_0 Rle_0_1].
  by rewrite -matrixP; case. }
apply lemma_3_aux1 => i.
have [o [e [e' Hoee']]] := fdotprod_l2r_fstr_err
                             Hnp [ffun k => (row_mx A B) i k]
                             [ffun k => (col_mx x u) k ord0].
have [o1 Ho1] := bounded_scale o Rlt_0_1.
have [o2 Ho2] := lemma_3_aux3 Hnp PP A B Hlambda Hu Hs i.
have [e1 He1] := bounded_scale e Rlt_0_1.
have [e'1 He'1] := bounded_scale e' Rlt_0_1.
have [e'2 He'2] := lemma_3_aux2 Hnp PP A B Hlambda Hu Hs.
set (r1 := (gamma fs (n.+1 + p).+1 * ((sqrt (s * lambda) * \sum_k Rabs (A i k))
                                   + \sum_k Rabs (B i k)))%Re).
set (r2 := (2 * INR (n.+1 + p) * eta fs)%Re).
set (r3 := (2 * eta fs * (sqrt (s * lambda) * INR n.+1 + INR p))%Re).
have [d' Hd'] := bounded_distrl Rle_0_1 (bounded_mult_1_l o1 o2) e1 r1 r2.
have [d Hd] := bounded_distrl Rle_0_1 d' (bounded_mult_1_l e'1 e'2)
                              (r1 + r2)%Re r3.
exists d.
rewrite !mxE Hoee' {Hoee'}.
rewrite 2!Rplus_assoc; apply f_equal2.
{ rewrite big_split_ord /=; apply f_equal2; apply /eq_bigr => i' _.
  { by rewrite !ffunE row_mxEl col_mxEu mxE. }
  by rewrite !ffunE row_mxEr col_mxEd mxE. }
rewrite Ho1 Ho2 (Rmult_assoc o1) /Rdiv Rinv_1 Rmult_1_r.
rewrite -(Rmult_assoc _ o2) (Rmult_comm _ o2) (Rmult_assoc o2) -/r1.
rewrite He1 -(Rmult_assoc o1) /Rdiv Rinv_1 Rmult_1_r.
rewrite (Rmult_comm e1) -(Rmult_assoc _ _ e1) (Rmult_comm _ e1) -/r2.
rewrite He'1 He'2 /Rdiv Rinv_1 Rmult_1_r -(Rplus_assoc (_ * r1)).
replace (2 * _ * _)%Re with (e'1 * e'2 * r3)%Re; [|by rewrite /r3; ring].
have Pr1 : (0 <= r1)%Re.
{ apply Rmult_le_pos; [by apply gamma_pos, bg_2|].
  apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [apply sqrt_pos|]|];
  apply big_sum_Rabs_pos. }
have Pr2 : (0 <= r2)%Re.
{ apply Rmult_le_pos;
  [apply Rmult_le_pos; [lra|apply pos_INR]|apply Rlt_le, eta_pos]. }
have Pr3 : (0 <= r3)%Re.
{ apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply Rlt_le, eta_pos]|].
  apply Rplus_le_le_0_compat;
  [apply Rmult_le_pos; [apply sqrt_pos|]|]; apply pos_INR. }
rewrite Hd' Rabs_pos_eq // Rabs_pos_eq //.
rewrite Hd Rabs_pos_eq; [|by apply Rplus_le_le_0_compat].
rewrite Rabs_pos_eq // /r1 /r2 /r3 sqrt_mult;
  [|by apply (lemma_2_aux2 PP)|by apply (lemma_2_aux3 PP Hlambda)].
by rewrite !plus_INR /GRing.mul /GRing.add /=; ring.
Qed.

Lemma lemma_4_aux1 n (P : 'M_n.+1) : semipos P ->
  forall (s' : R), P <=m s' *: 1%:M ->
  (0 <= s')%Re.
Proof.
move=> PP s Hs.
set (x := \col_(i < n.+1) (/ sqrt (INR n.+1))%Re); specialize (Hs x).
apply (Rle_trans _ ((x^T *m P *m x) ord0 ord0)).
{ replace 0%Re with ((0 : 'M[R]_(1,1)) ord0 ord0); [|by rewrite mxE].
  by apply PP. }
apply (Rle_trans _ _ _ (Hs ord0 ord0)); right.
rewrite -scalemxAr -scalemxAl mxE -{2}(Rmult_1_r s); apply f_equal2; [by []|].
rewrite mulmx1.
rewrite -/(dotprod x x) -norm2_sqr_dotprod.
have Hsn : (0 < sqrt (INR n.+1))%Re.
{ apply sqrt_lt_R0, lt_0_INR, lt_0_Sn. }
rewrite /x.
replace (||_||_2) with 1%Re; [by simpl; ring|apply sym_eq].
have H : (0 < sqrt (INR n.+1))%Re.
{ apply sqrt_lt_R0; rewrite S_INR; move: (pos_INR n); lra. }
apply (Rmult_eq_reg_l (sqrt (INR n.+1))); [rewrite Rmult_1_r|lra].
apply eq_trans with (||\col_(_ < n.+1) 1||_2); [|by apply norm2_const].
rewrite -{1}(Rabs_right (sqrt _)); [|lra]; rewrite -norm2_scale.
apply f_equal; rewrite -matrixP => i j; rewrite !mxE; apply Rinv_r; lra.
Qed.

Lemma lemma_4 n (P : 'M[R]_n) : semipos P ->
  forall (s' : R), P <=m s' *: 1%:M ->
  forall (d : (bounded 1)^n) (x : 'cV_n),
  (normP P ((diag_mx (\row_i (d i : R))) *m x) <= sqrt s' * ||x||_2)%Re.
Proof.
case: n P => [|n] P PP s' Hs' d x.
{ rewrite /normP /dotprodP /norm2 /dotprod !mxE !big_ord0 sqrt_0 Rmult_0_r.
  by right. }
set (D := diag_mx (\row_i (d i : R))).
apply (Rle_trans _ (sqrt (((D *m x)^T *m (s' *: (D *m x))) ord0 ord0))).
{ rewrite /normP; apply sqrt_le_1_alt; rewrite -Mle_scalar.
  by move: (Hs' (D *m x)); rewrite -!scalemxAr mulmx1 -scalemxAl. }
apply (Rle_trans _ (sqrt (s' * ||D *m x||_2^2))%Re).
{ apply sqrt_le_1_alt.
  rewrite -scalemxAr mxE norm2_sqr_dotprod /dotprod.
  by right. }
rewrite sqrt_mult; [|by apply (lemma_4_aux1 PP)|by apply pow2_ge_0].
apply Rmult_le_compat_l; [by apply sqrt_pos|].
rewrite /pow /= Rmult_1_r sqrt_square; [|by apply norm2_pos].
apply Mle_norm2.
rewrite /D mul_diag_mx; move=> i j; rewrite !mxE Rabs_mult.
rewrite -{2}(Rmult_1_l (Rabs (_ _ _))).
by apply Rmult_le_compat_r; [apply Rabs_pos|case (d i)].
Qed.

Lemma lemma_4_sqr n (P : 'M[R]_n) : semipos P ->
  forall (s' : R), P <=m s' *: 1%:M ->
  forall (d : (bounded 1)^n) (x : 'cV_n),
  ((x^T *m (diag_mx (\row_i (d i : R)))^T *m P
    *m (diag_mx (\row_i (d i : R))) *m x)%Ri ord0 ord0
   <= s' * ||x||_2^2)%Re.
Proof.
case: n P => [|n] P PP s' Hs' d x.
{ rewrite /norm2 /dotprod !mxE !big_ord0 sqrt_0 /pow Rmult_0_l Rmult_0_r.
  by right. }
apply sqrt_le_0.
{ replace 0%Re with ((0 : 'M[R]_(1,1)) ord0 ord0); [|by rewrite mxE].
  by rewrite -Mle_scalar -trmx_mul -mulmxA. }
{ apply Rmult_le_pos; [|by apply pow2_ge_0].
  by apply (lemma_4_aux1 PP). }
rewrite sqrt_mult; [|by apply (lemma_4_aux1 PP)|by apply pow2_ge_0].
rewrite /pow Rmult_1_r sqrt_square; [|by apply sqrt_pos].
rewrite -trmx_mul -mulmxA.
by apply lemma_4.
Qed.

Theorem ellipsoid_error n p (Hnp : 2 * INR (n + p).+1 * eps fs < 1) :
  forall (P : 'M[R]_n), P^T = P -> posdef P ->
  forall (A : 'M[R]_n) (B : 'M[R]_(n, p)) (x : 'cV[F fs]_n) (u : 'cV[F fs]_p),
  forall (s s' lambda lambda' : R),
  ((MF2R x)^T *m P *m (MF2R x) <=m: lambda%:M)%Re ->
  Mabs (MF2R u) <=m: \col__ 1%Re ->
  (A *m MF2R x + B *m MF2R u)^T
  *m P *m (A *m MF2R x + B *m MF2R u) <=m: lambda'%:M ->
  1%:M <=m s *: P -> P <=m s' *: 1%:M ->
  let a := (gamma fs (n + p).+1 * sqrt (s * s') * sqrt (INR n) * ||A||_F
            + 2 * sqrt (s * s') * INR n * sqrt (INR n) * eta fs)%Re in
  let b := (gamma fs (n + p).+1 * sqrt s' * sqrt (INR p) * ||B||_F
            + 2 * sqrt s' * INR (n + 2 * p) * sqrt (INR n) * eta fs)%Re in
  ((MF2R (fAxBu A x B u))^T *m P *m (MF2R (fAxBu A x B u))) ord0 ord0
  <= (sqrt lambda' + sqrt lambda * a + b)^2.
Proof.
case: n p Hnp => [|n] p Hnp P SymP PP A B x u s s' lambda lambda'.
{ move=> _ _ _ _ _ /=.
  by rewrite !mxE !big_ord0; apply pow2_ge_0. }
set (y := A *m MF2R x + B *m MF2R u).
set (fy := MF2R (fAxBu A x B u)).
set (r := sqrt s *: (gamma fs (n.+1 + p).+1 *: (\col_i \sum_j Rabs (A i j))
                     + (2 * INR n.+1)%Re *: \col__ (eta fs))).
set (f := gamma fs (n.+1 + p).+1 *: (\col_i \sum_j Rabs (B i j))
          + (2 * INR (n.+1 + 2 * p))%Re *: \col__ (eta fs)).
move=> Hlambda Hu Hlambda' Hs Hs'.
set (a := (gamma fs (n.+1 + p).+1 * sqrt (s * s') * sqrt (INR n.+1) * ||A||_F
           + 2 * sqrt (s * s') * INR n.+1 * sqrt (INR n.+1) * eta fs)%Re).
set (b := (gamma fs (n.+1 + p).+1 * sqrt s' * sqrt (INR p) * ||B||_F)%Re).
set (c := (sqrt s' * 2 * INR (n.+1 + 2 * p) * sqrt (INR n.+1) * eta fs)%Re).
replace (_ * eta _)%Re with c; [|by rewrite /c; ring].
simpl.
have [d Hd] := lemma_3 Hnp PP A B Hlambda Hu Hs.
set (D := diag_mx (\row_i (d i : R))).
have HD : fy = y + D *m (sqrt lambda *: r + f).
{ by rewrite /fy Hd -/y -GRing.addrA. }
move {Hd}.
apply (Rle_trans _ ((y^T *m P *m y + lambda *: (r^T *m D^T *m P *m D *m r)
                     + f^T *m D^T *m P *m D *m f
                     + 2 *: (sqrt lambda *: (r^T *m D^T *m P *m D *m f))
                     + 2 *: (y^T *m P *m D *m (sqrt lambda *: r))
                     + 2 *: (y^T *m P *m D *m f))%Ri ord0 ord0)).
{ right.
  rewrite -eq_scalar.
  rewrite HD.
  rewrite (mulmx_sum_sum SymP).
  rewrite (mulmxA (y^T *m P) D).
  rewrite (mulmxDr (y^T *m P *m D) _ f).
  rewrite GRing.scalerDr GRing.addrA.
  apply f_equal2; [|by []]; apply f_equal2; [|by []].
  rewrite -!GRing.addrA; apply f_equal2; [by []|].
  rewrite mulmxDr (mulmx_sum_sum SymP).
  rewrite -GRing.addrA; apply f_equal2.
  { rewrite - 2! scalemxAr scale_trmx -!scalemxAl GRing.scalerA.
    rewrite /GRing.mul /= sqrt_def; [|by apply (lemma_2_aux3 PP Hlambda)].
    apply f_equal2; [by []|].
    by rewrite trmx_mul mulmxA. }
  apply f_equal2; [by rewrite trmx_mul mulmxA|].
  apply f_equal2; [by []|].
  rewrite -scalemxAr scale_trmx -!scalemxAl.
  apply f_equal2; [by []|].
  by rewrite trmx_mul mulmxA. }
apply (Rle_trans _ (((y^T *m P *m y + lambda *: (r^T *m D^T *m P *m D *m r)
                      + f^T *m D^T *m P *m D *m f)%Ri ord0 ord0
                     + 2 * sqrt lambda * normP P (D *m r) * normP P (D *m f)
                     + 2 * sqrt lambda * normP P y * normP P (D *m r)
                     + 2 * normP P y * normP P (D *m f))%Re)).
{ rewrite mxE.
  apply Rplus_le_compat.
  { rewrite mxE.
    apply Rplus_le_compat.
    { rewrite mxE.
      apply Rplus_le_compat; [by right|].
      rewrite 2!mxE /GRing.mul /= !Rmult_assoc.
      apply Rmult_le_compat_l; [lra|].
      apply Rmult_le_compat_l; [by apply sqrt_pos|].
      rewrite -trmx_mul -mulmxA.
      by apply (cauchy_schwarzP SymP (posdef_semipos PP)). }
    rewrite -scalemxAr.
    rewrite 2!mxE /GRing.mul /= !Rmult_assoc.
    apply Rmult_le_compat_l; [lra|].
    apply Rmult_le_compat_l; [by apply sqrt_pos|].
    rewrite -(mulmxA _ D).
    by apply (cauchy_schwarzP SymP (posdef_semipos PP)). }
  rewrite mxE /GRing.mul /= Rmult_assoc.
  apply Rmult_le_compat_l; [lra|].
  rewrite -(mulmxA _ D).
  by apply (cauchy_schwarzP SymP (posdef_semipos PP)). }
apply (Rle_trans _ ((y^T *m P *m y)%Ri ord0 ord0 + lambda * s' * ||r||_2^2
                    + s' * ||f||_2^2 + 2 * sqrt lambda * s' * ||r||_2 * ||f||_2
                    + 2 * sqrt lambda * sqrt s' * normP P y * ||r||_2
                    + 2 * sqrt s' * normP P y * ||f||_2)).
{ apply Rplus_le_compat.
  { apply Rplus_le_compat.
    { apply Rplus_le_compat.
      { rewrite mxE.
        apply Rplus_le_compat.
        { rewrite mxE.
          apply Rplus_le_compat_l.
          rewrite mxE /GRing.mul /= Rmult_assoc.
          apply Rmult_le_compat_l; [by apply (lemma_2_aux3 PP Hlambda)|].
            by apply (lemma_4_sqr (posdef_semipos PP)). }
          by apply (lemma_4_sqr (posdef_semipos PP)). }
      rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
      apply Rmult_le_compat_l; [by apply sqrt_pos|].
      rewrite -(sqrt_def s'); [|by apply (lemma_4_aux1 (posdef_semipos PP))].
      replace (_ * _ * _)%Re
      with ((sqrt s' * ||r||_2) * (sqrt s' * ||f||_2))%Re by ring.
      apply Rmult_le_compat; [by apply normP_pos|by apply normP_pos
                              |by apply (lemma_4 (posdef_semipos PP))
                              |by apply (lemma_4 (posdef_semipos PP))]. }
    rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
    apply Rmult_le_compat_l; [by apply sqrt_pos|].
    replace (_ * (_ * _))%Re with (normP P y * (sqrt s' * ||r||_2))%Re by ring.
    by apply Rmult_le_compat_l;
      [apply normP_pos|apply (lemma_4 (posdef_semipos PP))]. }
  rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  replace (_ * (_ * _))%Re with (normP P y * (sqrt s' * ||f||_2))%Re by ring.
  by apply Rmult_le_compat_l;
    [apply normP_pos|apply (lemma_4 (posdef_semipos PP))]. }
apply (Rle_trans _ (lambda' + lambda * s' * ||r||_2^2 + s' * ||f||_2^2
                    + 2 * s' * sqrt lambda * ||r||_2 * ||f||_2
                    + 2 * sqrt s' * sqrt lambda * sqrt lambda' * ||r||_2
                    + 2 * sqrt s' * sqrt lambda' * ||f||_2)%Re).
{ apply Rplus_le_compat.
  { apply Rplus_le_compat.
    { apply Rplus_le_compat.
      { do 2 apply Rplus_le_compat_r.
        by replace lambda' with (lambda'%:M (@ord0 0) ord0); [|rewrite mxE]. }
      right; ring. }
    rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
    replace (_ * _)%Re
    with (sqrt s' * (sqrt lambda * (normP P y * ||r||_2)))%Re by ring.
    do 2 (apply Rmult_le_compat_l; [by apply sqrt_pos|]).
    apply Rmult_le_compat_r; [by apply norm2_pos|].
    by apply sqrt_le_1_alt; replace lambda' with (lambda'%:M (@ord0 0) ord0);
      [apply Hlambda'|rewrite mxE]. }
  rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  apply Rmult_le_compat_l; [by apply sqrt_pos|].
  apply Rmult_le_compat_r; [by apply norm2_pos|].
  by apply sqrt_le_1_alt; replace lambda' with (lambda'%:M (@ord0 0) ord0);
    [apply Hlambda'|rewrite mxE]. }
have Plambda' : (0 <= lambda').
{ rewrite -Mle_scalar_mx.
  apply (@Mle_trans _ _ _ (y^T *m P *m y)); [|by []].
  apply (@Mle_trans _ _ _ 0); [|by apply posdef_semipos].
  by move=> i j; rewrite !mxE (ord_1_0 i) (ord_1_0 j); right. }
apply (Rle_trans _ ((sqrt lambda' + sqrt lambda * sqrt s' * ||r||_2
                     + sqrt s' * ||f||_2)^2)%Re).    
{ right.
  rewrite /pow !Rmult_1_r.
  rewrite !Rmult_plus_distr_l !Rmult_plus_distr_r !Rmult_1_l.
  rewrite sqrt_def; [|by []].
  replace (sqrt lambda * sqrt s' * ||r||_2 * (_ * ||r||_2))%Re
  with ((sqrt lambda * sqrt lambda) * (sqrt s' * sqrt s')
        * ||r||_2 * ||r||_2)%Re by ring.
  replace (sqrt s' * ||f||_2 * (sqrt lambda * sqrt s' * ||r||_2))%Re
  with ((sqrt s' * sqrt s') * sqrt lambda * ||r||_2 * ||f||_2)%Re by ring.
  replace (sqrt lambda * sqrt s' * ||r||_2 * (sqrt s' * ||f||_2))%Re
  with ((sqrt s' * sqrt s') * sqrt lambda * ||r||_2 * ||f||_2)%Re by ring.
  replace (sqrt s' * ||f||_2 * (sqrt s' * ||f||_2))%Re
  with ((sqrt s' * sqrt s') * ||f||_2 * ||f||_2)%Re by ring.
  rewrite sqrt_def; [|by apply (lemma_2_aux3 PP Hlambda)].
  rewrite sqrt_def; [|by apply (lemma_4_aux1 (posdef_semipos PP))].
  ring. }
rewrite /pow !Rmult_1_r.
have H0 : (sqrt lambda' + sqrt lambda * sqrt s' * ||r||_2 + sqrt s' * ||f||_2
           <= sqrt lambda' + sqrt lambda * a + b + c)%Re.
{ rewrite (Rplus_assoc _ b c).
  apply Rplus_le_compat.
  { apply Rplus_le_compat_l.
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [by apply sqrt_pos|].
    rewrite /a sqrt_mult;
      [|by apply (lemma_2_aux2 PP)
       |by apply (lemma_4_aux1 (posdef_semipos PP))].
    replace (_ + _)%Re
    with (sqrt s' * (sqrt s * (gamma fs (n.+1 + p).+1
                               * sqrt (INR n.+1) * ||A||_F
                               + 2 * INR n.+1 * sqrt (INR n.+1) * eta fs)))%Re
      by ring.
    apply Rmult_le_compat_l; [by apply sqrt_pos|].
    rewrite /r norm2_scale Rabs_pos_eq; [|by apply sqrt_pos].
    apply Rmult_le_compat_l; [by apply sqrt_pos|].
    apply (Rle_trans _ _ _ (norm2_triang _ _)), Rplus_le_compat.
    { rewrite norm2_scale Rabs_pos_eq; [|by apply gamma_pos, bg_2].
      rewrite Rmult_assoc; apply Rmult_le_compat_l; [by apply gamma_pos, bg_2|].
      apply norm21_le_sqrt_normF. }
    rewrite norm2_scale Rabs_pos_eq;
      [|by apply Rmult_le_pos; [lra|apply pos_INR]].
    rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
    apply Rmult_le_compat_l; [by apply pos_INR|].
    rewrite -{2}(Rabs_pos_eq (eta fs)); [|by apply Rlt_le, eta_pos].
    right; rewrite Rmult_comm -norm2_const -norm2_scale.
    by apply f_equal; rewrite -matrixP => i j; rewrite !mxE GRing.mulr1. }
  rewrite /f /b /c.
  replace (_ + _ * eta fs)%Re
  with (sqrt s' * (gamma fs (n.+1 + p).+1 * sqrt (INR p) * ||B||_F
                   + 2 * INR (n.+1 + 2 * p) * sqrt (INR n.+1) * eta fs))%Re
    by ring.
  apply Rmult_le_compat_l; [by apply sqrt_pos|].
  apply (Rle_trans _ _ _ (norm2_triang _ _)), Rplus_le_compat.
  { rewrite norm2_scale Rabs_pos_eq; [|by apply gamma_pos, bg_2].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [by apply gamma_pos, bg_2|].
    apply norm21_le_sqrt_normF. }
  rewrite norm2_scale_pos; [|by apply Rmult_le_pos; [lra|apply pos_INR]].
  right; rewrite !Rmult_assoc; do 2 apply Rmult_eq_compat_l.
  rewrite -norm2_const Rmult_comm -{2}(Rabs_pos_eq (eta fs));
    [rewrite -norm2_scale|by apply Rlt_le, eta_pos].
  by apply f_equal; rewrite -matrixP => i j; rewrite !mxE GRing.mulr1. }
have H1 : (0 <= sqrt lambda' + sqrt lambda * sqrt s' * ||r||_2
                + sqrt s' * ||f||_2)%Re.
{ apply Rplus_le_le_0_compat.
  { apply Rplus_le_le_0_compat; [by apply sqrt_pos|].
    apply Rmult_le_pos; [by apply Rmult_le_pos; apply sqrt_pos|].
    by apply norm2_pos. }
  by apply Rmult_le_pos; [apply sqrt_pos|apply norm2_pos]. }
by rewrite -Rplus_assoc; apply Rmult_le_compat.
Qed.

(** ** Another similar result. *)

Definition x1 (n : nat) (x : 'cV[F fs]_n) :=
  (castmx (addn1 n, erefl 1%N) (col_mx x (\col__ (F1 fs)))).

(** $A [x 1]^T$#A [x 1]^T# computed in float (from left to right). *)
Definition fAx1 (n : nat) (A : 'M[R]_n.+1) (x : 'cV[F fs]_n) :=
  \col_i (fdotprod_l2r_fstr [ffun k => A i k] [ffun k => (x1 x) k ord0]).

Lemma lemma_5 n (Hn : 2 * INR n.+2 * eps fs < 1)
      (A : 'M[R]_n.+1) (x : 'cV[F fs]_n) :
  exists d : (bounded 1)^n.+1,
  MF2R (fAx1 A x)
  = A *m MF2R (x1 x)
    + diag_mx (\row_i (d i : R))
      *m (\col_i (gamma fs n.+2
                  * (Mabs (row i A) *m Mabs (MF2R (x1 x))) ord0 ord0
                  + 2 * (INR n + 2 + ||MF2R x||_1) * eta fs)%Re).
Proof.
apply lemma_3_aux1 => i.
have [o [e [e' Hoee']]] := fdotprod_l2r_fstr_err
                             Hn [ffun k => A i k] [ffun k => (x1 x) k ord0].
have [o1 Ho1] := bounded_scale o Rlt_0_1.
have [e1 He1] := bounded_scale e Rlt_0_1.
have [e'1 He'1] := bounded_scale e' Rlt_0_1.
set (r1 := (gamma fs n.+2
            * (\big[+%R/0]_i0 Rabs ([ffun k => A i k] i0
                                    * [ffun k => (x1 x) k ord0] i0)))%Re).
set (r2 := (2 * INR (n.+1) * eta fs)%Re).
set (r3 := (2 * eta fs * \big[+%R/0]_i Rabs ([ffun k => (x1 x) k ord0] i))%Re).
have [d' Hd'] := bounded_distrl Rle_0_1 e1 e'1 r2 r3.
have [d Hd] := bounded_distrl Rle_0_1 o1 d' r1 (r2 + r3)%Re.
exists d.
rewrite !mxE Hoee' {Hoee'}.
rewrite 2!Rplus_assoc; apply f_equal2.
{ by apply /eq_bigr => i' _; rewrite !ffunE mxE. }
rewrite Ho1 He1 He'1 /Rdiv Rinv_1 !Rmult_1_r.
replace (o1 * _ * _)%Re with (o1 * r1)%Re; [|by rewrite /r1 Rmult_assoc].
replace (_ * (e1 * eta _))%Re with (e1 * r2)%Re; [|rewrite /r2; ring].
replace (2 * (e'1 * _) * _)%Re with (e'1 * r3)%Re;
  [|by rewrite /r3 -!Rmult_assoc (Rmult_comm e'1)].
have Pr1 : (0 <= r1)%Re.
{ apply Rmult_le_pos; [by apply gamma_pos, bg_2|].
  apply big_sum_Rabs_pos. }
have Pr2 : (0 <= r2)%Re.
{ apply Rmult_le_pos;
  [apply Rmult_le_pos; [lra|apply pos_INR]|apply Rlt_le, eta_pos]. }
have Pr3 : (0 <= r3)%Re.
{ apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply Rlt_le, eta_pos]|].
  apply big_sum_Rabs_pos. }
rewrite Hd' Rabs_pos_eq // Rabs_pos_eq // Hd Rabs_pos_eq //.
rewrite Rabs_pos_eq; [|by apply Rplus_le_le_0_compat].
apply f_equal2; [by []|apply f_equal2].
{ rewrite /r1; apply f_equal2; [by []|].
  by apply /eq_bigr => i' _; rewrite !mxE !ffunE Rabs_mult. }
rewrite /r2 /r3 !Rmult_assoc -Rmult_plus_distr_l.
apply f_equal2; [by []|].
rewrite (Rmult_comm (eta _)) -Rmult_plus_distr_r.
apply f_equal2; [|by []].
rewrite -(Rplus_assoc _ 1) (Rplus_assoc _ 1) -S_INR.
apply f_equal2; [by []|].
rewrite big_ord_recr /=.
rewrite Rplus_comm; apply f_equal2.
{ apply /eq_bigr => i' _.
  apply f_equal; rewrite ffunE /x1 mxE.
  rewrite castmxE cast_ord_id /=.
  replace (cast_ord _ _ : 'I_(n+1)) with (lshift 1 i'); [|by apply ord_inj].
  by rewrite col_mxEu. }
rewrite ffunE castmxE cast_ord_id /=.
replace (cast_ord _ _ : 'I_(n+1)) with (rshift n (@ord0 0)).
{ by rewrite col_mxEd mxE Rabs_R1. }
by apply ord_inj; rewrite /= addn0.
Qed.

Theorem assignment_error n (Hn : 2 * INR n.+2 * eps fs < 1) (P A : 'M[R]_n.+1) :
  P^T = P -> semipos P ->
  forall (s b : R), P <=m s *: 1%:M ->
  forall (x : 'cV[F fs]_n),
  let x1 := MF2R (x1 x) in
  let e := \col_i (gamma fs n.+2 * (Mabs (row i A) *m Mabs x1) ord0 ord0
                   + 2 * (INR n + 2 + ||MF2R x||_1) * eta fs)%Re in
  (s * ||e||_2^2 <= b)%Re ->
  (x1^T *m A^T *m P *m A *m x1) ord0 ord0
  <= ((sqrt b - sqrt s * ||e||_2)^2)%Re ->
  ((MF2R (fAx1 A x))^T *m P *m (MF2R (fAx1 A x))) ord0 ord0 <= b.
Proof.
move=> SymP PP s b Hs x /=.
set (x2 := MF2R (x1 x)).
set (e := \col_i (gamma fs n.+2 * (Mabs (row i A) *m Mabs x2) ord0 ord0 +
                  2 * (INR n + 2 + ||MF2R x||_1) * eta fs)%Re).
simpl in e; fold e.
change (_ * (||e||_2 * 1))%Re with (||e||_2^2)%Re.
set (y := A *m x2).
rewrite -trmx_mul -mulmxA; change (A *m x2) with y.
move=> Hs' Hy.
have [d Hd] := lemma_5 Hn A x.
rewrite Hd {Hd}.
fold x2 y; change (\col__ _) with e.
set (D := diag_mx (\row_i (d i : R))).
rewrite (mulmx_sum_sum SymP).
apply Rle_trans with ((y^T *m P *m y + (D *m e)^T *m P *m (D *m e)) ord0 ord0
                      + 2 * normP P y * normP P (D *m e)).
{ rewrite mxE; apply Rplus_le_compat_l.
  rewrite mxE /GRing.mul /= Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  by apply cauchy_schwarzP. }
apply Rle_trans with ((y^T *m P *m y) ord0 ord0 + s * ||e||_2^2
                      + 2 * normP P y * (sqrt s * ||e||_2))%Re.
{ rewrite mxE /GRing.add /= !Rplus_assoc; apply Rplus_le_compat_l.
  apply Rplus_le_compat.
  { rewrite trmx_mul /D.
    change (_ * (_ * 1))%Re with (||e||_2^2).
    by rewrite mulmxA; apply lemma_4_sqr. }
  rewrite /GRing.mul /= !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  apply Rmult_le_compat_l; [by apply normP_pos|].
  by apply lemma_4. }
have Hy' : (normP P y <= sqrt b - sqrt s * ||e||_2)%Re.
{ apply Rle_trans with (sqrt ((sqrt b - sqrt s * ||e||_2)^2)); [|right].
  { by apply sqrt_le_1_alt. }
  rewrite /= Rmult_1_r sqrt_square; [by []|].
  apply Rle_0_minus.
  replace (||e||_2) with (sqrt (||e||_2^2)).
  { rewrite -sqrt_mult; [|by apply (lemma_4_aux1 PP)|by apply pow2_ge_0].
    by apply sqrt_le_1_alt. }
  rewrite /= Rmult_1_r.
  by rewrite sqrt_square; [|apply norm2_pos]. }
apply Rle_trans
with ((sqrt b - sqrt s * ||e||_2)^2 + s * ||e||_2^2
      + 2 * (sqrt b - sqrt s * ||e||_2) * (sqrt s * ||e||_2))%Re; [|right].
{ apply Rplus_le_compat; [by apply Rplus_le_compat_r|].
  rewrite !Rmult_assoc; apply Rmult_le_compat_l; [lra|].
  by apply Rmult_le_compat_r;
    [by apply Rmult_le_pos; [apply sqrt_ge_0|apply norm2_pos]|]. }
ring_simplify; rewrite /= !Rmult_1_r.
rewrite sqrt_def; [rewrite sqrt_def; [ring|]|].
{ by apply (lemma_4_aux1 PP). }
apply Rle_trans with (s * ||e||_2^2)%Re; [|exact Hs'].
by apply Rmult_le_pos; [apply (lemma_4_aux1 PP)|apply pow2_ge_0].
Qed.

End Fellipsoid_error.
