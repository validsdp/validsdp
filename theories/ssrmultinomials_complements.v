(* TODO: review and submit a PR to Ssrmultinomials *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.
From mathcomp Require Import fintype tuple ssralg bigop.
From SsrMultinomials Require Import mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Lemma map_mpolyC (R S : ringType) (f : {additive R -> S}) n c :
  map_mpoly f c%:MP_[n] = (f c)%:MP_[n].
Proof. by rewrite /map_mpoly mmapC. Qed.

Lemma map_mpolyX (R S : ringType) (f : {rmorphism R -> S}) n (m : 'X_{1..n}) :
  map_mpoly f 'X_[m] = 'X_[m].
Proof. by rewrite /map_mpoly mmapX mmap1_id. Qed.

Lemma map_mpolyZ n (R S : ringType) (f : {rmorphism R -> S})
      (c : R) (p : {mpoly R[n]}) :
  map_mpoly f (c *: p) = (f c) *: (map_mpoly f p).
Proof.
apply /mpolyP => m.
by rewrite mcoeff_map_mpoly !mcoeffZ mcoeff_map_mpoly /= rmorphM.
Qed.

Lemma msupp_map_mpoly n (R S : ringType)
      (f : {rmorphism R -> S}) (injf : injective f) (p : {mpoly R[n]}) :
  perm_eq (msupp (map_mpoly f p)) (msupp p).
Proof.
rewrite /map_mpoly /mmap.
set s := BigOp.bigop _ _ _.
have -> : s = \big[+%R/0%R]_(m <- msupp p) (f p@_m *: 'X_[m]).
{ by apply eq_bigr => m _; rewrite /= mmap1_id mul_mpolyC. }
apply (msupp_sumX (msupp_uniq _)).
by move=> m; rewrite mcoeff_msupp (rmorph_eq_nat _ O injf).
Qed.

Lemma map_mpoly_comp (n k : nat) (R S : ringType)
      (f : {rmorphism R -> S}) (injf : injective f)
      (lq : n.-tuple {mpoly R[k]}) (p : {mpoly R[n]}) :
  map_mpoly f (p \mPo lq) = (map_mpoly f p) \mPo (map_tuple (map_mpoly f) lq).
Proof.
apply /mpolyP => m.
rewrite mcoeff_map_mpoly !raddf_sum (eq_big_perm _ (msupp_map_mpoly injf p)) /=.
apply eq_bigr => m' _; rewrite mcoeff_map_mpoly !mcoeffCM rmorphM; f_equal.
rewrite /mmap1 -mcoeff_map_mpoly rmorph_prod; f_equal.
by apply eq_bigr => i _; rewrite tnth_map rmorphX.
Qed.

Lemma comp_mpoly_meval (n k : nat) (R : comRingType)
      (lq : n.-tuple {mpoly R[k]}) (p : {mpoly R[n]}) (v : 'I_k -> R) :
  (p \mPo lq).@[v] = p.@[fun i => (tnth lq i).@[v]].
Proof.
rewrite comp_mpolyEX {3}(mpolyE p) !raddf_sum.
apply eq_bigr => m _ /=.
rewrite !mevalZ; f_equal.
rewrite /comp_mpoly /meval !mmapX rmorph_prod.
by apply eq_bigr => i _; rewrite rmorphX.
Qed.

Lemma meval_eq n (R : ringType) (e1 e2 : 'I_n -> R) (p : {mpoly R[n]}) :
  e1 =1 e2 -> p.@[e1] = p.@[e2].
Proof.
move=> He; rewrite !mevalE; apply eq_bigr => m _; f_equal.
by apply eq_bigr => i _; f_equal.
Qed.
