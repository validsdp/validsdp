(** * Error bounds on triangular substitution *)

(** Bounds from:
    Effects of Underflow on Solving Linear Systems
    James Demmel, May 1981. *)

From Stdlib Require Import Reals Psatz.
From Flocq Require Import Core.Raux.

Require Import misc.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop matrix.
From mathcomp Require Import seq eqtype.

From mathcomp Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Require Import fsum_l2r fcmsum cholesky.

Section Triangle.

Variable fs : Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).

(** Eq. (87) from Algorithm in Appendix 2 *)
Definition yhat n (bi : F) (L : 'M[F]_n) (y : 'cV[F]_n) (i : 'I_n) :=
  fdiv (fcmsum_l2r bi [ffun j => fmult (L i j) (y j ord0) : R]) (L i i).

(** Triangular substitution (algorithm in Appendix 2) *)
Definition fwd_subst n (L : 'M[F]_n) (b : 'cV[F]_n) :=
  foldl
    (fun (y : 'cV_n) i =>
       \col_i' if i' != i then y i ord0 else yhat (b i ord0) L y i)
    b (ord_enum n).  (* initial value (b here) can be any vector of correct
                        dimensions, we chose b as it better matches the fctl
                        model where the C program overwrites b with y *)

(** Lemma 4 *)
Lemma lemma_4_ideal n (L : 'M[F]_n) (b : 'cV[F]_n) :
  exists (dL : 'M_n) (db : 'cV_n),
    [/\
       (MF2R L + dL) *m MF2R (fwd_subst L b) = MF2R b + db,
       (forall i j,
         Rabs (dL i j)
         <= Rabs (L i j)
            * (if i == j then if j == 0%N :> nat then eps else eps + eps
               else if j == 0%N :> nat then INR i * eps else INR (i + 1 - j) * eps)) &
       forall i, db i ord0 <= INR i * eta
    ].
Abort.

(* For now, let's prove a slightly weaker lemma so that we can reuse
   our previous results on summation error (instead of Proposition 2). *)

(** Lemma 4' *)
Lemma lemma_4 n (L : 'M[F]_n) (b : 'cV[F]_n) :
  let yhat := fwd_subst L b in
  (forall i, Rabs (yhat i ord0) >= eta / eps) ->
  exists (dL : 'M_n) (db : 'cV_n),
    [/\
       (MF2R L + dL) *m MF2R yhat = MF2R b + db,
       (forall i j, Rabs (dL i j) <= Rabs (L i j) * INR (n + 1) * eps) &
       forall i, db i ord0 <= INR i * eta
    ].
Proof.
move=> yhat' yhat'_normalized.
