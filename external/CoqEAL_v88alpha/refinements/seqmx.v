From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly matrix mxpoly.

From CoqEAL Require Import hrel param refinements trivial_seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Refinements.Op.

Local Open Scope ring_scope.

Delimit Scope hetero_computable_scope with HC.

Section classes.

Class hzero_of I B := hzero_op : forall m n : I, B m n.
Local Notation "0" := hzero_op : hetero_computable_scope.

Class hmul_of I B := hmul_op : forall m n p : I, B m n -> B n p -> B m p.
Local Notation "*m%HC" := hmul_op.
Local Notation "x *m y" := (hmul_op x y) : hetero_computable_scope.

(* Class hopp I B := hopp_op : forall m n : I, B m n -> B m n. *)
(* Local Notation "- x" := (hopp_op x) : hetero_computable_scope. *)

Class heq_of I B := heq_op : forall m n : I, B m n -> B m n -> bool.
Local Notation "x == y" := (heq_op x y) : hetero_computable_scope.

Local Open Scope nat_scope.

(* TODO: Remove this and get a better way for extracting elements *)
Class top_left_of A B := top_left_op : A -> B.

Class usubmx_of B :=
  usubmx_op : forall (m1 m2 n : nat), B (m1 + m2) n -> B m1 n.
Class dsubmx_of B :=
  dsubmx_op : forall (m1 m2 n : nat), B (m1 + m2) n -> B m2 n.
Class lsubmx_of B :=
  lsubmx_op : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n1.
Class rsubmx_of B :=
  rsubmx_op : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n2.
Class ulsubmx_of B :=
  ulsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n1.
Class ursubmx_of B :=
  ursubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n2.
Class dlsubmx_of B :=
  dlsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n1.
Class drsubmx_of B :=
  drsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n2.
Class row_mx_of B :=
  row_mx_op : forall (m n1 n2 : nat), B m n1 -> B m n2 -> B m (n1 + n2).
Class col_mx_of B :=
  col_mx_op : forall (m1 m2 n : nat), B m1 n -> B m2 n -> B (m1 + m2) n.
Class block_mx_of B :=
  block_mx_op : forall (m1 m2 n1 n2 : nat),
    B m1 n1 -> B m1 n2 -> B m2 n1 -> B m2 n2 -> B (m1 + m2) (n1 + n2).

Class const_mx_of A B := const_mx_op : forall (m n : nat), A -> B m n.

Class map_mx_of A B C D :=
  map_mx_op : (A -> B) -> C -> D.

End classes.

Typeclasses Transparent hzero_of hmul_of heq_of top_left_of usubmx_of dsubmx_of
            lsubmx_of rsubmx_of ulsubmx_of ursubmx_of dlsubmx_of drsubmx_of
            row_mx_of col_mx_of block_mx_of const_mx_of map_mx_of.

Notation "0" := hzero_op : hetero_computable_scope.
(* Notation "- x" := (hopp_op x) : hetero_computable_scope. *)
Notation "x == y" := (heq_op x y) : hetero_computable_scope.
Notation "*m%HC" := hmul_op.
Notation "x *m y" := (hmul_op x y) : hetero_computable_scope.

Section extra_seq.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma zipwithE s1 s2 : zipwith s1 s2 = [seq f x.1 x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x1 s1 ihs1] [|x2 s2] //=; rewrite ihs1. Qed.

Fixpoint foldl2 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

End extra_seq.

Parametricity zipwith.
Parametricity foldl2.

Section seqmx_op.

Variable A B : Type.
Variable I : nat -> Type.

Definition seqmx {A} := seq (seq A).
Definition hseqmx {A} := fun (_ _ : nat) => @seqmx A.

Context `{zero_of A, one_of A, add_of A, opp_of A, mul_of A, eq_of A}.
Context `{forall n, implem_of 'I_n (I n)}.

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition seqmx_of_fun m n (f : I m -> I n -> A) : hseqmx m n :=
  let enum_n := map implem (ord_enum_eq n) in
  let enum_m := map implem (ord_enum_eq m) in
  map (fun i => map (f i) enum_n) enum_m.

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmx :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Global Instance const_seqmx : const_mx_of A hseqmx :=
  fun m n (x : A) => nseq m (nseq n x).

Global Instance map_seqmx : map_mx_of A B seqmx seqmx :=
  fun (f : A -> B) (M : seqmx) => map (map f) M.

Definition zipwith_seqmx (f : A -> A -> A) (M N : seqmx) :=
  zipwith (zipwith f) M N.

Global Instance seqmx0 : hzero_of hseqmx :=
  fun m n => const_seqmx m n 0%C.

Definition diag_seqmx (s : seqmx) :=
  mkseqmx_ord (fun (i j : 'I_(size (nth [::] s 0))) =>
                 (if i == j then nth 0%C (nth [::] s 0) i else 0%C)).

Definition scalar_seqmx m (x : A) := diag_seqmx (const_seqmx 1%N m x).

Global Instance seqmx1 m : one_of seqmx := scalar_seqmx m 1%C.

Global Instance opp_seqmx : opp_of (@seqmx A) := map (map -%C).

Global Instance add_seqmx : add_of seqmx := zipwith_seqmx +%C.

(* TODO: Implement better *)
Global Instance sub_seqmx : sub_of (@seqmx A) := fun a b => (a + - b)%C.

Definition trseqmx m n (M : @hseqmx A m n) :=
  if eqn m 0 then nseq n [::] else foldr (zipwith cons) (nseq n [::]) M.

Global Instance mul_seqmx : @hmul_of nat hseqmx :=
  fun _ n p M N =>
    let N := trseqmx N in
    if n is O then seqmx0 (size M) p else
      map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

Global Instance scale_seqmx : scale_of A seqmx :=
  fun x M => map (map (mul_op x)) M.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance eq_seqmx : eq_of (@seqmx A) := eq_seq (eq_seq eq_op).

Global Instance top_left_seqmx : top_left_of seqmx A :=
  fun (M : seqmx) => nth 0%C (nth [::] M 0) 0.

Global Instance usubseqmx : usubmx_of hseqmx :=
  fun m1 m2 n (M : @seqmx A) => take m1 M.

Global Instance dsubseqmx : dsubmx_of hseqmx :=
  fun m1 m2 n (M : @seqmx A) => drop m1 M.

Global Instance lsubseqmx : lsubmx_of hseqmx :=
  fun m n1 n2 (M : @seqmx A) => map (take n1) M.

Global Instance rsubseqmx : rsubmx_of hseqmx :=
  fun m n1 n2 (M : @seqmx A) => map (drop n1) M.

Global Instance ulsubseqmx : ulsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
    lsubseqmx (usubseqmx M).

Global Instance ursubseqmx : ursubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
    rsubseqmx (usubseqmx M).

Global Instance dlsubseqmx : dlsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
  lsubseqmx (dsubseqmx M).

Global Instance drsubseqmx : drsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
  rsubseqmx (dsubseqmx M).

Global Instance row_seqmx : row_mx_of hseqmx :=
  fun m n1 n2 (M N : @seqmx A) => zipwith cat M N.

Global Instance col_seqmx : col_mx_of hseqmx :=
  fun m1 m2 n (M N : @seqmx A) => M ++ N.

Global Instance block_seqmx : block_mx_of hseqmx :=
  fun m1 m2 n1 n2 Aul Aur Adl Adr =>
  col_seqmx (row_seqmx Aul Aur) (row_seqmx Adl Adr).

Definition delta_seqmx m n i j : hseqmx m n :=
  mkseqmx_ord (fun (i0 : 'I_m) (j0 : 'I_n) =>
                 if (eqn i0 i) && (eqn j0 j) then 1%C else 0%C).

Fixpoint trace_seqmx m (s : hseqmx m m) :=
  match m with
  | O => 0%C
  | (S n) => (top_left_seqmx s + @trace_seqmx n (@drsubseqmx 1%N n 1%N n s))%C
  end.

Definition pid_seqmx m n r :=
  mkseqmx_ord (fun (i : 'I_m) (j : 'I_n) =>
                 if (eqn i j) && (i < r) then 1%C else 0%C).

Definition copid_seqmx m r := (seqmx1 m - pid_seqmx m m r)%C.

End seqmx_op.

Parametricity subType.
Parametricity ord_enum_eq.
Parametricity seqmx_of_fun.
Parametricity mkseqmx_ord.
Parametricity const_seqmx.
Parametricity map_seqmx.
Parametricity zipwith_seqmx.
Parametricity seqmx0.
Definition diag_seqmx_simpl := Eval cbv in diag_seqmx.
Definition diag_seqmx_simpl_R     : forall (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
         (H₁ : A₁) (H₂ : A₂) (_ : A_R H₁ H₂) (s₁ : list (list A₁)) 
         (s₂ : list (list A₂)) (_ : @list_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R) s₁ s₂),
       @list_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R) (@diag_seqmx_simpl A₁ H₁ s₁)
         (@diag_seqmx_simpl A₂ H₂ s₂)
 := 
fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (H₁ : A₁) 
  (H₂ : A₂) (H_R : A_R H₁ H₂) (s₁ : list (list A₁)) (s₂ : list (list A₂))
  (s_R : @list_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R) s₁ s₂) =>
(let fix_map_1 :
   forall
     _ : list
           (ordinal
              ((fix size (s : list A₁) : nat :=
                  match s return nat with
                  | nil => O
                  | cons _ s' => S (size s')
                  end) match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end)), list (list A₁) :=
   fix
   map (s : list
              (ordinal
                 ((fix size (s : list A₁) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end))) : list (list A₁) :=
     match s return (list (list A₁)) with
     | nil => @nil (list A₁)
     | cons x s' =>
         @cons (list A₁)
           ((fix
             map0 (s0 : list
                          (ordinal
                             ((fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end))) : list A₁ :=
               match s0 return (list A₁) with
               | nil => @nil A₁
               | cons x0 s'0 =>
                   @cons A₁
                     match
                       (fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end) match x return nat with
                               | @Ordinal _ m _ => m
                               end match x0 return nat with
                                   | @Ordinal _ m _ => m
                                   end return A₁
                     with
                     | true =>
                         (fix nth (s1 : list A₁) (n : nat) {struct n} : A₁ :=
                            match s1 return A₁ with
                            | nil => H₁
                            | cons x1 s'1 =>
                                match n return A₁ with
                                | O => x1
                                | S n' => nth s'1 n'
                                end
                            end)
                           match s₁ return (list A₁) with
                           | nil => @nil A₁
                           | cons x1 _ => x1
                           end match x return nat with
                               | @Ordinal _ m _ => m
                               end
                     | false => H₁
                     end (map0 s'0)
               end)
              ((fix pmap (s0 : list nat) :
                  list
                    (ordinal
                       ((fix size (s1 : list A₁) : nat :=
                           match s1 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x0 _ => x0
                          end)) :=
                  match
                    s0
                    return
                      (list
                         (ordinal
                            ((fix size (s2 : list A₁) : nat :=
                                match s2 return nat with
                                | nil => O
                                | cons _ s'0 => S (size s'0)
                                end)
                               match s₁ return (list A₁) with
                               | nil => @nil A₁
                               | cons x0 _ => x0
                               end)))
                  with
                  | nil =>
                      @nil
                        (ordinal
                           ((fix size (s1 : list A₁) : nat :=
                               match s1 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x0 _ => x0
                              end))
                  | cons x0 s'0 =>
                      match
                        match
                          (fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s1 : list A₁) : nat :=
                                 match s1 return nat with
                                 | nil => O
                                 | cons _ s'1 => S (size s'1)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x1 _ => x1
                                end return nat
                            with
                            | O => S x0
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x0 l
                            end O as Px
                          return
                            (forall
                               _ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s1 : list A₁) : nat :=
                                             match s1 return nat with
                                             | nil => O
                                             | cons _ s'1 => S (size s'1)
                                             end)
                                            match s₁ return (list A₁) with
                                            | nil => @nil A₁
                                            | cons x1 _ => x1
                                            end return nat
                                        with
                                        | O => S x0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x0 l
                                        end O) Px,
                             option
                               (ordinal
                                  ((fix size (s1 : list A₁) : nat :=
                                      match s1 return nat with
                                      | nil => O
                                      | cons _ s'1 => S (size s'1)
                                      end)
                                     match s₁ return (list A₁) with
                                     | nil => @nil A₁
                                     | cons x1 _ => x1
                                     end)))
                        with
                        | true =>
                            fun
                              Px : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s1 : list A₁) : nat :=
                                             match s1 return nat with
                                             | nil => O
                                             | cons _ s'1 => S (size s'1)
                                             end)
                                            match s₁ return (list A₁) with
                                            | nil => @nil A₁
                                            | cons x1 _ => x1
                                            end return nat
                                        with
                                        | O => S x0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x0 l
                                        end O) true =>
                            @Some
                              (ordinal
                                 ((fix size (s1 : list A₁) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x1 _ => x1
                                    end))
                              (@Ordinal
                                 ((fix size (s1 : list A₁) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x1 _ => x1
                                    end) x0 Px)
                        | false =>
                            fun
                              _ : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s1 : list A₁) : nat :=
                                            match s1 return nat with
                                            | nil => O
                                            | cons _ s'1 => S (size s'1)
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x1 _ => x1
                                           end return nat
                                       with
                                       | O => S x0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x0 l
                                       end O) false =>
                            @None
                              (ordinal
                                 ((fix size (s1 : list A₁) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x1 _ => x1
                                    end))
                        end
                          (@Logic.eq_refl bool
                             ((fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end)
                                match
                                  (fix size (s1 : list A₁) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x1 _ => x1
                                    end return nat
                                with
                                | O => S x0
                                | S l =>
                                    (fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l0 => sub k l0
                                           end
                                       end) x0 l
                                end O))
                        return
                          (list
                             (ordinal
                                ((fix size (s1 : list A₁) : nat :=
                                    match s1 return nat with
                                    | nil => O
                                    | cons _ s'1 => S (size s'1)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x1 _ => x1
                                   end)))
                      with
                      | Some y =>
                          @cons
                            (ordinal
                               ((fix size (s1 : list A₁) : nat :=
                                   match s1 return nat with
                                   | nil => O
                                   | cons _ s'1 => S (size s'1)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x1 _ => x1
                                  end)) y (pmap s'0)
                      | None => pmap s'0
                      end
                  end)
                 ((fix iota (m n : nat) {struct n} : list nat :=
                     match n return (list nat) with
                     | O => @nil nat
                     | S n' => @cons nat m (iota (S m) n')
                     end) O
                    ((fix size (s0 : list A₁) : nat :=
                        match s0 return nat with
                        | nil => O
                        | cons _ s'0 => S (size s'0)
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x0 _ => x0
                       end)))) (map s')
     end in
 let fix_map_2 :
   forall
     _ : list
           (ordinal
              ((fix size (s : list A₂) : nat :=
                  match s return nat with
                  | nil => O
                  | cons _ s' => S (size s')
                  end) match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end)), list (list A₂) :=
   fix
   map (s : list
              (ordinal
                 ((fix size (s : list A₂) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end))) : list (list A₂) :=
     match s return (list (list A₂)) with
     | nil => @nil (list A₂)
     | cons x s' =>
         @cons (list A₂)
           ((fix
             map0 (s0 : list
                          (ordinal
                             ((fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end))) : list A₂ :=
               match s0 return (list A₂) with
               | nil => @nil A₂
               | cons x0 s'0 =>
                   @cons A₂
                     match
                       (fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end) match x return nat with
                               | @Ordinal _ m _ => m
                               end match x0 return nat with
                                   | @Ordinal _ m _ => m
                                   end return A₂
                     with
                     | true =>
                         (fix nth (s1 : list A₂) (n : nat) {struct n} : A₂ :=
                            match s1 return A₂ with
                            | nil => H₂
                            | cons x1 s'1 =>
                                match n return A₂ with
                                | O => x1
                                | S n' => nth s'1 n'
                                end
                            end)
                           match s₂ return (list A₂) with
                           | nil => @nil A₂
                           | cons x1 _ => x1
                           end match x return nat with
                               | @Ordinal _ m _ => m
                               end
                     | false => H₂
                     end (map0 s'0)
               end)
              ((fix pmap (s0 : list nat) :
                  list
                    (ordinal
                       ((fix size (s1 : list A₂) : nat :=
                           match s1 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x0 _ => x0
                          end)) :=
                  match
                    s0
                    return
                      (list
                         (ordinal
                            ((fix size (s2 : list A₂) : nat :=
                                match s2 return nat with
                                | nil => O
                                | cons _ s'0 => S (size s'0)
                                end)
                               match s₂ return (list A₂) with
                               | nil => @nil A₂
                               | cons x0 _ => x0
                               end)))
                  with
                  | nil =>
                      @nil
                        (ordinal
                           ((fix size (s1 : list A₂) : nat :=
                               match s1 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x0 _ => x0
                              end))
                  | cons x0 s'0 =>
                      match
                        match
                          (fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s1 : list A₂) : nat :=
                                 match s1 return nat with
                                 | nil => O
                                 | cons _ s'1 => S (size s'1)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x1 _ => x1
                                end return nat
                            with
                            | O => S x0
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x0 l
                            end O as Px
                          return
                            (forall
                               _ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s1 : list A₂) : nat :=
                                             match s1 return nat with
                                             | nil => O
                                             | cons _ s'1 => S (size s'1)
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x1 _ => x1
                                            end return nat
                                        with
                                        | O => S x0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x0 l
                                        end O) Px,
                             option
                               (ordinal
                                  ((fix size (s1 : list A₂) : nat :=
                                      match s1 return nat with
                                      | nil => O
                                      | cons _ s'1 => S (size s'1)
                                      end)
                                     match s₂ return (list A₂) with
                                     | nil => @nil A₂
                                     | cons x1 _ => x1
                                     end)))
                        with
                        | true =>
                            fun
                              Px : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s1 : list A₂) : nat :=
                                             match s1 return nat with
                                             | nil => O
                                             | cons _ s'1 => S (size s'1)
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x1 _ => x1
                                            end return nat
                                        with
                                        | O => S x0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x0 l
                                        end O) true =>
                            @Some
                              (ordinal
                                 ((fix size (s1 : list A₂) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x1 _ => x1
                                    end))
                              (@Ordinal
                                 ((fix size (s1 : list A₂) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x1 _ => x1
                                    end) x0 Px)
                        | false =>
                            fun
                              _ : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s1 : list A₂) : nat :=
                                            match s1 return nat with
                                            | nil => O
                                            | cons _ s'1 => S (size s'1)
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x1 _ => x1
                                           end return nat
                                       with
                                       | O => S x0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x0 l
                                       end O) false =>
                            @None
                              (ordinal
                                 ((fix size (s1 : list A₂) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x1 _ => x1
                                    end))
                        end
                          (@Logic.eq_refl bool
                             ((fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end)
                                match
                                  (fix size (s1 : list A₂) : nat :=
                                     match s1 return nat with
                                     | nil => O
                                     | cons _ s'1 => S (size s'1)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x1 _ => x1
                                    end return nat
                                with
                                | O => S x0
                                | S l =>
                                    (fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l0 => sub k l0
                                           end
                                       end) x0 l
                                end O))
                        return
                          (list
                             (ordinal
                                ((fix size (s1 : list A₂) : nat :=
                                    match s1 return nat with
                                    | nil => O
                                    | cons _ s'1 => S (size s'1)
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x1 _ => x1
                                   end)))
                      with
                      | Some y =>
                          @cons
                            (ordinal
                               ((fix size (s1 : list A₂) : nat :=
                                   match s1 return nat with
                                   | nil => O
                                   | cons _ s'1 => S (size s'1)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x1 _ => x1
                                  end)) y (pmap s'0)
                      | None => pmap s'0
                      end
                  end)
                 ((fix iota (m n : nat) {struct n} : list nat :=
                     match n return (list nat) with
                     | O => @nil nat
                     | S n' => @cons nat m (iota (S m) n')
                     end) O
                    ((fix size (s0 : list A₂) : nat :=
                        match s0 return nat with
                        | nil => O
                        | cons _ s'0 => S (size s'0)
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x0 _ => x0
                       end)))) (map s')
     end in
 fix
 map_R (s₁0 : list
                (ordinal
                   ((fix size (s : list A₁) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x _ => x
                      end)))
       (s₂0 : list
                (ordinal
                   ((fix size (s : list A₂) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end)))
       (s_R0 : @list_R
                 (ordinal
                    ((fix size (s : list A₁) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end))
                 (ordinal
                    ((fix size (s : list A₂) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end))
                 (@ordinal_R
                    ((fix size (s : list A₁) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end)
                    ((fix size (s : list A₂) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end)
                    ((let fix_size_1 : forall _ : list A₁, nat :=
                        fix size (s : list A₁) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end in
                      let fix_size_2 : forall _ : list A₂, nat :=
                        fix size (s : list A₂) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end in
                      fix
                      size_R (s₁1 : list A₁) (s₂1 : list A₂)
                             (s_R0 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R0} :
                        nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                        match
                          s_R0 in (list_R _ s₁2 s₂2)
                          return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                        with
                        | @list_R_nil_R _ _ _ => nat_R_O_R
                        | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁ s'₂ s'_R =>
                            @nat_R_S_R (fix_size_1 s'₁) (fix_size_2 s'₂)
                              (size_R s'₁ s'₂ s'_R)
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end
                       match
                         s_R in (list_R _ s₁1 s₂1)
                         return
                           (@list_R A₁ A₂ A_R
                              match s₁1 return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end
                              match s₂1 return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end)
                       with
                       | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                       | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ _ => x_R
                       end)) s₁0 s₂0) {struct s_R0} :
   @list_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R) (fix_map_1 s₁0) (fix_map_2 s₂0) :=
   match
     s_R0 in (list_R _ s₁1 s₂1)
     return
       (@list_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R) (fix_map_1 s₁1) (fix_map_2 s₂1))
   with
   | @list_R_nil_R _ _ _ => @list_R_nil_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R)
   | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
       @list_R_cons_R (list A₁) (list A₂) (@list_R A₁ A₂ A_R)
         ((fix
           map (s : list
                      (ordinal
                         ((fix size (s : list A₁) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end))) : list A₁ :=
             match s return (list A₁) with
             | nil => @nil A₁
             | cons x s' =>
                 @cons A₁
                   match
                     (fix eqn (m n : nat) {struct m} : bool :=
                        match m return bool with
                        | O => match n return bool with
                               | O => true
                               | S _ => false
                               end
                        | S m' =>
                            match n return bool with
                            | O => false
                            | S n' => eqn m' n'
                            end
                        end) match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end match x return nat with
                                 | @Ordinal _ m _ => m
                                 end return A₁
                   with
                   | true =>
                       (fix nth (s0 : list A₁) (n : nat) {struct n} : A₁ :=
                          match s0 return A₁ with
                          | nil => H₁
                          | cons x0 s'0 =>
                              match n return A₁ with
                              | O => x0
                              | S n' => nth s'0 n'
                              end
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x0 _ => x0
                         end match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end
                   | false => H₁
                   end (map s')
             end)
            ((fix pmap (s : list nat) :
                list
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)) :=
                match
                  s
                  return
                    (list
                       (ordinal
                          ((fix size (s1 : list A₁) : nat :=
                              match s1 return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end)))
                with
                | nil =>
                    @nil
                      (ordinal
                         ((fix size (s0 : list A₁) : nat :=
                             match s0 return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end))
                | cons x s' =>
                    match
                      match
                        (fix eqn (m n : nat) {struct m} : bool :=
                           match m return bool with
                           | O => match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                           | S m' =>
                               match n return bool with
                               | O => false
                               | S n' => eqn m' n'
                               end
                           end)
                          match
                            (fix size (s0 : list A₁) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x0 _ => x0
                              end return nat
                          with
                          | O => S x
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x l
                          end O as Px
                        return
                          (forall
                             _ : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₁) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) Px,
                           option
                             (ordinal
                                ((fix size (s0 : list A₁) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | true =>
                          fun
                            Px : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₁) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) true =>
                          @Some
                            (ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end))
                            (@Ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end) x Px)
                      | false =>
                          fun
                            _ : @eq bool
                                  ((fix eqn (m n : nat) {struct m} : bool :=
                                      match m return bool with
                                      | O =>
                                          match n return bool with
                                          | O => true
                                          | S _ => false
                                          end
                                      | S m' =>
                                          match n return bool with
                                          | O => false
                                          | S n' => eqn m' n'
                                          end
                                      end)
                                     match
                                       (fix size (s0 : list A₁) : nat :=
                                          match s0 return nat with
                                          | nil => O
                                          | cons _ s'0 => S (size s'0)
                                          end)
                                         match s₁ return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x0 _ => x0
                                         end return nat
                                     with
                                     | O => S x
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x l
                                     end O) false =>
                          @None
                            (ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end))
                      end
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O))
                      return
                        (list
                           (ordinal
                              ((fix size (s0 : list A₁) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x0 _ => x0
                                 end)))
                    with
                    | Some y =>
                        @cons
                          (ordinal
                             ((fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end)) y (pmap s')
                    | None => pmap s'
                    end
                end)
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₁) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end))))
         ((fix
           map (s : list
                      (ordinal
                         ((fix size (s : list A₂) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end))) : list A₂ :=
             match s return (list A₂) with
             | nil => @nil A₂
             | cons x s' =>
                 @cons A₂
                   match
                     (fix eqn (m n : nat) {struct m} : bool :=
                        match m return bool with
                        | O => match n return bool with
                               | O => true
                               | S _ => false
                               end
                        | S m' =>
                            match n return bool with
                            | O => false
                            | S n' => eqn m' n'
                            end
                        end) match x₂ return nat with
                             | @Ordinal _ m _ => m
                             end match x return nat with
                                 | @Ordinal _ m _ => m
                                 end return A₂
                   with
                   | true =>
                       (fix nth (s0 : list A₂) (n : nat) {struct n} : A₂ :=
                          match s0 return A₂ with
                          | nil => H₂
                          | cons x0 s'0 =>
                              match n return A₂ with
                              | O => x0
                              | S n' => nth s'0 n'
                              end
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x0 _ => x0
                         end match x₂ return nat with
                             | @Ordinal _ m _ => m
                             end
                   | false => H₂
                   end (map s')
             end)
            ((fix pmap (s : list nat) :
                list
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)) :=
                match
                  s
                  return
                    (list
                       (ordinal
                          ((fix size (s1 : list A₂) : nat :=
                              match s1 return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end)))
                with
                | nil =>
                    @nil
                      (ordinal
                         ((fix size (s0 : list A₂) : nat :=
                             match s0 return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end))
                | cons x s' =>
                    match
                      match
                        (fix eqn (m n : nat) {struct m} : bool :=
                           match m return bool with
                           | O => match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                           | S m' =>
                               match n return bool with
                               | O => false
                               | S n' => eqn m' n'
                               end
                           end)
                          match
                            (fix size (s0 : list A₂) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x0 _ => x0
                              end return nat
                          with
                          | O => S x
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x l
                          end O as Px
                        return
                          (forall
                             _ : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₂) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) Px,
                           option
                             (ordinal
                                ((fix size (s0 : list A₂) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | true =>
                          fun
                            Px : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₂) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) true =>
                          @Some
                            (ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end))
                            (@Ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end) x Px)
                      | false =>
                          fun
                            _ : @eq bool
                                  ((fix eqn (m n : nat) {struct m} : bool :=
                                      match m return bool with
                                      | O =>
                                          match n return bool with
                                          | O => true
                                          | S _ => false
                                          end
                                      | S m' =>
                                          match n return bool with
                                          | O => false
                                          | S n' => eqn m' n'
                                          end
                                      end)
                                     match
                                       (fix size (s0 : list A₂) : nat :=
                                          match s0 return nat with
                                          | nil => O
                                          | cons _ s'0 => S (size s'0)
                                          end)
                                         match s₂ return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x0 _ => x0
                                         end return nat
                                     with
                                     | O => S x
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x l
                                     end O) false =>
                          @None
                            (ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end))
                      end
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O))
                      return
                        (list
                           (ordinal
                              ((fix size (s0 : list A₂) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x0 _ => x0
                                 end)))
                    with
                    | Some y =>
                        @cons
                          (ordinal
                             ((fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end)) y (pmap s')
                    | None => pmap s'
                    end
                end)
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₂) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end))))
         ((let fix_map_3 :
             forall
               _ : list
                     (ordinal
                        ((fix size (s : list A₁) : nat :=
                            match s return nat with
                            | nil => O
                            | cons _ s' => S (size s')
                            end)
                           match s₁ return (list A₁) with
                           | nil => @nil A₁
                           | cons x _ => x
                           end)), list A₁ :=
             fix
             map (s : list
                        (ordinal
                           ((fix size (s : list A₁) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end))) : list A₁ :=
               match s return (list A₁) with
               | nil => @nil A₁
               | cons x s' =>
                   @cons A₁
                     match
                       (fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end) match x₁ return nat with
                               | @Ordinal _ m _ => m
                               end match x return nat with
                                   | @Ordinal _ m _ => m
                                   end return A₁
                     with
                     | true =>
                         (fix nth (s0 : list A₁) (n : nat) {struct n} : A₁ :=
                            match s0 return A₁ with
                            | nil => H₁
                            | cons x0 s'0 =>
                                match n return A₁ with
                                | O => x0
                                | S n' => nth s'0 n'
                                end
                            end)
                           match s₁ return (list A₁) with
                           | nil => @nil A₁
                           | cons x0 _ => x0
                           end match x₁ return nat with
                               | @Ordinal _ m _ => m
                               end
                     | false => H₁
                     end (map s')
               end in
           let fix_map_4 :
             forall
               _ : list
                     (ordinal
                        ((fix size (s : list A₂) : nat :=
                            match s return nat with
                            | nil => O
                            | cons _ s' => S (size s')
                            end)
                           match s₂ return (list A₂) with
                           | nil => @nil A₂
                           | cons x _ => x
                           end)), list A₂ :=
             fix
             map (s : list
                        (ordinal
                           ((fix size (s : list A₂) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end))) : list A₂ :=
               match s return (list A₂) with
               | nil => @nil A₂
               | cons x s' =>
                   @cons A₂
                     match
                       (fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end) match x₂ return nat with
                               | @Ordinal _ m _ => m
                               end match x return nat with
                                   | @Ordinal _ m _ => m
                                   end return A₂
                     with
                     | true =>
                         (fix nth (s0 : list A₂) (n : nat) {struct n} : A₂ :=
                            match s0 return A₂ with
                            | nil => H₂
                            | cons x0 s'0 =>
                                match n return A₂ with
                                | O => x0
                                | S n' => nth s'0 n'
                                end
                            end)
                           match s₂ return (list A₂) with
                           | nil => @nil A₂
                           | cons x0 _ => x0
                           end match x₂ return nat with
                               | @Ordinal _ m _ => m
                               end
                     | false => H₂
                     end (map s')
               end in
           fix
           map_R0 (s₁1 : list
                           (ordinal
                              ((fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end)))
                  (s₂1 : list
                           (ordinal
                              ((fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end)))
                  (s_R1 : @list_R
                            (ordinal
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end))
                            (ordinal
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end))
                            (@ordinal_R
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end)
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end)
                               ((let fix_size_1 : forall _ : list A₁, nat :=
                                   fix size (s : list A₁) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 let fix_size_2 : forall _ : list A₂, nat :=
                                   fix size (s : list A₂) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 fix
                                 size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                        (s_R1 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R1} :
                                   nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                   match
                                     s_R1 in (list_R _ s₁3 s₂3)
                                     return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                   with
                                   | @list_R_nil_R _ _ _ => nat_R_O_R
                                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                       @nat_R_S_R (fix_size_1 s'₁0) 
                                         (fix_size_2 s'₂0) (size_R s'₁0 s'₂0 s'_R0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end
                                  match
                                    s_R in (list_R _ s₁2 s₂2)
                                    return
                                      (@list_R A₁ A₂ A_R
                                         match s₁2 return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x _ => x
                                         end
                                         match s₂2 return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x _ => x
                                         end)
                                  with
                                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                  | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                                  end)) s₁1 s₂1) {struct s_R1} :
             @list_R A₁ A₂ A_R (fix_map_3 s₁1) (fix_map_4 s₂1) :=
             match
               s_R1 in (list_R _ s₁2 s₂2)
               return (@list_R A₁ A₂ A_R (fix_map_3 s₁2) (fix_map_4 s₂2))
             with
             | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
             | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 s'_R0 =>
                 @list_R_cons_R A₁ A₂ A_R
                   match
                     (fix eqn (m n : nat) {struct m} : bool :=
                        match m return bool with
                        | O => match n return bool with
                               | O => true
                               | S _ => false
                               end
                        | S m' =>
                            match n return bool with
                            | O => false
                            | S n' => eqn m' n'
                            end
                        end) match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end match x₁0 return nat with
                                 | @Ordinal _ m _ => m
                                 end return A₁
                   with
                   | true =>
                       (fix nth (s : list A₁) (n : nat) {struct n} : A₁ :=
                          match s return A₁ with
                          | nil => H₁
                          | cons x s' =>
                              match n return A₁ with
                              | O => x
                              | S n' => nth s' n'
                              end
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end
                   | false => H₁
                   end
                   match
                     (fix eqn (m n : nat) {struct m} : bool :=
                        match m return bool with
                        | O => match n return bool with
                               | O => true
                               | S _ => false
                               end
                        | S m' =>
                            match n return bool with
                            | O => false
                            | S n' => eqn m' n'
                            end
                        end) match x₂ return nat with
                             | @Ordinal _ m _ => m
                             end match x₂0 return nat with
                                 | @Ordinal _ m _ => m
                                 end return A₂
                   with
                   | true =>
                       (fix nth (s : list A₂) (n : nat) {struct n} : A₂ :=
                          match s return A₂ with
                          | nil => H₂
                          | cons x s' =>
                              match n return A₂ with
                              | O => x
                              | S n' => nth s' n'
                              end
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end match x₂ return nat with
                             | @Ordinal _ m _ => m
                             end
                   | false => H₂
                   end
                   match
                     (let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                        fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end in
                      let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                        fix eqn (m n : nat) {struct m} : bool :=
                          match m return bool with
                          | O => match n return bool with
                                 | O => true
                                 | S _ => false
                                 end
                          | S m' =>
                              match n return bool with
                              | O => false
                              | S n' => eqn m' n'
                              end
                          end in
                      fix
                      eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat)
                            (n_R : nat_R n₁ n₂) {struct m_R} :
                        bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                        match
                          m_R in (nat_R m₁0 m₂0)
                          return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                        with
                        | nat_R_O_R =>
                            match
                              n_R in (nat_R n₁0 n₂0)
                              return
                                (bool_R
                                   match n₁0 return bool with
                                   | O => true
                                   | S _ => false
                                   end
                                   match n₂0 return bool with
                                   | O => true
                                   | S _ => false
                                   end)
                            with
                            | nat_R_O_R => bool_R_true_R
                            | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                            end
                        | @nat_R_S_R m'₁ m'₂ m'_R =>
                            match
                              n_R in (nat_R n₁0 n₂0)
                              return
                                (bool_R
                                   match n₁0 return bool with
                                   | O => false
                                   | S n' => fix_eqn_1 m'₁ n'
                                   end
                                   match n₂0 return bool with
                                   | O => false
                                   | S n' => fix_eqn_2 m'₂ n'
                                   end)
                            with
                            | nat_R_O_R => bool_R_false_R
                            | @nat_R_S_R n'₁ n'₂ n'_R => eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                            end
                        end) match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end match x₂ return nat with
                                 | @Ordinal _ m _ => m
                                 end
                       match
                         x_R in (ordinal_R _ i₁ i₂)
                         return
                           (nat_R match i₁ return nat with
                                  | @Ordinal _ m _ => m
                                  end match i₂ return nat with
                                      | @Ordinal _ m _ => m
                                      end)
                       with
                       | @ordinal_R_Ordinal_R _ _ _ m₁ m₂ m_R i₁ i₂ _ => m_R
                       end match x₁0 return nat with
                           | @Ordinal _ m _ => m
                           end match x₂0 return nat with
                               | @Ordinal _ m _ => m
                               end
                       match
                         x_R0 in (ordinal_R _ i₁ i₂)
                         return
                           (nat_R match i₁ return nat with
                                  | @Ordinal _ m _ => m
                                  end match i₂ return nat with
                                      | @Ordinal _ m _ => m
                                      end)
                       with
                       | @ordinal_R_Ordinal_R _ _ _ m₁ m₂ m_R i₁ i₂ _ => m_R
                       end in (bool_R x₁1 x₂1)
                     return
                       (A_R
                          match x₁1 return A₁ with
                          | true =>
                              (fix nth (s : list A₁) (n : nat) {struct n} : A₁ :=
                                 match s return A₁ with
                                 | nil => H₁
                                 | cons x s' =>
                                     match n return A₁ with
                                     | O => x
                                     | S n' => nth s' n'
                                     end
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end match x₁ return nat with
                                    | @Ordinal _ m _ => m
                                    end
                          | false => H₁
                          end
                          match x₂1 return A₂ with
                          | true =>
                              (fix nth (s : list A₂) (n : nat) {struct n} : A₂ :=
                                 match s return A₂ with
                                 | nil => H₂
                                 | cons x s' =>
                                     match n return A₂ with
                                     | O => x
                                     | S n' => nth s' n'
                                     end
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end match x₂ return nat with
                                    | @Ordinal _ m _ => m
                                    end
                          | false => H₂
                          end)
                   with
                   | bool_R_true_R =>
                       (let fix_nth_1 : forall (_ : list A₁) (_ : nat), A₁ :=
                          fix nth (s : list A₁) (n : nat) {struct n} : A₁ :=
                            match s return A₁ with
                            | nil => H₁
                            | cons x s' =>
                                match n return A₁ with
                                | O => x
                                | S n' => nth s' n'
                                end
                            end in
                        let fix_nth_2 : forall (_ : list A₂) (_ : nat), A₂ :=
                          fix nth (s : list A₂) (n : nat) {struct n} : A₂ :=
                            match s return A₂ with
                            | nil => H₂
                            | cons x s' =>
                                match n return A₂ with
                                | O => x
                                | S n' => nth s' n'
                                end
                            end in
                        fix
                        nth_R (s₁2 : list A₁) (s₂2 : list A₂)
                              (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) 
                              (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
                          A_R (fix_nth_1 s₁2 n₁) (fix_nth_2 s₂2 n₂) :=
                          match
                            s_R2 in (list_R _ s₁3 s₂3)
                            return (A_R (fix_nth_1 s₁3 n₁) (fix_nth_2 s₂3 n₂))
                          with
                          | @list_R_nil_R _ _ _ =>
                              let gen_path :
                                forall (A : Type) (H : A),
                                let
                                  fix nth (s : list A) (n : nat) {struct n} : A :=
                                    match s return A with
                                    | nil => H
                                    | cons x s' =>
                                        match n return A with
                                        | O => x
                                        | S n' => nth s' n'
                                        end
                                    end in
                                forall n : nat, @eq A H (nth (@nil A) n) :=
                                fun (A : Type) (H : A) =>
                                let
                                  fix nth (s : list A) (n : nat) {struct n} : A :=
                                    match s return A with
                                    | nil => H
                                    | cons x s' =>
                                        match n return A with
                                        | O => x
                                        | S n' => nth s' n'
                                        end
                                    end in
                                fun n : nat =>
                                match n as n0 return (@eq A H (nth (@nil A) n0)) with
                                | O => @Logic.eq_refl A (nth (@nil A) O)
                                | S n0 => @Logic.eq_refl A (nth (@nil A) (S n0))
                                end in
                              @eq_rect A₁ H₁ (fun x : A₁ => A_R x (fix_nth_2 (@nil A₂) n₂))
                                (@eq_rect A₂ H₂ (fun x : A₂ => A_R H₁ x) H_R
                                   (fix_nth_2 (@nil A₂) n₂) (gen_path A₂ H₂ n₂))
                                (fix_nth_1 (@nil A₁) n₁) (gen_path A₁ H₁ n₁)
                          | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 s'_R1 =>
                              match
                                n_R in (nat_R n₁0 n₂0)
                                return
                                  (A_R (fix_nth_1 (@cons A₁ x₁1 s'₁1) n₁0)
                                     (fix_nth_2 (@cons A₂ x₂1 s'₂1) n₂0))
                              with
                              | nat_R_O_R => x_R1
                              | @nat_R_S_R n'₁ n'₂ n'_R =>
                                  nth_R s'₁1 s'₂1 s'_R1 n'₁ n'₂ n'_R
                              end
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end
                         match
                           s_R in (list_R _ s₁2 s₂2)
                           return
                             (@list_R A₁ A₂ A_R
                                match s₁2 return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end
                                match s₂2 return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end)
                         with
                         | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                         | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                         end match x₁ return nat with
                             | @Ordinal _ m _ => m
                             end match x₂ return nat with
                                 | @Ordinal _ m _ => m
                                 end
                         match
                           x_R in (ordinal_R _ i₁ i₂)
                           return
                             (nat_R match i₁ return nat with
                                    | @Ordinal _ m _ => m
                                    end match i₂ return nat with
                                        | @Ordinal _ m _ => m
                                        end)
                         with
                         | @ordinal_R_Ordinal_R _ _ _ m₁ m₂ m_R i₁ i₂ _ => m_R
                         end
                   | bool_R_false_R => H_R
                   end (fix_map_3 s'₁0) (fix_map_4 s'₂0) (map_R0 s'₁0 s'₂0 s'_R0)
             end)
            ((fix pmap (s : list nat) :
                list
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)) :=
                match
                  s
                  return
                    (list
                       (ordinal
                          ((fix size (s1 : list A₁) : nat :=
                              match s1 return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end)))
                with
                | nil =>
                    @nil
                      (ordinal
                         ((fix size (s0 : list A₁) : nat :=
                             match s0 return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end))
                | cons x s' =>
                    match
                      match
                        (fix eqn (m n : nat) {struct m} : bool :=
                           match m return bool with
                           | O => match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                           | S m' =>
                               match n return bool with
                               | O => false
                               | S n' => eqn m' n'
                               end
                           end)
                          match
                            (fix size (s0 : list A₁) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x0 _ => x0
                              end return nat
                          with
                          | O => S x
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x l
                          end O as Px
                        return
                          (forall
                             _ : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₁) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) Px,
                           option
                             (ordinal
                                ((fix size (s0 : list A₁) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | true =>
                          fun
                            Px : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₁) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) true =>
                          @Some
                            (ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end))
                            (@Ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end) x Px)
                      | false =>
                          fun
                            _ : @eq bool
                                  ((fix eqn (m n : nat) {struct m} : bool :=
                                      match m return bool with
                                      | O =>
                                          match n return bool with
                                          | O => true
                                          | S _ => false
                                          end
                                      | S m' =>
                                          match n return bool with
                                          | O => false
                                          | S n' => eqn m' n'
                                          end
                                      end)
                                     match
                                       (fix size (s0 : list A₁) : nat :=
                                          match s0 return nat with
                                          | nil => O
                                          | cons _ s'0 => S (size s'0)
                                          end)
                                         match s₁ return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x0 _ => x0
                                         end return nat
                                     with
                                     | O => S x
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x l
                                     end O) false =>
                          @None
                            (ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end))
                      end
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O))
                      return
                        (list
                           (ordinal
                              ((fix size (s0 : list A₁) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x0 _ => x0
                                 end)))
                    with
                    | Some y =>
                        @cons
                          (ordinal
                             ((fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end)) y (pmap s')
                    | None => pmap s'
                    end
                end)
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₁) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end)))
            ((fix pmap (s : list nat) :
                list
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)) :=
                match
                  s
                  return
                    (list
                       (ordinal
                          ((fix size (s1 : list A₂) : nat :=
                              match s1 return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end)))
                with
                | nil =>
                    @nil
                      (ordinal
                         ((fix size (s0 : list A₂) : nat :=
                             match s0 return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end))
                | cons x s' =>
                    match
                      match
                        (fix eqn (m n : nat) {struct m} : bool :=
                           match m return bool with
                           | O => match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                           | S m' =>
                               match n return bool with
                               | O => false
                               | S n' => eqn m' n'
                               end
                           end)
                          match
                            (fix size (s0 : list A₂) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s'0 => S (size s'0)
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x0 _ => x0
                              end return nat
                          with
                          | O => S x
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x l
                          end O as Px
                        return
                          (forall
                             _ : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₂) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) Px,
                           option
                             (ordinal
                                ((fix size (s0 : list A₂) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | true =>
                          fun
                            Px : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s0 : list A₂) : nat :=
                                           match s0 return nat with
                                           | nil => O
                                           | cons _ s'0 => S (size s'0)
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x0 _ => x0
                                          end return nat
                                      with
                                      | O => S x
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x l
                                      end O) true =>
                          @Some
                            (ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end))
                            (@Ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end) x Px)
                      | false =>
                          fun
                            _ : @eq bool
                                  ((fix eqn (m n : nat) {struct m} : bool :=
                                      match m return bool with
                                      | O =>
                                          match n return bool with
                                          | O => true
                                          | S _ => false
                                          end
                                      | S m' =>
                                          match n return bool with
                                          | O => false
                                          | S n' => eqn m' n'
                                          end
                                      end)
                                     match
                                       (fix size (s0 : list A₂) : nat :=
                                          match s0 return nat with
                                          | nil => O
                                          | cons _ s'0 => S (size s'0)
                                          end)
                                         match s₂ return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x0 _ => x0
                                         end return nat
                                     with
                                     | O => S x
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x l
                                     end O) false =>
                          @None
                            (ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end))
                      end
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O))
                      return
                        (list
                           (ordinal
                              ((fix size (s0 : list A₂) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x0 _ => x0
                                 end)))
                    with
                    | Some y =>
                        @cons
                          (ordinal
                             ((fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end)) y (pmap s')
                    | None => pmap s'
                    end
                end)
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₂) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end)))
            ((let fix_pmap_1 :
                forall _ : list nat,
                list
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)) :=
                fix pmap (s : list nat) :
                  list
                    (ordinal
                       ((fix size (s0 : list A₁) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x _ => x
                          end)) :=
                  match
                    s
                    return
                      (list
                         (ordinal
                            ((fix size (s1 : list A₁) : nat :=
                                match s1 return nat with
                                | nil => O
                                | cons _ s' => S (size s')
                                end)
                               match s₁ return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end)))
                  with
                  | nil =>
                      @nil
                        (ordinal
                           ((fix size (s0 : list A₁) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end))
                  | cons x s' =>
                      match
                        match
                          (fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O as Px
                          return
                            (forall
                               _ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s0 : list A₁) : nat :=
                                             match s0 return nat with
                                             | nil => O
                                             | cons _ s'0 => S (size s'0)
                                             end)
                                            match s₁ return (list A₁) with
                                            | nil => @nil A₁
                                            | cons x0 _ => x0
                                            end return nat
                                        with
                                        | O => S x
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x l
                                        end O) Px,
                             option
                               (ordinal
                                  ((fix size (s0 : list A₁) : nat :=
                                      match s0 return nat with
                                      | nil => O
                                      | cons _ s'0 => S (size s'0)
                                      end)
                                     match s₁ return (list A₁) with
                                     | nil => @nil A₁
                                     | cons x0 _ => x0
                                     end)))
                        with
                        | true =>
                            fun
                              Px : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s0 : list A₁) : nat :=
                                             match s0 return nat with
                                             | nil => O
                                             | cons _ s'0 => S (size s'0)
                                             end)
                                            match s₁ return (list A₁) with
                                            | nil => @nil A₁
                                            | cons x0 _ => x0
                                            end return nat
                                        with
                                        | O => S x
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x l
                                        end O) true =>
                            @Some
                              (ordinal
                                 ((fix size (s0 : list A₁) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x0 _ => x0
                                    end))
                              (@Ordinal
                                 ((fix size (s0 : list A₁) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x0 _ => x0
                                    end) x Px)
                        | false =>
                            fun
                              _ : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s0 : list A₁) : nat :=
                                            match s0 return nat with
                                            | nil => O
                                            | cons _ s'0 => S (size s'0)
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x0 _ => x0
                                           end return nat
                                       with
                                       | O => S x
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x l
                                       end O) false =>
                            @None
                              (ordinal
                                 ((fix size (s0 : list A₁) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x0 _ => x0
                                    end))
                        end
                          (@Logic.eq_refl bool
                             ((fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end)
                                match
                                  (fix size (s0 : list A₁) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₁ return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x0 _ => x0
                                    end return nat
                                with
                                | O => S x
                                | S l =>
                                    (fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l0 => sub k l0
                                           end
                                       end) x l
                                end O))
                        return
                          (list
                             (ordinal
                                ((fix size (s0 : list A₁) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | Some y =>
                          @cons
                            (ordinal
                               ((fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end)) y (pmap s')
                      | None => pmap s'
                      end
                  end in
              let fix_pmap_2 :
                forall _ : list nat,
                list
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)) :=
                fix pmap (s : list nat) :
                  list
                    (ordinal
                       ((fix size (s0 : list A₂) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x _ => x
                          end)) :=
                  match
                    s
                    return
                      (list
                         (ordinal
                            ((fix size (s1 : list A₂) : nat :=
                                match s1 return nat with
                                | nil => O
                                | cons _ s' => S (size s')
                                end)
                               match s₂ return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)))
                  with
                  | nil =>
                      @nil
                        (ordinal
                           ((fix size (s0 : list A₂) : nat :=
                               match s0 return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end))
                  | cons x s' =>
                      match
                        match
                          (fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O as Px
                          return
                            (forall
                               _ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s0 : list A₂) : nat :=
                                             match s0 return nat with
                                             | nil => O
                                             | cons _ s'0 => S (size s'0)
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x0 _ => x0
                                            end return nat
                                        with
                                        | O => S x
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x l
                                        end O) Px,
                             option
                               (ordinal
                                  ((fix size (s0 : list A₂) : nat :=
                                      match s0 return nat with
                                      | nil => O
                                      | cons _ s'0 => S (size s'0)
                                      end)
                                     match s₂ return (list A₂) with
                                     | nil => @nil A₂
                                     | cons x0 _ => x0
                                     end)))
                        with
                        | true =>
                            fun
                              Px : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s0 : list A₂) : nat :=
                                             match s0 return nat with
                                             | nil => O
                                             | cons _ s'0 => S (size s'0)
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x0 _ => x0
                                            end return nat
                                        with
                                        | O => S x
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x l
                                        end O) true =>
                            @Some
                              (ordinal
                                 ((fix size (s0 : list A₂) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x0 _ => x0
                                    end))
                              (@Ordinal
                                 ((fix size (s0 : list A₂) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x0 _ => x0
                                    end) x Px)
                        | false =>
                            fun
                              _ : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s0 : list A₂) : nat :=
                                            match s0 return nat with
                                            | nil => O
                                            | cons _ s'0 => S (size s'0)
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x0 _ => x0
                                           end return nat
                                       with
                                       | O => S x
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x l
                                       end O) false =>
                            @None
                              (ordinal
                                 ((fix size (s0 : list A₂) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x0 _ => x0
                                    end))
                        end
                          (@Logic.eq_refl bool
                             ((fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end)
                                match
                                  (fix size (s0 : list A₂) : nat :=
                                     match s0 return nat with
                                     | nil => O
                                     | cons _ s'0 => S (size s'0)
                                     end)
                                    match s₂ return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x0 _ => x0
                                    end return nat
                                with
                                | O => S x
                                | S l =>
                                    (fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l0 => sub k l0
                                           end
                                       end) x l
                                end O))
                        return
                          (list
                             (ordinal
                                ((fix size (s0 : list A₂) : nat :=
                                    match s0 return nat with
                                    | nil => O
                                    | cons _ s'0 => S (size s'0)
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x0 _ => x0
                                   end)))
                      with
                      | Some y =>
                          @cons
                            (ordinal
                               ((fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end)) y (pmap s')
                      | None => pmap s'
                      end
                  end in
              fix
              pmap_R (s₁1 s₂1 : list nat) (s_R1 : @list_R nat nat nat_R s₁1 s₂1) {struct
                     s_R1} :
                @list_R
                  (ordinal
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end))
                  (ordinal
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end))
                  (@ordinal_R
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)
                     ((let fix_size_1 : forall _ : list A₁, nat :=
                         fix size (s : list A₁) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       let fix_size_2 : forall _ : list A₂, nat :=
                         fix size (s : list A₂) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       fix
                       size_R (s₁2 : list A₁) (s₂2 : list A₂)
                              (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                         nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                         match
                           s_R2 in (list_R _ s₁3 s₂3)
                           return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                         with
                         | @list_R_nil_R _ _ _ => nat_R_O_R
                         | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                             @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                               (size_R s'₁0 s'₂0 s'_R0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                        match
                          s_R in (list_R _ s₁2 s₂2)
                          return
                            (@list_R A₁ A₂ A_R
                               match s₁2 return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end
                               match s₂2 return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)
                        with
                        | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                        | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                        end)) (fix_pmap_1 s₁1) (fix_pmap_2 s₂1) :=
                match
                  s_R1 in (list_R _ s₁2 s₂2)
                  return
                    (@list_R
                       (ordinal
                          ((fix size (s : list A₁) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end))
                       (ordinal
                          ((fix size (s : list A₂) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end))
                       (@ordinal_R
                          ((fix size (s : list A₁) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end)
                          ((fix size (s : list A₂) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end)
                          ((let fix_size_1 : forall _ : list A₁, nat :=
                              fix size (s : list A₁) : nat :=
                                match s return nat with
                                | nil => O
                                | cons _ s' => S (size s')
                                end in
                            let fix_size_2 : forall _ : list A₂, nat :=
                              fix size (s : list A₂) : nat :=
                                match s return nat with
                                | nil => O
                                | cons _ s' => S (size s')
                                end in
                            fix
                            size_R (s₁3 : list A₁) (s₂3 : list A₂)
                                   (s_R3 : @list_R A₁ A₂ A_R s₁3 s₂3) {struct s_R3} :
                              nat_R (fix_size_1 s₁3) (fix_size_2 s₂3) :=
                              match
                                s_R3 in (list_R _ s₁4 s₂4)
                                return (nat_R (fix_size_1 s₁4) (fix_size_2 s₂4))
                              with
                              | @list_R_nil_R _ _ _ => nat_R_O_R
                              | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                  @nat_R_S_R (fix_size_1 s'₁0) 
                                    (fix_size_2 s'₂0) (size_R s'₁0 s'₂0 s'_R0)
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end
                             match
                               s_R in (list_R _ s₁3 s₂3)
                               return
                                 (@list_R A₁ A₂ A_R
                                    match s₁3 return (list A₁) with
                                    | nil => @nil A₁
                                    | cons x _ => x
                                    end
                                    match s₂3 return (list A₂) with
                                    | nil => @nil A₂
                                    | cons x _ => x
                                    end)
                             with
                             | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                             | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                             end)) (fix_pmap_1 s₁2) (fix_pmap_2 s₂2))
                with
                | @list_R_nil_R _ _ _ =>
                    @list_R_nil_R
                      (ordinal
                         ((fix size (s : list A₁) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end))
                      (ordinal
                         ((fix size (s : list A₂) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end))
                      (@ordinal_R
                         ((fix size (s : list A₁) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end)
                         ((fix size (s : list A₂) : nat :=
                             match s return nat with
                             | nil => O
                             | cons _ s' => S (size s')
                             end)
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end)
                         ((let fix_size_1 : forall _ : list A₁, nat :=
                             fix size (s : list A₁) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end in
                           let fix_size_2 : forall _ : list A₂, nat :=
                             fix size (s : list A₂) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end in
                           fix
                           size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                  (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                             nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                             match
                               s_R2 in (list_R _ s₁3 s₂3)
                               return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                             with
                             | @list_R_nil_R _ _ _ => nat_R_O_R
                             | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                 @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                                   (size_R s'₁0 s'₂0 s'_R0)
                             end)
                            match s₁ return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end
                            match s₂ return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end
                            match
                              s_R in (list_R _ s₁2 s₂2)
                              return
                                (@list_R A₁ A₂ A_R
                                   match s₁2 return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end
                                   match s₂2 return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end)
                            with
                            | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                            | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                            end))
                | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 s'_R0 =>
                    match
                      match
                        (let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                           fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end in
                         let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                           fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end in
                         fix
                         eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                               (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                           bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                           match
                             m_R in (nat_R m₁0 m₂0)
                             return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                           with
                           | nat_R_O_R =>
                               match
                                 n_R in (nat_R n₁0 n₂0)
                                 return
                                   (bool_R
                                      match n₁0 return bool with
                                      | O => true
                                      | S _ => false
                                      end
                                      match n₂0 return bool with
                                      | O => true
                                      | S _ => false
                                      end)
                               with
                               | nat_R_O_R => bool_R_true_R
                               | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                               end
                           | @nat_R_S_R m'₁ m'₂ m'_R =>
                               match
                                 n_R in (nat_R n₁0 n₂0)
                                 return
                                   (bool_R
                                      match n₁0 return bool with
                                      | O => false
                                      | S n' => fix_eqn_1 m'₁ n'
                                      end
                                      match n₂0 return bool with
                                      | O => false
                                      | S n' => fix_eqn_2 m'₂ n'
                                      end)
                               with
                               | nat_R_O_R => bool_R_false_R
                               | @nat_R_S_R n'₁ n'₂ n'_R => eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                               end
                           end)
                          match
                            (fix size (s : list A₁) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end return nat
                          with
                          | O => S x₁0
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x₁0 l
                          end
                          match
                            (fix size (s : list A₂) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end return nat
                          with
                          | O => S x₂0
                          | S l =>
                              (fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l0 => sub k l0
                                     end
                                 end) x₂0 l
                          end
                          match
                            (let fix_size_1 : forall _ : list A₁, nat :=
                               fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end in
                             let fix_size_2 : forall _ : list A₂, nat :=
                               fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end in
                             fix
                             size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                    (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                               nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                               match
                                 s_R2 in (list_R _ s₁3 s₂3)
                                 return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                               with
                               | @list_R_nil_R _ _ _ => nat_R_O_R
                               | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                   @nat_R_S_R (fix_size_1 s'₁1) 
                                     (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end
                              match
                                s_R in (list_R _ s₁2 s₂2)
                                return
                                  (@list_R A₁ A₂ A_R
                                     match s₁2 return (list A₁) with
                                     | nil => @nil A₁
                                     | cons x _ => x
                                     end
                                     match s₂2 return (list A₂) with
                                     | nil => @nil A₂
                                     | cons x _ => x
                                     end)
                              with
                              | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                              | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                              end in (nat_R m₁ m₂)
                            return
                              (nat_R
                                 match m₁ return nat with
                                 | O => S x₁0
                                 | S l =>
                                     (fix sub (n m : nat) {struct n} : nat :=
                                        match n return nat with
                                        | O => n
                                        | S k =>
                                            match m return nat with
                                            | O => n
                                            | S l0 => sub k l0
                                            end
                                        end) x₁0 l
                                 end
                                 match m₂ return nat with
                                 | O => S x₂0
                                 | S l =>
                                     (fix sub (n m : nat) {struct n} : nat :=
                                        match n return nat with
                                        | O => n
                                        | S k =>
                                            match m return nat with
                                            | O => n
                                            | S l0 => sub k l0
                                            end
                                        end) x₂0 l
                                 end)
                          with
                          | nat_R_O_R => @nat_R_S_R x₁0 x₂0 x_R0
                          | @nat_R_S_R l₁ l₂ l_R =>
                              (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                                 fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l => sub k l
                                       end
                                   end in
                               let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                                 fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l => sub k l
                                       end
                                   end in
                               fix
                               sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                                     (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                                 nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                 let gen_path :
                                   let
                                     fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l => sub k l
                                           end
                                       end in
                                   forall n m : nat,
                                   @eq nat
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l => sub k l
                                         end
                                     end (sub n m) :=
                                   let
                                     fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l => sub k l
                                           end
                                       end in
                                   fun n m : nat =>
                                   match
                                     n as n0
                                     return
                                       (@eq nat
                                          match n0 return nat with
                                          | O => n0
                                          | S k =>
                                              match m return nat with
                                              | O => n0
                                              | S l => sub k l
                                              end
                                          end (sub n0 m))
                                   with
                                   | O => @Logic.eq_refl nat (sub O m)
                                   | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                   end in
                                 @eq_rect nat
                                   match n₁ return nat with
                                   | O => n₁
                                   | S k =>
                                       match m₁ return nat with
                                       | O => n₁
                                       | S l => fix_sub_1 k l
                                       end
                                   end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                   (@eq_rect nat
                                      match n₂ return nat with
                                      | O => n₂
                                      | S k =>
                                          match m₂ return nat with
                                          | O => n₂
                                          | S l => fix_sub_2 k l
                                          end
                                      end
                                      (fun x : nat =>
                                       nat_R
                                         match n₁ return nat with
                                         | O => n₁
                                         | S k =>
                                             match m₁ return nat with
                                             | O => n₁
                                             | S l => fix_sub_1 k l
                                             end
                                         end x)
                                      match
                                        n_R in (nat_R n₁0 n₂0)
                                        return
                                          (nat_R
                                             match n₁0 return nat with
                                             | O => n₁
                                             | S k =>
                                                 match m₁ return nat with
                                                 | O => n₁
                                                 | S l => fix_sub_1 k l
                                                 end
                                             end
                                             match n₂0 return nat with
                                             | O => n₂
                                             | S k =>
                                                 match m₂ return nat with
                                                 | O => n₂
                                                 | S l => fix_sub_2 k l
                                                 end
                                             end)
                                      with
                                      | nat_R_O_R => n_R
                                      | @nat_R_S_R k₁ k₂ k_R =>
                                          match
                                            m_R in (nat_R m₁0 m₂0)
                                            return
                                              (nat_R
                                                 match m₁0 return nat with
                                                 | O => n₁
                                                 | S l => fix_sub_1 k₁ l
                                                 end
                                                 match m₂0 return nat with
                                                 | O => n₂
                                                 | S l => fix_sub_2 k₂ l
                                                 end)
                                          with
                                          | nat_R_O_R => n_R
                                          | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                              sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                          end
                                      end (fix_sub_2 n₂ m₂) (gen_path n₂ m₂))
                                   (fix_sub_1 n₁ m₁) (gen_path n₁ m₁)) x₁0 x₂0 x_R0 l₁ l₂
                                l_R
                          end O O nat_R_O_R as Px_R in (bool_R Px₁ Px₂)
                        return
                          (forall
                             (H : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s : list A₁) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₁0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₁0 l
                                       end O) Px₁)
                             (H0 : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s : list A₂) : nat :=
                                             match s return nat with
                                             | nil => O
                                             | cons _ s' => S (size s')
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x _ => x
                                            end return nat
                                        with
                                        | O => S x₂0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x₂0 l
                                        end O) Px₂)
                             (_ : @eq_R bool bool bool_R
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s : list A₁) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₁0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₁0 l
                                       end O)
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s : list A₂) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₂0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₂0 l
                                       end O)
                                    ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                                        fix eqn (m n : nat) {struct m} : bool :=
                                          match m return bool with
                                          | O =>
                                              match n return bool with
                                              | O => true
                                              | S _ => false
                                              end
                                          | S m' =>
                                              match n return bool with
                                              | O => false
                                              | S n' => eqn m' n'
                                              end
                                          end in
                                      let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                                        fix eqn (m n : nat) {struct m} : bool :=
                                          match m return bool with
                                          | O =>
                                              match n return bool with
                                              | O => true
                                              | S _ => false
                                              end
                                          | S m' =>
                                              match n return bool with
                                              | O => false
                                              | S n' => eqn m' n'
                                              end
                                          end in
                                      fix
                                      eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                            (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                                        bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                                        match
                                          m_R in (nat_R m₁0 m₂0)
                                          return
                                            (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                                        with
                                        | nat_R_O_R =>
                                            match
                                              n_R in (nat_R n₁0 n₂0)
                                              return
                                                (bool_R
                                                   match n₁0 return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end
                                                   match n₂0 return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end)
                                            with
                                            | nat_R_O_R => bool_R_true_R
                                            | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                            end
                                        | @nat_R_S_R m'₁ m'₂ m'_R =>
                                            match
                                              n_R in (nat_R n₁0 n₂0)
                                              return
                                                (bool_R
                                                   match n₁0 return bool with
                                                   | O => false
                                                   | S n' => fix_eqn_1 m'₁ n'
                                                   end
                                                   match n₂0 return bool with
                                                   | O => false
                                                   | S n' => fix_eqn_2 m'₂ n'
                                                   end)
                                            with
                                            | nat_R_O_R => bool_R_false_R
                                            | @nat_R_S_R n'₁ n'₂ n'_R =>
                                                eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                            end
                                        end)
                                       match
                                         (fix size (s : list A₁) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₁0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₁0 l
                                       end
                                       match
                                         (fix size (s : list A₂) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₂0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₂0 l
                                       end
                                       match
                                         (let fix_size_1 : forall _ : list A₁, nat :=
                                            fix size (s : list A₁) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end in
                                          let fix_size_2 : forall _ : list A₂, nat :=
                                            fix size (s : list A₂) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end in
                                          fix
                                          size_R (s₁2 : list A₁) 
                                                 (s₂2 : list A₂)
                                                 (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct
                                                 s_R2} :
                                            nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                            match
                                              s_R2 in (list_R _ s₁3 s₂3)
                                              return
                                                (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                            with
                                            | @list_R_nil_R _ _ _ => nat_R_O_R
                                            | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1
                                              s'_R1 =>
                                                @nat_R_S_R (fix_size_1 s'₁1)
                                                  (fix_size_2 s'₂1)
                                                  (size_R s'₁1 s'₂1 s'_R1)
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x _ => x
                                           end
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x _ => x
                                           end
                                           match
                                             s_R in (list_R _ s₁2 s₂2)
                                             return
                                               (@list_R A₁ A₂ A_R
                                                  match s₁2 return (list A₁) with
                                                  | nil => @nil A₁
                                                  | cons x _ => x
                                                  end
                                                  match s₂2 return (list A₂) with
                                                  | nil => @nil A₂
                                                  | cons x _ => x
                                                  end)
                                           with
                                           | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                           | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1
                                             _ => x_R1
                                           end in (nat_R m₁ m₂)
                                         return
                                           (nat_R
                                              match m₁ return nat with
                                              | O => S x₁0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₁0 l
                                              end
                                              match m₂ return nat with
                                              | O => S x₂0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₂0 l
                                              end)
                                       with
                                       | nat_R_O_R => @nat_R_S_R x₁0 x₂0 x_R0
                                       | @nat_R_S_R l₁ l₂ l_R =>
                                           (let fix_sub_1 :
                                              forall (_ : nat) (_ : nat), nat :=
                                              fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l => sub k l
                                                    end
                                                end in
                                            let fix_sub_2 :
                                              forall (_ : nat) (_ : nat), nat :=
                                              fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l => sub k l
                                                    end
                                                end in
                                            fix
                                            sub_R (n₁ n₂ : nat) 
                                                  (n_R : nat_R n₁ n₂) 
                                                  (m₁ m₂ : nat) 
                                                  (m_R : nat_R m₁ m₂) {struct n_R} :
                                              nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                              let gen_path :
                                                let
                                                  fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l => sub k l
                                                        end
                                                    end in
                                                forall n m : nat,
                                                @eq nat
                                                  match n return nat with
                                                  | O => n
                                                  | S k =>
                                                      match m return nat with
                                                      | O => n
                                                      | S l => sub k l
                                                      end
                                                  end (sub n m) :=
                                                let
                                                  fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l => sub k l
                                                        end
                                                    end in
                                                fun n m : nat =>
                                                match
                                                  n as n0
                                                  return
                                                    (@eq nat
                                                       match n0 return nat with
                                                       | O => n0
                                                       | S k =>
                                                           match m return nat with
                                                           | O => n0
                                                           | S l => sub k l
                                                           end
                                                       end (sub n0 m))
                                                with
                                                | O => @Logic.eq_refl nat (sub O m)
                                                | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                                end in
                                              @eq_rect nat
                                                match n₁ return nat with
                                                | O => n₁
                                                | S k =>
                                                    match m₁ return nat with
                                                    | O => n₁
                                                    | S l => fix_sub_1 k l
                                                    end
                                                end
                                                (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                                (@eq_rect nat
                                                   match n₂ return nat with
                                                   | O => n₂
                                                   | S k =>
                                                       match m₂ return nat with
                                                       | O => n₂
                                                       | S l => fix_sub_2 k l
                                                       end
                                                   end
                                                   (fun x : nat =>
                                                    nat_R
                                                      match n₁ return nat with
                                                      | O => n₁
                                                      | S k =>
                                                          match m₁ return nat with
                                                          | O => n₁
                                                          | S l => fix_sub_1 k l
                                                          end
                                                      end x)
                                                   match
                                                     n_R in (nat_R n₁0 n₂0)
                                                     return
                                                       (nat_R
                                                          match n₁0 return nat with
                                                          | O => n₁
                                                          | S k =>
                                                              match m₁ return nat with
                                                              | O => n₁
                                                              | S l => fix_sub_1 k l
                                                              end
                                                          end
                                                          match n₂0 return nat with
                                                          | O => n₂
                                                          | S k =>
                                                              match m₂ return nat with
                                                              | O => n₂
                                                              | S l => fix_sub_2 k l
                                                              end
                                                          end)
                                                   with
                                                   | nat_R_O_R => n_R
                                                   | @nat_R_S_R k₁ k₂ k_R =>
                                                       match
                                                         m_R in (nat_R m₁0 m₂0)
                                                         return
                                                           (nat_R
                                                              match m₁0 return nat with
                                                              | O => n₁
                                                              | S l => fix_sub_1 k₁ l
                                                              end
                                                              match m₂0 return nat with
                                                              | O => n₂
                                                              | S l => fix_sub_2 k₂ l
                                                              end)
                                                       with
                                                       | nat_R_O_R => n_R
                                                       | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                           sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                                       end
                                                   end (fix_sub_2 n₂ m₂) 
                                                   (gen_path n₂ m₂)) 
                                                (fix_sub_1 n₁ m₁) 
                                                (gen_path n₁ m₁)) x₁0 x₂0 x_R0 l₁ l₂ l_R
                                       end O O nat_R_O_R) Px₁ Px₂ Px_R H H0),
                           @option_R
                             (ordinal
                                ((fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end))
                             (ordinal
                                ((fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end))
                             (@ordinal_R
                                ((fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end)
                                ((fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end)
                                ((let fix_size_1 : forall _ : list A₁, nat :=
                                    fix size (s : list A₁) : nat :=
                                      match s return nat with
                                      | nil => O
                                      | cons _ s' => S (size s')
                                      end in
                                  let fix_size_2 : forall _ : list A₂, nat :=
                                    fix size (s : list A₂) : nat :=
                                      match s return nat with
                                      | nil => O
                                      | cons _ s' => S (size s')
                                      end in
                                  fix
                                  size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                         (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                    nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                    match
                                      s_R2 in (list_R _ s₁3 s₂3)
                                      return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                    with
                                    | @list_R_nil_R _ _ _ => nat_R_O_R
                                    | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                        @nat_R_S_R (fix_size_1 s'₁1) 
                                          (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end
                                   match
                                     s_R in (list_R _ s₁2 s₂2)
                                     return
                                       (@list_R A₁ A₂ A_R
                                          match s₁2 return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end
                                          match s₂2 return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end)
                                   with
                                   | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                   | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                   end))
                             (match
                                Px₁ as Px
                                return
                                  (forall
                                     _ : @eq bool
                                           ((fix eqn (m n : nat) {struct m} : bool :=
                                               match m return bool with
                                               | O =>
                                                   match n return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end
                                               | S m' =>
                                                   match n return bool with
                                                   | O => false
                                                   | S n' => eqn m' n'
                                                   end
                                               end)
                                              match
                                                (fix size (s : list A₁) : nat :=
                                                   match s return nat with
                                                   | nil => O
                                                   | cons _ s' => S (size s')
                                                   end)
                                                  match s₁ return (list A₁) with
                                                  | nil => @nil A₁
                                                  | cons x _ => x
                                                  end return nat
                                              with
                                              | O => S x₁0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₁0 l
                                              end O) Px,
                                   option
                                     (ordinal
                                        ((fix size (s : list A₁) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₁ return (list A₁) with
                                           | nil => @nil A₁
                                           | cons x _ => x
                                           end)))
                              with
                              | true =>
                                  fun
                                    Px : @eq bool
                                           ((fix eqn (m n : nat) {struct m} : bool :=
                                               match m return bool with
                                               | O =>
                                                   match n return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end
                                               | S m' =>
                                                   match n return bool with
                                                   | O => false
                                                   | S n' => eqn m' n'
                                                   end
                                               end)
                                              match
                                                (fix size (s : list A₁) : nat :=
                                                   match s return nat with
                                                   | nil => O
                                                   | cons _ s' => S (size s')
                                                   end)
                                                  match s₁ return (list A₁) with
                                                  | nil => @nil A₁
                                                  | cons x _ => x
                                                  end return nat
                                              with
                                              | O => S x₁0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₁0 l
                                              end O) true =>
                                  @Some
                                    (ordinal
                                       ((fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end))
                                    (@Ordinal
                                       ((fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end) x₁0 Px)
                              | false =>
                                  fun
                                    _ : @eq bool
                                          ((fix eqn (m n : nat) {struct m} : bool :=
                                              match m return bool with
                                              | O =>
                                                  match n return bool with
                                                  | O => true
                                                  | S _ => false
                                                  end
                                              | S m' =>
                                                  match n return bool with
                                                  | O => false
                                                  | S n' => eqn m' n'
                                                  end
                                              end)
                                             match
                                               (fix size (s : list A₁) : nat :=
                                                  match s return nat with
                                                  | nil => O
                                                  | cons _ s' => S (size s')
                                                  end)
                                                 match s₁ return (list A₁) with
                                                 | nil => @nil A₁
                                                 | cons x _ => x
                                                 end return nat
                                             with
                                             | O => S x₁0
                                             | S l =>
                                                 (fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l0 => sub k l0
                                                        end
                                                    end) x₁0 l
                                             end O) false =>
                                  @None
                                    (ordinal
                                       ((fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end))
                              end H)
                             (match
                                Px₂ as Px
                                return
                                  (forall
                                     _ : @eq bool
                                           ((fix eqn (m n : nat) {struct m} : bool :=
                                               match m return bool with
                                               | O =>
                                                   match n return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end
                                               | S m' =>
                                                   match n return bool with
                                                   | O => false
                                                   | S n' => eqn m' n'
                                                   end
                                               end)
                                              match
                                                (fix size (s : list A₂) : nat :=
                                                   match s return nat with
                                                   | nil => O
                                                   | cons _ s' => S (size s')
                                                   end)
                                                  match s₂ return (list A₂) with
                                                  | nil => @nil A₂
                                                  | cons x _ => x
                                                  end return nat
                                              with
                                              | O => S x₂0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₂0 l
                                              end O) Px,
                                   option
                                     (ordinal
                                        ((fix size (s : list A₂) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x _ => x
                                           end)))
                              with
                              | true =>
                                  fun
                                    Px : @eq bool
                                           ((fix eqn (m n : nat) {struct m} : bool :=
                                               match m return bool with
                                               | O =>
                                                   match n return bool with
                                                   | O => true
                                                   | S _ => false
                                                   end
                                               | S m' =>
                                                   match n return bool with
                                                   | O => false
                                                   | S n' => eqn m' n'
                                                   end
                                               end)
                                              match
                                                (fix size (s : list A₂) : nat :=
                                                   match s return nat with
                                                   | nil => O
                                                   | cons _ s' => S (size s')
                                                   end)
                                                  match s₂ return (list A₂) with
                                                  | nil => @nil A₂
                                                  | cons x _ => x
                                                  end return nat
                                              with
                                              | O => S x₂0
                                              | S l =>
                                                  (fix sub (n m : nat) {struct n} : nat :=
                                                     match n return nat with
                                                     | O => n
                                                     | S k =>
                                                         match m return nat with
                                                         | O => n
                                                         | S l0 => sub k l0
                                                         end
                                                     end) x₂0 l
                                              end O) true =>
                                  @Some
                                    (ordinal
                                       ((fix size (s : list A₂) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end))
                                    (@Ordinal
                                       ((fix size (s : list A₂) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end) x₂0 Px)
                              | false =>
                                  fun
                                    _ : @eq bool
                                          ((fix eqn (m n : nat) {struct m} : bool :=
                                              match m return bool with
                                              | O =>
                                                  match n return bool with
                                                  | O => true
                                                  | S _ => false
                                                  end
                                              | S m' =>
                                                  match n return bool with
                                                  | O => false
                                                  | S n' => eqn m' n'
                                                  end
                                              end)
                                             match
                                               (fix size (s : list A₂) : nat :=
                                                  match s return nat with
                                                  | nil => O
                                                  | cons _ s' => S (size s')
                                                  end)
                                                 match s₂ return (list A₂) with
                                                 | nil => @nil A₂
                                                 | cons x _ => x
                                                 end return nat
                                             with
                                             | O => S x₂0
                                             | S l =>
                                                 (fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l0 => sub k l0
                                                        end
                                                    end) x₂0 l
                                             end O) false =>
                                  @None
                                    (ordinal
                                       ((fix size (s : list A₂) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end))
                              end H0))
                      with
                      | bool_R_true_R =>
                          fun
                            (Px₁ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s : list A₁) : nat :=
                                             match s return nat with
                                             | nil => O
                                             | cons _ s' => S (size s')
                                             end)
                                            match s₁ return (list A₁) with
                                            | nil => @nil A₁
                                            | cons x _ => x
                                            end return nat
                                        with
                                        | O => S x₁0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x₁0 l
                                        end O) true)
                            (Px₂ : @eq bool
                                     ((fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end)
                                        match
                                          (fix size (s : list A₂) : nat :=
                                             match s return nat with
                                             | nil => O
                                             | cons _ s' => S (size s')
                                             end)
                                            match s₂ return (list A₂) with
                                            | nil => @nil A₂
                                            | cons x _ => x
                                            end return nat
                                        with
                                        | O => S x₂0
                                        | S l =>
                                            (fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l0 => sub k l0
                                                   end
                                               end) x₂0 l
                                        end O) true)
                            (Px_R : @eq_R bool bool bool_R
                                      ((fix eqn (m n : nat) {struct m} : bool :=
                                          match m return bool with
                                          | O =>
                                              match n return bool with
                                              | O => true
                                              | S _ => false
                                              end
                                          | S m' =>
                                              match n return bool with
                                              | O => false
                                              | S n' => eqn m' n'
                                              end
                                          end)
                                         match
                                           (fix size (s : list A₁) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end)
                                             match s₁ return (list A₁) with
                                             | nil => @nil A₁
                                             | cons x _ => x
                                             end return nat
                                         with
                                         | O => S x₁0
                                         | S l =>
                                             (fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l0 => sub k l0
                                                    end
                                                end) x₁0 l
                                         end O)
                                      ((fix eqn (m n : nat) {struct m} : bool :=
                                          match m return bool with
                                          | O =>
                                              match n return bool with
                                              | O => true
                                              | S _ => false
                                              end
                                          | S m' =>
                                              match n return bool with
                                              | O => false
                                              | S n' => eqn m' n'
                                              end
                                          end)
                                         match
                                           (fix size (s : list A₂) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end)
                                             match s₂ return (list A₂) with
                                             | nil => @nil A₂
                                             | cons x _ => x
                                             end return nat
                                         with
                                         | O => S x₂0
                                         | S l =>
                                             (fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l0 => sub k l0
                                                    end
                                                end) x₂0 l
                                         end O)
                                      ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                                          fix eqn (m n : nat) {struct m} : bool :=
                                            match m return bool with
                                            | O =>
                                                match n return bool with
                                                | O => true
                                                | S _ => false
                                                end
                                            | S m' =>
                                                match n return bool with
                                                | O => false
                                                | S n' => eqn m' n'
                                                end
                                            end in
                                        let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                                          fix eqn (m n : nat) {struct m} : bool :=
                                            match m return bool with
                                            | O =>
                                                match n return bool with
                                                | O => true
                                                | S _ => false
                                                end
                                            | S m' =>
                                                match n return bool with
                                                | O => false
                                                | S n' => eqn m' n'
                                                end
                                            end in
                                        fix
                                        eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂)
                                              (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct
                                              m_R} :
                                          bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                                          match
                                            m_R in (nat_R m₁0 m₂0)
                                            return
                                              (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                                          with
                                          | nat_R_O_R =>
                                              match
                                                n_R in (nat_R n₁0 n₂0)
                                                return
                                                  (bool_R
                                                     match n₁0 return bool with
                                                     | O => true
                                                     | S _ => false
                                                     end
                                                     match n₂0 return bool with
                                                     | O => true
                                                     | S _ => false
                                                     end)
                                              with
                                              | nat_R_O_R => bool_R_true_R
                                              | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                              end
                                          | @nat_R_S_R m'₁ m'₂ m'_R =>
                                              match
                                                n_R in (nat_R n₁0 n₂0)
                                                return
                                                  (bool_R
                                                     match n₁0 return bool with
                                                     | O => false
                                                     | S n' => fix_eqn_1 m'₁ n'
                                                     end
                                                     match n₂0 return bool with
                                                     | O => false
                                                     | S n' => fix_eqn_2 m'₂ n'
                                                     end)
                                              with
                                              | nat_R_O_R => bool_R_false_R
                                              | @nat_R_S_R n'₁ n'₂ n'_R =>
                                                  eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                              end
                                          end)
                                         match
                                           (fix size (s : list A₁) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end)
                                             match s₁ return (list A₁) with
                                             | nil => @nil A₁
                                             | cons x _ => x
                                             end return nat
                                         with
                                         | O => S x₁0
                                         | S l =>
                                             (fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l0 => sub k l0
                                                    end
                                                end) x₁0 l
                                         end
                                         match
                                           (fix size (s : list A₂) : nat :=
                                              match s return nat with
                                              | nil => O
                                              | cons _ s' => S (size s')
                                              end)
                                             match s₂ return (list A₂) with
                                             | nil => @nil A₂
                                             | cons x _ => x
                                             end return nat
                                         with
                                         | O => S x₂0
                                         | S l =>
                                             (fix sub (n m : nat) {struct n} : nat :=
                                                match n return nat with
                                                | O => n
                                                | S k =>
                                                    match m return nat with
                                                    | O => n
                                                    | S l0 => sub k l0
                                                    end
                                                end) x₂0 l
                                         end
                                         match
                                           (let fix_size_1 : forall _ : list A₁, nat :=
                                              fix size (s : list A₁) : nat :=
                                                match s return nat with
                                                | nil => O
                                                | cons _ s' => S (size s')
                                                end in
                                            let fix_size_2 : forall _ : list A₂, nat :=
                                              fix size (s : list A₂) : nat :=
                                                match s return nat with
                                                | nil => O
                                                | cons _ s' => S (size s')
                                                end in
                                            fix
                                            size_R (s₁2 : list A₁) 
                                                   (s₂2 : list A₂)
                                                   (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2)
                                                   {struct s_R2} :
                                              nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                              match
                                                s_R2 in (list_R _ s₁3 s₂3)
                                                return
                                                  (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                              with
                                              | @list_R_nil_R _ _ _ => nat_R_O_R
                                              | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1
                                                s'_R1 =>
                                                  @nat_R_S_R (fix_size_1 s'₁1)
                                                    (fix_size_2 s'₂1)
                                                    (size_R s'₁1 s'₂1 s'_R1)
                                              end)
                                             match s₁ return (list A₁) with
                                             | nil => @nil A₁
                                             | cons x _ => x
                                             end
                                             match s₂ return (list A₂) with
                                             | nil => @nil A₂
                                             | cons x _ => x
                                             end
                                             match
                                               s_R in (list_R _ s₁2 s₂2)
                                               return
                                                 (@list_R A₁ A₂ A_R
                                                    match s₁2 return (list A₁) with
                                                    | nil => @nil A₁
                                                    | cons x _ => x
                                                    end
                                                    match s₂2 return (list A₂) with
                                                    | nil => @nil A₂
                                                    | cons x _ => x
                                                    end)
                                             with
                                             | @list_R_nil_R _ _ _ =>
                                                 @list_R_nil_R A₁ A₂ A_R
                                             | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1
                                               _ => x_R1
                                             end in (nat_R m₁ m₂)
                                           return
                                             (nat_R
                                                match m₁ return nat with
                                                | O => S x₁0
                                                | S l =>
                                                    (fix sub (n m : nat) {struct n} :
                                                       nat :=
                                                       match n return nat with
                                                       | O => n
                                                       | S k =>
                                                           match m return nat with
                                                           | O => n
                                                           | S l0 => sub k l0
                                                           end
                                                       end) x₁0 l
                                                end
                                                match m₂ return nat with
                                                | O => S x₂0
                                                | S l =>
                                                    (fix sub (n m : nat) {struct n} :
                                                       nat :=
                                                       match n return nat with
                                                       | O => n
                                                       | S k =>
                                                           match m return nat with
                                                           | O => n
                                                           | S l0 => sub k l0
                                                           end
                                                       end) x₂0 l
                                                end)
                                         with
                                         | nat_R_O_R => @nat_R_S_R x₁0 x₂0 x_R0
                                         | @nat_R_S_R l₁ l₂ l_R =>
                                             (let fix_sub_1 :
                                                forall (_ : nat) (_ : nat), nat :=
                                                fix sub (n m : nat) {struct n} : nat :=
                                                  match n return nat with
                                                  | O => n
                                                  | S k =>
                                                      match m return nat with
                                                      | O => n
                                                      | S l => sub k l
                                                      end
                                                  end in
                                              let fix_sub_2 :
                                                forall (_ : nat) (_ : nat), nat :=
                                                fix sub (n m : nat) {struct n} : nat :=
                                                  match n return nat with
                                                  | O => n
                                                  | S k =>
                                                      match m return nat with
                                                      | O => n
                                                      | S l => sub k l
                                                      end
                                                  end in
                                              fix
                                              sub_R (n₁ n₂ : nat) 
                                                    (n_R : nat_R n₁ n₂) 
                                                    (m₁ m₂ : nat) 
                                                    (m_R : nat_R m₁ m₂) {struct n_R} :
                                                nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                                let gen_path :
                                                  let
                                                    fix sub (n m : nat) {struct n} : nat :=
                                                      match n return nat with
                                                      | O => n
                                                      | S k =>
                                                          match m return nat with
                                                          | O => n
                                                          | S l => sub k l
                                                          end
                                                      end in
                                                  forall n m : nat,
                                                  @eq nat
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l => sub k l
                                                        end
                                                    end (sub n m) :=
                                                  let
                                                    fix sub (n m : nat) {struct n} : nat :=
                                                      match n return nat with
                                                      | O => n
                                                      | S k =>
                                                          match m return nat with
                                                          | O => n
                                                          | S l => sub k l
                                                          end
                                                      end in
                                                  fun n m : nat =>
                                                  match
                                                    n as n0
                                                    return
                                                      (@eq nat
                                                         match n0 return nat with
                                                         | O => n0
                                                         | S k =>
                                                             match m return nat with
                                                             | O => n0
                                                             | S l => sub k l
                                                             end
                                                         end (sub n0 m))
                                                  with
                                                  | O => @Logic.eq_refl nat (sub O m)
                                                  | S n0 =>
                                                      @Logic.eq_refl nat (sub (S n0) m)
                                                  end in
                                                @eq_rect nat
                                                  match n₁ return nat with
                                                  | O => n₁
                                                  | S k =>
                                                      match m₁ return nat with
                                                      | O => n₁
                                                      | S l => fix_sub_1 k l
                                                      end
                                                  end
                                                  (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                                  (@eq_rect nat
                                                     match n₂ return nat with
                                                     | O => n₂
                                                     | S k =>
                                                         match m₂ return nat with
                                                         | O => n₂
                                                         | S l => fix_sub_2 k l
                                                         end
                                                     end
                                                     (fun x : nat =>
                                                      nat_R
                                                        match n₁ return nat with
                                                        | O => n₁
                                                        | S k =>
                                                            match m₁ return nat with
                                                            | O => n₁
                                                            | S l => fix_sub_1 k l
                                                            end
                                                        end x)
                                                     match
                                                       n_R in (nat_R n₁0 n₂0)
                                                       return
                                                         (nat_R
                                                            match n₁0 return nat with
                                                            | O => n₁
                                                            | S k =>
                                                              match m₁ return nat with
                                                              | O => n₁
                                                              | S l => fix_sub_1 k l
                                                              end
                                                            end
                                                            match n₂0 return nat with
                                                            | O => n₂
                                                            | S k =>
                                                              match m₂ return nat with
                                                              | O => n₂
                                                              | S l => fix_sub_2 k l
                                                              end
                                                            end)
                                                     with
                                                     | nat_R_O_R => n_R
                                                     | @nat_R_S_R k₁ k₂ k_R =>
                                                         match
                                                           m_R in (nat_R m₁0 m₂0)
                                                           return
                                                             (nat_R
                                                              match m₁0 return nat with
                                                              | O => n₁
                                                              | S l => fix_sub_1 k₁ l
                                                              end
                                                              match m₂0 return nat with
                                                              | O => n₂
                                                              | S l => fix_sub_2 k₂ l
                                                              end)
                                                         with
                                                         | nat_R_O_R => n_R
                                                         | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                             sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                                         end
                                                     end (fix_sub_2 n₂ m₂) 
                                                     (gen_path n₂ m₂)) 
                                                  (fix_sub_1 n₁ m₁) 
                                                  (gen_path n₁ m₁)) x₁0 x₂0 x_R0 l₁ l₂ l_R
                                         end O O nat_R_O_R) true true bool_R_true_R Px₁ Px₂)
                          =>
                          @option_R_Some_R
                            (ordinal
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end))
                            (ordinal
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end))
                            (@ordinal_R
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end)
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end)
                               ((let fix_size_1 : forall _ : list A₁, nat :=
                                   fix size (s : list A₁) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 let fix_size_2 : forall _ : list A₂, nat :=
                                   fix size (s : list A₂) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 fix
                                 size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                        (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                   nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                   match
                                     s_R2 in (list_R _ s₁3 s₂3)
                                     return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                   with
                                   | @list_R_nil_R _ _ _ => nat_R_O_R
                                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                       @nat_R_S_R (fix_size_1 s'₁1) 
                                         (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end
                                  match
                                    s_R in (list_R _ s₁2 s₂2)
                                    return
                                      (@list_R A₁ A₂ A_R
                                         match s₁2 return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x _ => x
                                         end
                                         match s₂2 return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x _ => x
                                         end)
                                  with
                                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                  | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                  end))
                            (@Ordinal
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end) x₁0 Px₁)
                            (@Ordinal
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end) x₂0 Px₂)
                            (@ordinal_R_Ordinal_R
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end)
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end)
                               ((let fix_size_1 : forall _ : list A₁, nat :=
                                   fix size (s : list A₁) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 let fix_size_2 : forall _ : list A₂, nat :=
                                   fix size (s : list A₂) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 fix
                                 size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                        (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                   nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                   match
                                     s_R2 in (list_R _ s₁3 s₂3)
                                     return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                   with
                                   | @list_R_nil_R _ _ _ => nat_R_O_R
                                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                       @nat_R_S_R (fix_size_1 s'₁1) 
                                         (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end
                                  match
                                    s_R in (list_R _ s₁2 s₂2)
                                    return
                                      (@list_R A₁ A₂ A_R
                                         match s₁2 return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x _ => x
                                         end
                                         match s₂2 return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x _ => x
                                         end)
                                  with
                                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                  | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                  end) x₁0 x₂0 x_R0 Px₁ Px₂ Px_R)
                      | bool_R_false_R =>
                          fun
                            (H : @eq bool
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end return nat
                                      with
                                      | O => S x₁0
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₁0 l
                                      end O) false)
                            (H0 : @eq bool
                                    ((fix eqn (m n : nat) {struct m} : bool :=
                                        match m return bool with
                                        | O =>
                                            match n return bool with
                                            | O => true
                                            | S _ => false
                                            end
                                        | S m' =>
                                            match n return bool with
                                            | O => false
                                            | S n' => eqn m' n'
                                            end
                                        end)
                                       match
                                         (fix size (s : list A₂) : nat :=
                                            match s return nat with
                                            | nil => O
                                            | cons _ s' => S (size s')
                                            end)
                                           match s₂ return (list A₂) with
                                           | nil => @nil A₂
                                           | cons x _ => x
                                           end return nat
                                       with
                                       | O => S x₂0
                                       | S l =>
                                           (fix sub (n m : nat) {struct n} : nat :=
                                              match n return nat with
                                              | O => n
                                              | S k =>
                                                  match m return nat with
                                                  | O => n
                                                  | S l0 => sub k l0
                                                  end
                                              end) x₂0 l
                                       end O) false)
                            (_ : @eq_R bool bool bool_R
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end return nat
                                      with
                                      | O => S x₁0
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₁0 l
                                      end O)
                                   ((fix eqn (m n : nat) {struct m} : bool :=
                                       match m return bool with
                                       | O =>
                                           match n return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                       | S m' =>
                                           match n return bool with
                                           | O => false
                                           | S n' => eqn m' n'
                                           end
                                       end)
                                      match
                                        (fix size (s : list A₂) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end return nat
                                      with
                                      | O => S x₂0
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₂0 l
                                      end O)
                                   ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                                       fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end in
                                     let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                                       fix eqn (m n : nat) {struct m} : bool :=
                                         match m return bool with
                                         | O =>
                                             match n return bool with
                                             | O => true
                                             | S _ => false
                                             end
                                         | S m' =>
                                             match n return bool with
                                             | O => false
                                             | S n' => eqn m' n'
                                             end
                                         end in
                                     fix
                                     eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                           (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                                       bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                                       match
                                         m_R in (nat_R m₁0 m₂0)
                                         return
                                           (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                                       with
                                       | nat_R_O_R =>
                                           match
                                             n_R in (nat_R n₁0 n₂0)
                                             return
                                               (bool_R
                                                  match n₁0 return bool with
                                                  | O => true
                                                  | S _ => false
                                                  end
                                                  match n₂0 return bool with
                                                  | O => true
                                                  | S _ => false
                                                  end)
                                           with
                                           | nat_R_O_R => bool_R_true_R
                                           | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                           end
                                       | @nat_R_S_R m'₁ m'₂ m'_R =>
                                           match
                                             n_R in (nat_R n₁0 n₂0)
                                             return
                                               (bool_R
                                                  match n₁0 return bool with
                                                  | O => false
                                                  | S n' => fix_eqn_1 m'₁ n'
                                                  end
                                                  match n₂0 return bool with
                                                  | O => false
                                                  | S n' => fix_eqn_2 m'₂ n'
                                                  end)
                                           with
                                           | nat_R_O_R => bool_R_false_R
                                           | @nat_R_S_R n'₁ n'₂ n'_R =>
                                               eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                           end
                                       end)
                                      match
                                        (fix size (s : list A₁) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end return nat
                                      with
                                      | O => S x₁0
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₁0 l
                                      end
                                      match
                                        (fix size (s : list A₂) : nat :=
                                           match s return nat with
                                           | nil => O
                                           | cons _ s' => S (size s')
                                           end)
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end return nat
                                      with
                                      | O => S x₂0
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₂0 l
                                      end
                                      match
                                        (let fix_size_1 : forall _ : list A₁, nat :=
                                           fix size (s : list A₁) : nat :=
                                             match s return nat with
                                             | nil => O
                                             | cons _ s' => S (size s')
                                             end in
                                         let fix_size_2 : forall _ : list A₂, nat :=
                                           fix size (s : list A₂) : nat :=
                                             match s return nat with
                                             | nil => O
                                             | cons _ s' => S (size s')
                                             end in
                                         fix
                                         size_R (s₁2 : list A₁) 
                                                (s₂2 : list A₂)
                                                (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct
                                                s_R2} :
                                           nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                           match
                                             s_R2 in (list_R _ s₁3 s₂3)
                                             return
                                               (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                           with
                                           | @list_R_nil_R _ _ _ => nat_R_O_R
                                           | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1
                                             s'_R1 =>
                                               @nat_R_S_R (fix_size_1 s'₁1)
                                                 (fix_size_2 s'₂1) 
                                                 (size_R s'₁1 s'₂1 s'_R1)
                                           end)
                                          match s₁ return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end
                                          match s₂ return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end
                                          match
                                            s_R in (list_R _ s₁2 s₂2)
                                            return
                                              (@list_R A₁ A₂ A_R
                                                 match s₁2 return (list A₁) with
                                                 | nil => @nil A₁
                                                 | cons x _ => x
                                                 end
                                                 match s₂2 return (list A₂) with
                                                 | nil => @nil A₂
                                                 | cons x _ => x
                                                 end)
                                          with
                                          | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                          | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1
                                            _ => x_R1
                                          end in (nat_R m₁ m₂)
                                        return
                                          (nat_R
                                             match m₁ return nat with
                                             | O => S x₁0
                                             | S l =>
                                                 (fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l0 => sub k l0
                                                        end
                                                    end) x₁0 l
                                             end
                                             match m₂ return nat with
                                             | O => S x₂0
                                             | S l =>
                                                 (fix sub (n m : nat) {struct n} : nat :=
                                                    match n return nat with
                                                    | O => n
                                                    | S k =>
                                                        match m return nat with
                                                        | O => n
                                                        | S l0 => sub k l0
                                                        end
                                                    end) x₂0 l
                                             end)
                                      with
                                      | nat_R_O_R => @nat_R_S_R x₁0 x₂0 x_R0
                                      | @nat_R_S_R l₁ l₂ l_R =>
                                          (let fix_sub_1 :
                                             forall (_ : nat) (_ : nat), nat :=
                                             fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l => sub k l
                                                   end
                                               end in
                                           let fix_sub_2 :
                                             forall (_ : nat) (_ : nat), nat :=
                                             fix sub (n m : nat) {struct n} : nat :=
                                               match n return nat with
                                               | O => n
                                               | S k =>
                                                   match m return nat with
                                                   | O => n
                                                   | S l => sub k l
                                                   end
                                               end in
                                           fix
                                           sub_R (n₁ n₂ : nat) 
                                                 (n_R : nat_R n₁ n₂) 
                                                 (m₁ m₂ : nat) 
                                                 (m_R : nat_R m₁ m₂) {struct n_R} :
                                             nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                             let gen_path :
                                               let
                                                 fix sub (n m : nat) {struct n} : nat :=
                                                   match n return nat with
                                                   | O => n
                                                   | S k =>
                                                       match m return nat with
                                                       | O => n
                                                       | S l => sub k l
                                                       end
                                                   end in
                                               forall n m : nat,
                                               @eq nat
                                                 match n return nat with
                                                 | O => n
                                                 | S k =>
                                                     match m return nat with
                                                     | O => n
                                                     | S l => sub k l
                                                     end
                                                 end (sub n m) :=
                                               let
                                                 fix sub (n m : nat) {struct n} : nat :=
                                                   match n return nat with
                                                   | O => n
                                                   | S k =>
                                                       match m return nat with
                                                       | O => n
                                                       | S l => sub k l
                                                       end
                                                   end in
                                               fun n m : nat =>
                                               match
                                                 n as n0
                                                 return
                                                   (@eq nat
                                                      match n0 return nat with
                                                      | O => n0
                                                      | S k =>
                                                          match m return nat with
                                                          | O => n0
                                                          | S l => sub k l
                                                          end
                                                      end (sub n0 m))
                                               with
                                               | O => @Logic.eq_refl nat (sub O m)
                                               | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                               end in
                                             @eq_rect nat
                                               match n₁ return nat with
                                               | O => n₁
                                               | S k =>
                                                   match m₁ return nat with
                                                   | O => n₁
                                                   | S l => fix_sub_1 k l
                                                   end
                                               end
                                               (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                               (@eq_rect nat
                                                  match n₂ return nat with
                                                  | O => n₂
                                                  | S k =>
                                                      match m₂ return nat with
                                                      | O => n₂
                                                      | S l => fix_sub_2 k l
                                                      end
                                                  end
                                                  (fun x : nat =>
                                                   nat_R
                                                     match n₁ return nat with
                                                     | O => n₁
                                                     | S k =>
                                                         match m₁ return nat with
                                                         | O => n₁
                                                         | S l => fix_sub_1 k l
                                                         end
                                                     end x)
                                                  match
                                                    n_R in (nat_R n₁0 n₂0)
                                                    return
                                                      (nat_R
                                                         match n₁0 return nat with
                                                         | O => n₁
                                                         | S k =>
                                                             match m₁ return nat with
                                                             | O => n₁
                                                             | S l => fix_sub_1 k l
                                                             end
                                                         end
                                                         match n₂0 return nat with
                                                         | O => n₂
                                                         | S k =>
                                                             match m₂ return nat with
                                                             | O => n₂
                                                             | S l => fix_sub_2 k l
                                                             end
                                                         end)
                                                  with
                                                  | nat_R_O_R => n_R
                                                  | @nat_R_S_R k₁ k₂ k_R =>
                                                      match
                                                        m_R in (nat_R m₁0 m₂0)
                                                        return
                                                          (nat_R
                                                             match m₁0 return nat with
                                                             | O => n₁
                                                             | S l => fix_sub_1 k₁ l
                                                             end
                                                             match m₂0 return nat with
                                                             | O => n₂
                                                             | S l => fix_sub_2 k₂ l
                                                             end)
                                                      with
                                                      | nat_R_O_R => n_R
                                                      | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                          sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                                      end
                                                  end (fix_sub_2 n₂ m₂) 
                                                  (gen_path n₂ m₂)) 
                                               (fix_sub_1 n₁ m₁) 
                                               (gen_path n₁ m₁)) x₁0 x₂0 x_R0 l₁ l₂ l_R
                                      end O O nat_R_O_R) false false bool_R_false_R H H0)
                          =>
                          @option_R_None_R
                            (ordinal
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end))
                            (ordinal
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end))
                            (@ordinal_R
                               ((fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end)
                               ((fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end)
                               ((let fix_size_1 : forall _ : list A₁, nat :=
                                   fix size (s : list A₁) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 let fix_size_2 : forall _ : list A₂, nat :=
                                   fix size (s : list A₂) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 fix
                                 size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                        (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                   nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                   match
                                     s_R2 in (list_R _ s₁3 s₂3)
                                     return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                   with
                                   | @list_R_nil_R _ _ _ => nat_R_O_R
                                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                       @nat_R_S_R (fix_size_1 s'₁1) 
                                         (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end
                                  match
                                    s_R in (list_R _ s₁2 s₂2)
                                    return
                                      (@list_R A₁ A₂ A_R
                                         match s₁2 return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x _ => x
                                         end
                                         match s₂2 return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x _ => x
                                         end)
                                  with
                                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                  | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                  end))
                      end
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₁0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₁0 l
                              end O))
                        (@Logic.eq_refl bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₂0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₂0 l
                              end O))
                        (@eq_R_eq_refl_R bool bool bool_R
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₁0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₁0 l
                              end O)
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₂0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₂0 l
                              end O)
                           ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                               fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end in
                             let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                               fix eqn (m n : nat) {struct m} : bool :=
                                 match m return bool with
                                 | O =>
                                     match n return bool with
                                     | O => true
                                     | S _ => false
                                     end
                                 | S m' =>
                                     match n return bool with
                                     | O => false
                                     | S n' => eqn m' n'
                                     end
                                 end in
                             fix
                             eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                   (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                               bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                               match
                                 m_R in (nat_R m₁0 m₂0)
                                 return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                               with
                               | nat_R_O_R =>
                                   match
                                     n_R in (nat_R n₁0 n₂0)
                                     return
                                       (bool_R
                                          match n₁0 return bool with
                                          | O => true
                                          | S _ => false
                                          end
                                          match n₂0 return bool with
                                          | O => true
                                          | S _ => false
                                          end)
                                   with
                                   | nat_R_O_R => bool_R_true_R
                                   | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                   end
                               | @nat_R_S_R m'₁ m'₂ m'_R =>
                                   match
                                     n_R in (nat_R n₁0 n₂0)
                                     return
                                       (bool_R
                                          match n₁0 return bool with
                                          | O => false
                                          | S n' => fix_eqn_1 m'₁ n'
                                          end
                                          match n₂0 return bool with
                                          | O => false
                                          | S n' => fix_eqn_2 m'₂ n'
                                          end)
                                   with
                                   | nat_R_O_R => bool_R_false_R
                                   | @nat_R_S_R n'₁ n'₂ n'_R =>
                                       eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                   end
                               end)
                              match
                                (fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₁0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₁0 l
                              end
                              match
                                (fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₂0
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₂0 l
                              end
                              match
                                (let fix_size_1 : forall _ : list A₁, nat :=
                                   fix size (s : list A₁) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 let fix_size_2 : forall _ : list A₂, nat :=
                                   fix size (s : list A₂) : nat :=
                                     match s return nat with
                                     | nil => O
                                     | cons _ s' => S (size s')
                                     end in
                                 fix
                                 size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                        (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                   nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                   match
                                     s_R2 in (list_R _ s₁3 s₂3)
                                     return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                   with
                                   | @list_R_nil_R _ _ _ => nat_R_O_R
                                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                       @nat_R_S_R (fix_size_1 s'₁1) 
                                         (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end
                                  match
                                    s_R in (list_R _ s₁2 s₂2)
                                    return
                                      (@list_R A₁ A₂ A_R
                                         match s₁2 return (list A₁) with
                                         | nil => @nil A₁
                                         | cons x _ => x
                                         end
                                         match s₂2 return (list A₂) with
                                         | nil => @nil A₂
                                         | cons x _ => x
                                         end)
                                  with
                                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                  | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                  end in (nat_R m₁ m₂)
                                return
                                  (nat_R
                                     match m₁ return nat with
                                     | O => S x₁0
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x₁0 l
                                     end
                                     match m₂ return nat with
                                     | O => S x₂0
                                     | S l =>
                                         (fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l0 => sub k l0
                                                end
                                            end) x₂0 l
                                     end)
                              with
                              | nat_R_O_R => @nat_R_S_R x₁0 x₂0 x_R0
                              | @nat_R_S_R l₁ l₂ l_R =>
                                  (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                                     fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l => sub k l
                                           end
                                       end in
                                   let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                                     fix sub (n m : nat) {struct n} : nat :=
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l => sub k l
                                           end
                                       end in
                                   fix
                                   sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                                         (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                                     nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                     let gen_path :
                                       let
                                         fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l => sub k l
                                               end
                                           end in
                                       forall n m : nat,
                                       @eq nat
                                         match n return nat with
                                         | O => n
                                         | S k =>
                                             match m return nat with
                                             | O => n
                                             | S l => sub k l
                                             end
                                         end (sub n m) :=
                                       let
                                         fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l => sub k l
                                               end
                                           end in
                                       fun n m : nat =>
                                       match
                                         n as n0
                                         return
                                           (@eq nat
                                              match n0 return nat with
                                              | O => n0
                                              | S k =>
                                                  match m return nat with
                                                  | O => n0
                                                  | S l => sub k l
                                                  end
                                              end (sub n0 m))
                                       with
                                       | O => @Logic.eq_refl nat (sub O m)
                                       | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                       end in
                                     @eq_rect nat
                                       match n₁ return nat with
                                       | O => n₁
                                       | S k =>
                                           match m₁ return nat with
                                           | O => n₁
                                           | S l => fix_sub_1 k l
                                           end
                                       end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                       (@eq_rect nat
                                          match n₂ return nat with
                                          | O => n₂
                                          | S k =>
                                              match m₂ return nat with
                                              | O => n₂
                                              | S l => fix_sub_2 k l
                                              end
                                          end
                                          (fun x : nat =>
                                           nat_R
                                             match n₁ return nat with
                                             | O => n₁
                                             | S k =>
                                                 match m₁ return nat with
                                                 | O => n₁
                                                 | S l => fix_sub_1 k l
                                                 end
                                             end x)
                                          match
                                            n_R in (nat_R n₁0 n₂0)
                                            return
                                              (nat_R
                                                 match n₁0 return nat with
                                                 | O => n₁
                                                 | S k =>
                                                     match m₁ return nat with
                                                     | O => n₁
                                                     | S l => fix_sub_1 k l
                                                     end
                                                 end
                                                 match n₂0 return nat with
                                                 | O => n₂
                                                 | S k =>
                                                     match m₂ return nat with
                                                     | O => n₂
                                                     | S l => fix_sub_2 k l
                                                     end
                                                 end)
                                          with
                                          | nat_R_O_R => n_R
                                          | @nat_R_S_R k₁ k₂ k_R =>
                                              match
                                                m_R in (nat_R m₁0 m₂0)
                                                return
                                                  (nat_R
                                                     match m₁0 return nat with
                                                     | O => n₁
                                                     | S l => fix_sub_1 k₁ l
                                                     end
                                                     match m₂0 return nat with
                                                     | O => n₂
                                                     | S l => fix_sub_2 k₂ l
                                                     end)
                                              with
                                              | nat_R_O_R => n_R
                                              | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                  sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                              end
                                          end (fix_sub_2 n₂ m₂) 
                                          (gen_path n₂ m₂)) (fix_sub_1 n₁ m₁)
                                       (gen_path n₁ m₁)) x₁0 x₂0 x_R0 l₁ l₂ l_R
                              end O O nat_R_O_R)) in (option_R _ u₁ u₂)
                      return
                        (@list_R
                           (ordinal
                              ((fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end))
                           (ordinal
                              ((fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end))
                           (@ordinal_R
                              ((fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end)
                              ((fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end)
                              ((let fix_size_1 : forall _ : list A₁, nat :=
                                  fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end in
                                let fix_size_2 : forall _ : list A₂, nat :=
                                  fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end in
                                fix
                                size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                       (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                  nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                  match
                                    s_R2 in (list_R _ s₁3 s₂3)
                                    return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                  with
                                  | @list_R_nil_R _ _ _ => nat_R_O_R
                                  | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                      @nat_R_S_R (fix_size_1 s'₁1) 
                                        (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end
                                 match
                                   s_R in (list_R _ s₁2 s₂2)
                                   return
                                     (@list_R A₁ A₂ A_R
                                        match s₁2 return (list A₁) with
                                        | nil => @nil A₁
                                        | cons x _ => x
                                        end
                                        match s₂2 return (list A₂) with
                                        | nil => @nil A₂
                                        | cons x _ => x
                                        end)
                                 with
                                 | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                 | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                 end))
                           match
                             u₁
                             return
                               (list
                                  (ordinal
                                     ((fix size (s : list A₁) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₁ return (list A₁) with
                                        | nil => @nil A₁
                                        | cons x _ => x
                                        end)))
                           with
                           | Some y =>
                               @cons
                                 (ordinal
                                    ((fix size (s : list A₁) : nat :=
                                        match s return nat with
                                        | nil => O
                                        | cons _ s' => S (size s')
                                        end)
                                       match s₁ return (list A₁) with
                                       | nil => @nil A₁
                                       | cons x _ => x
                                       end)) y (fix_pmap_1 s'₁0)
                           | None => fix_pmap_1 s'₁0
                           end
                           match
                             u₂
                             return
                               (list
                                  (ordinal
                                     ((fix size (s : list A₂) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₂ return (list A₂) with
                                        | nil => @nil A₂
                                        | cons x _ => x
                                        end)))
                           with
                           | Some y =>
                               @cons
                                 (ordinal
                                    ((fix size (s : list A₂) : nat :=
                                        match s return nat with
                                        | nil => O
                                        | cons _ s' => S (size s')
                                        end)
                                       match s₂ return (list A₂) with
                                       | nil => @nil A₂
                                       | cons x _ => x
                                       end)) y (fix_pmap_2 s'₂0)
                           | None => fix_pmap_2 s'₂0
                           end)
                    with
                    | @option_R_Some_R _ _ _ y₁ y₂ y_R =>
                        @list_R_cons_R
                          (ordinal
                             ((fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end))
                          (ordinal
                             ((fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end))
                          (@ordinal_R
                             ((fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end)
                             ((fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end)
                             ((let fix_size_1 : forall _ : list A₁, nat :=
                                 fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end in
                               let fix_size_2 : forall _ : list A₂, nat :=
                                 fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end in
                               fix
                               size_R (s₁2 : list A₁) (s₂2 : list A₂)
                                      (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2) {struct s_R2} :
                                 nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                                 match
                                   s_R2 in (list_R _ s₁3 s₂3)
                                   return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                                 with
                                 | @list_R_nil_R _ _ _ => nat_R_O_R
                                 | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁1 s'₂1 s'_R1 =>
                                     @nat_R_S_R (fix_size_1 s'₁1) 
                                       (fix_size_2 s'₂1) (size_R s'₁1 s'₂1 s'_R1)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end
                                match
                                  s_R in (list_R _ s₁2 s₂2)
                                  return
                                    (@list_R A₁ A₂ A_R
                                       match s₁2 return (list A₁) with
                                       | nil => @nil A₁
                                       | cons x _ => x
                                       end
                                       match s₂2 return (list A₂) with
                                       | nil => @nil A₂
                                       | cons x _ => x
                                       end)
                                with
                                | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                | @list_R_cons_R _ _ _ x₁1 x₂1 x_R1 s'₁1 s'₂1 _ => x_R1
                                end)) y₁ y₂ y_R (fix_pmap_1 s'₁0) 
                          (fix_pmap_2 s'₂0) (pmap_R s'₁0 s'₂0 s'_R0)
                    | @option_R_None_R _ _ _ => pmap_R s'₁0 s'₂0 s'_R0
                    end
                end)
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₁) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end))
               ((fix iota (m n : nat) {struct n} : list nat :=
                   match n return (list nat) with
                   | O => @nil nat
                   | S n' => @cons nat m (iota (S m) n')
                   end) O
                  ((fix size (s : list A₂) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end))
               ((let fix_iota_1 : forall (_ : nat) (_ : nat), list nat :=
                   fix iota (m n : nat) {struct n} : list nat :=
                     match n return (list nat) with
                     | O => @nil nat
                     | S n' => @cons nat m (iota (S m) n')
                     end in
                 let fix_iota_2 : forall (_ : nat) (_ : nat), list nat :=
                   fix iota (m n : nat) {struct n} : list nat :=
                     match n return (list nat) with
                     | O => @nil nat
                     | S n' => @cons nat m (iota (S m) n')
                     end in
                 fix
                 iota_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat) 
                        (n_R : nat_R n₁ n₂) {struct n_R} :
                   @list_R nat nat nat_R (fix_iota_1 m₁ n₁) (fix_iota_2 m₂ n₂) :=
                   match
                     n_R in (nat_R n₁0 n₂0)
                     return (@list_R nat nat nat_R (fix_iota_1 m₁ n₁0) (fix_iota_2 m₂ n₂0))
                   with
                   | nat_R_O_R => @list_R_nil_R nat nat nat_R
                   | @nat_R_S_R n'₁ n'₂ n'_R =>
                       @list_R_cons_R nat nat nat_R m₁ m₂ m_R (fix_iota_1 (S m₁) n'₁)
                         (fix_iota_2 (S m₂) n'₂)
                         (iota_R (S m₁) (S m₂) (@nat_R_S_R m₁ m₂ m_R) n'₁ n'₂ n'_R)
                   end) O O nat_R_O_R
                  ((fix size (s : list A₁) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end)
                  ((fix size (s : list A₂) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end)
                  ((let fix_size_1 : forall _ : list A₁, nat :=
                      fix size (s : list A₁) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end in
                    let fix_size_2 : forall _ : list A₂, nat :=
                      fix size (s : list A₂) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end in
                    fix
                    size_R (s₁1 : list A₁) (s₂1 : list A₂)
                           (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                      nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                      match
                        s_R1 in (list_R _ s₁2 s₂2)
                        return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                      with
                      | @list_R_nil_R _ _ _ => nat_R_O_R
                      | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                          @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                            (size_R s'₁0 s'₂0 s'_R0)
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end
                     match
                       s_R in (list_R _ s₁1 s₂1)
                       return
                         (@list_R A₁ A₂ A_R
                            match s₁1 return (list A₁) with
                            | nil => @nil A₁
                            | cons x _ => x
                            end
                            match s₂1 return (list A₂) with
                            | nil => @nil A₂
                            | cons x _ => x
                            end)
                     with
                     | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                     | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                     end)))) (fix_map_1 s'₁) (fix_map_2 s'₂) (map_R s'₁ s'₂ s'_R)
   end)
  ((fix pmap (s : list nat) :
      list
        (ordinal
           ((fix size (s0 : list A₁) : nat :=
               match s0 return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end)) :=
      match
        s
        return
          (list
             (ordinal
                ((fix size (s1 : list A₁) : nat :=
                    match s1 return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₁ return (list A₁) with
                   | nil => @nil A₁
                   | cons x _ => x
                   end)))
      with
      | nil =>
          @nil
            (ordinal
               ((fix size (s0 : list A₁) : nat :=
                   match s0 return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end))
      | cons x s' =>
          match
            match
              (fix eqn (m n : nat) {struct m} : bool :=
                 match m return bool with
                 | O => match n return bool with
                        | O => true
                        | S _ => false
                        end
                 | S m' => match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                 end)
                match
                  (fix size (s0 : list A₁) : nat :=
                     match s0 return nat with
                     | nil => O
                     | cons _ s'0 => S (size s'0)
                     end)
                    match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x0 _ => x0
                    end return nat
                with
                | O => S x
                | S l =>
                    (fix sub (n m : nat) {struct n} : nat :=
                       match n return nat with
                       | O => n
                       | S k => match m return nat with
                                | O => n
                                | S l0 => sub k l0
                                end
                       end) x l
                end O as Px
              return
                (forall
                   _ : @eq bool
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O) Px,
                 option
                   (ordinal
                      ((fix size (s0 : list A₁) : nat :=
                          match s0 return nat with
                          | nil => O
                          | cons _ s'0 => S (size s'0)
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x0 _ => x0
                         end)))
            with
            | true =>
                fun
                  Px : @eq bool
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₁) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O) true =>
                @Some
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x0 _ => x0
                        end))
                  (@Ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x0 _ => x0
                        end) x Px)
            | false =>
                fun
                  _ : @eq bool
                        ((fix eqn (m n : nat) {struct m} : bool :=
                            match m return bool with
                            | O => match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                            | S m' =>
                                match n return bool with
                                | O => false
                                | S n' => eqn m' n'
                                end
                            end)
                           match
                             (fix size (s0 : list A₁) : nat :=
                                match s0 return nat with
                                | nil => O
                                | cons _ s'0 => S (size s'0)
                                end)
                               match s₁ return (list A₁) with
                               | nil => @nil A₁
                               | cons x0 _ => x0
                               end return nat
                           with
                           | O => S x
                           | S l =>
                               (fix sub (n m : nat) {struct n} : nat :=
                                  match n return nat with
                                  | O => n
                                  | S k =>
                                      match m return nat with
                                      | O => n
                                      | S l0 => sub k l0
                                      end
                                  end) x l
                           end O) false =>
                @None
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x0 _ => x0
                        end))
            end
              (@Logic.eq_refl bool
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x0 _ => x0
                        end return nat
                    with
                    | O => S x
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x l
                    end O))
            return
              (list
                 (ordinal
                    ((fix size (s0 : list A₁) : nat :=
                        match s0 return nat with
                        | nil => O
                        | cons _ s'0 => S (size s'0)
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x0 _ => x0
                       end)))
          with
          | Some y =>
              @cons
                (ordinal
                   ((fix size (s0 : list A₁) : nat :=
                       match s0 return nat with
                       | nil => O
                       | cons _ s'0 => S (size s'0)
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x0 _ => x0
                      end)) y (pmap s')
          | None => pmap s'
          end
      end)
     ((fix iota (m n : nat) {struct n} : list nat :=
         match n return (list nat) with
         | O => @nil nat
         | S n' => @cons nat m (iota (S m) n')
         end) O
        ((fix size (s : list A₁) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₁ return (list A₁) with
                 | nil => @nil A₁
                 | cons x _ => x
                 end)))
  ((fix pmap (s : list nat) :
      list
        (ordinal
           ((fix size (s0 : list A₂) : nat :=
               match s0 return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end)) :=
      match
        s
        return
          (list
             (ordinal
                ((fix size (s1 : list A₂) : nat :=
                    match s1 return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₂ return (list A₂) with
                   | nil => @nil A₂
                   | cons x _ => x
                   end)))
      with
      | nil =>
          @nil
            (ordinal
               ((fix size (s0 : list A₂) : nat :=
                   match s0 return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end))
      | cons x s' =>
          match
            match
              (fix eqn (m n : nat) {struct m} : bool :=
                 match m return bool with
                 | O => match n return bool with
                        | O => true
                        | S _ => false
                        end
                 | S m' => match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                 end)
                match
                  (fix size (s0 : list A₂) : nat :=
                     match s0 return nat with
                     | nil => O
                     | cons _ s'0 => S (size s'0)
                     end)
                    match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x0 _ => x0
                    end return nat
                with
                | O => S x
                | S l =>
                    (fix sub (n m : nat) {struct n} : nat :=
                       match n return nat with
                       | O => n
                       | S k => match m return nat with
                                | O => n
                                | S l0 => sub k l0
                                end
                       end) x l
                end O as Px
              return
                (forall
                   _ : @eq bool
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O) Px,
                 option
                   (ordinal
                      ((fix size (s0 : list A₂) : nat :=
                          match s0 return nat with
                          | nil => O
                          | cons _ s'0 => S (size s'0)
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x0 _ => x0
                         end)))
            with
            | true =>
                fun
                  Px : @eq bool
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s0 : list A₂) : nat :=
                                 match s0 return nat with
                                 | nil => O
                                 | cons _ s'0 => S (size s'0)
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x0 _ => x0
                                end return nat
                            with
                            | O => S x
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x l
                            end O) true =>
                @Some
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x0 _ => x0
                        end))
                  (@Ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x0 _ => x0
                        end) x Px)
            | false =>
                fun
                  _ : @eq bool
                        ((fix eqn (m n : nat) {struct m} : bool :=
                            match m return bool with
                            | O => match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                            | S m' =>
                                match n return bool with
                                | O => false
                                | S n' => eqn m' n'
                                end
                            end)
                           match
                             (fix size (s0 : list A₂) : nat :=
                                match s0 return nat with
                                | nil => O
                                | cons _ s'0 => S (size s'0)
                                end)
                               match s₂ return (list A₂) with
                               | nil => @nil A₂
                               | cons x0 _ => x0
                               end return nat
                           with
                           | O => S x
                           | S l =>
                               (fix sub (n m : nat) {struct n} : nat :=
                                  match n return nat with
                                  | O => n
                                  | S k =>
                                      match m return nat with
                                      | O => n
                                      | S l0 => sub k l0
                                      end
                                  end) x l
                           end O) false =>
                @None
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x0 _ => x0
                        end))
            end
              (@Logic.eq_refl bool
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x0 _ => x0
                        end return nat
                    with
                    | O => S x
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x l
                    end O))
            return
              (list
                 (ordinal
                    ((fix size (s0 : list A₂) : nat :=
                        match s0 return nat with
                        | nil => O
                        | cons _ s'0 => S (size s'0)
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x0 _ => x0
                       end)))
          with
          | Some y =>
              @cons
                (ordinal
                   ((fix size (s0 : list A₂) : nat :=
                       match s0 return nat with
                       | nil => O
                       | cons _ s'0 => S (size s'0)
                       end)
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x0 _ => x0
                      end)) y (pmap s')
          | None => pmap s'
          end
      end)
     ((fix iota (m n : nat) {struct n} : list nat :=
         match n return (list nat) with
         | O => @nil nat
         | S n' => @cons nat m (iota (S m) n')
         end) O
        ((fix size (s : list A₂) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₂ return (list A₂) with
                 | nil => @nil A₂
                 | cons x _ => x
                 end)))
  ((let fix_pmap_1 :
      forall _ : list nat,
      list
        (ordinal
           ((fix size (s0 : list A₁) : nat :=
               match s0 return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end)) :=
      fix pmap (s : list nat) :
        list
          (ordinal
             ((fix size (s0 : list A₁) : nat :=
                 match s0 return nat with
                 | nil => O
                 | cons _ s' => S (size s')
                 end) match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x _ => x
                      end)) :=
        match
          s
          return
            (list
               (ordinal
                  ((fix size (s1 : list A₁) : nat :=
                      match s1 return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₁ return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end)))
        with
        | nil =>
            @nil
              (ordinal
                 ((fix size (s0 : list A₁) : nat :=
                     match s0 return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end))
        | cons x s' =>
            match
              match
                (fix eqn (m n : nat) {struct m} : bool :=
                   match m return bool with
                   | O => match n return bool with
                          | O => true
                          | S _ => false
                          end
                   | S m' => match n return bool with
                             | O => false
                             | S n' => eqn m' n'
                             end
                   end)
                  match
                    (fix size (s0 : list A₁) : nat :=
                       match s0 return nat with
                       | nil => O
                       | cons _ s'0 => S (size s'0)
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x0 _ => x0
                      end return nat
                  with
                  | O => S x
                  | S l =>
                      (fix sub (n m : nat) {struct n} : nat :=
                         match n return nat with
                         | O => n
                         | S k => match m return nat with
                                  | O => n
                                  | S l0 => sub k l0
                                  end
                         end) x l
                  end O as Px
                return
                  (forall
                     _ : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O) Px,
                   option
                     (ordinal
                        ((fix size (s0 : list A₁) : nat :=
                            match s0 return nat with
                            | nil => O
                            | cons _ s'0 => S (size s'0)
                            end)
                           match s₁ return (list A₁) with
                           | nil => @nil A₁
                           | cons x0 _ => x0
                           end)))
              with
              | true =>
                  fun
                    Px : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₁) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O) true =>
                  @Some
                    (ordinal
                       ((fix size (s0 : list A₁) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x0 _ => x0
                          end))
                    (@Ordinal
                       ((fix size (s0 : list A₁) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x0 _ => x0
                          end) x Px)
              | false =>
                  fun
                    _ : @eq bool
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s0 : list A₁) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x0 _ => x0
                                 end return nat
                             with
                             | O => S x
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x l
                             end O) false =>
                  @None
                    (ordinal
                       ((fix size (s0 : list A₁) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x0 _ => x0
                          end))
              end
                (@Logic.eq_refl bool
                   ((fix eqn (m n : nat) {struct m} : bool :=
                       match m return bool with
                       | O => match n return bool with
                              | O => true
                              | S _ => false
                              end
                       | S m' =>
                           match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                       end)
                      match
                        (fix size (s0 : list A₁) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₁ return (list A₁) with
                          | nil => @nil A₁
                          | cons x0 _ => x0
                          end return nat
                      with
                      | O => S x
                      | S l =>
                          (fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k =>
                                 match m return nat with
                                 | O => n
                                 | S l0 => sub k l0
                                 end
                             end) x l
                      end O))
              return
                (list
                   (ordinal
                      ((fix size (s0 : list A₁) : nat :=
                          match s0 return nat with
                          | nil => O
                          | cons _ s'0 => S (size s'0)
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x0 _ => x0
                         end)))
            with
            | Some y =>
                @cons
                  (ordinal
                     ((fix size (s0 : list A₁) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x0 _ => x0
                        end)) y (pmap s')
            | None => pmap s'
            end
        end in
    let fix_pmap_2 :
      forall _ : list nat,
      list
        (ordinal
           ((fix size (s0 : list A₂) : nat :=
               match s0 return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end)) :=
      fix pmap (s : list nat) :
        list
          (ordinal
             ((fix size (s0 : list A₂) : nat :=
                 match s0 return nat with
                 | nil => O
                 | cons _ s' => S (size s')
                 end) match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end)) :=
        match
          s
          return
            (list
               (ordinal
                  ((fix size (s1 : list A₂) : nat :=
                      match s1 return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end)
                     match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end)))
        with
        | nil =>
            @nil
              (ordinal
                 ((fix size (s0 : list A₂) : nat :=
                     match s0 return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end))
        | cons x s' =>
            match
              match
                (fix eqn (m n : nat) {struct m} : bool :=
                   match m return bool with
                   | O => match n return bool with
                          | O => true
                          | S _ => false
                          end
                   | S m' => match n return bool with
                             | O => false
                             | S n' => eqn m' n'
                             end
                   end)
                  match
                    (fix size (s0 : list A₂) : nat :=
                       match s0 return nat with
                       | nil => O
                       | cons _ s'0 => S (size s'0)
                       end)
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x0 _ => x0
                      end return nat
                  with
                  | O => S x
                  | S l =>
                      (fix sub (n m : nat) {struct n} : nat :=
                         match n return nat with
                         | O => n
                         | S k => match m return nat with
                                  | O => n
                                  | S l0 => sub k l0
                                  end
                         end) x l
                  end O as Px
                return
                  (forall
                     _ : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O) Px,
                   option
                     (ordinal
                        ((fix size (s0 : list A₂) : nat :=
                            match s0 return nat with
                            | nil => O
                            | cons _ s'0 => S (size s'0)
                            end)
                           match s₂ return (list A₂) with
                           | nil => @nil A₂
                           | cons x0 _ => x0
                           end)))
              with
              | true =>
                  fun
                    Px : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s0 : list A₂) : nat :=
                                   match s0 return nat with
                                   | nil => O
                                   | cons _ s'0 => S (size s'0)
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x0 _ => x0
                                  end return nat
                              with
                              | O => S x
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x l
                              end O) true =>
                  @Some
                    (ordinal
                       ((fix size (s0 : list A₂) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x0 _ => x0
                          end))
                    (@Ordinal
                       ((fix size (s0 : list A₂) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x0 _ => x0
                          end) x Px)
              | false =>
                  fun
                    _ : @eq bool
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s0 : list A₂) : nat :=
                                  match s0 return nat with
                                  | nil => O
                                  | cons _ s'0 => S (size s'0)
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x0 _ => x0
                                 end return nat
                             with
                             | O => S x
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x l
                             end O) false =>
                  @None
                    (ordinal
                       ((fix size (s0 : list A₂) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x0 _ => x0
                          end))
              end
                (@Logic.eq_refl bool
                   ((fix eqn (m n : nat) {struct m} : bool :=
                       match m return bool with
                       | O => match n return bool with
                              | O => true
                              | S _ => false
                              end
                       | S m' =>
                           match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                       end)
                      match
                        (fix size (s0 : list A₂) : nat :=
                           match s0 return nat with
                           | nil => O
                           | cons _ s'0 => S (size s'0)
                           end)
                          match s₂ return (list A₂) with
                          | nil => @nil A₂
                          | cons x0 _ => x0
                          end return nat
                      with
                      | O => S x
                      | S l =>
                          (fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k =>
                                 match m return nat with
                                 | O => n
                                 | S l0 => sub k l0
                                 end
                             end) x l
                      end O))
              return
                (list
                   (ordinal
                      ((fix size (s0 : list A₂) : nat :=
                          match s0 return nat with
                          | nil => O
                          | cons _ s'0 => S (size s'0)
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x0 _ => x0
                         end)))
            with
            | Some y =>
                @cons
                  (ordinal
                     ((fix size (s0 : list A₂) : nat :=
                         match s0 return nat with
                         | nil => O
                         | cons _ s'0 => S (size s'0)
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x0 _ => x0
                        end)) y (pmap s')
            | None => pmap s'
            end
        end in
    fix pmap_R (s₁0 s₂0 : list nat) (s_R0 : @list_R nat nat nat_R s₁0 s₂0) {struct s_R0} :
      @list_R
        (ordinal
           ((fix size (s : list A₁) : nat :=
               match s return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end))
        (ordinal
           ((fix size (s : list A₂) : nat :=
               match s return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end))
        (@ordinal_R
           ((fix size (s : list A₁) : nat :=
               match s return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end)
           ((fix size (s : list A₂) : nat :=
               match s return nat with
               | nil => O
               | cons _ s' => S (size s')
               end) match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end)
           ((let fix_size_1 : forall _ : list A₁, nat :=
               fix size (s : list A₁) : nat :=
                 match s return nat with
                 | nil => O
                 | cons _ s' => S (size s')
                 end in
             let fix_size_2 : forall _ : list A₂, nat :=
               fix size (s : list A₂) : nat :=
                 match s return nat with
                 | nil => O
                 | cons _ s' => S (size s')
                 end in
             fix
             size_R (s₁1 : list A₁) (s₂1 : list A₂) (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1)
                    {struct s_R1} : nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
               match
                 s_R1 in (list_R _ s₁2 s₂2)
                 return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
               with
               | @list_R_nil_R _ _ _ => nat_R_O_R
               | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁ s'₂ s'_R =>
                   @nat_R_S_R (fix_size_1 s'₁) (fix_size_2 s'₂) (size_R s'₁ s'₂ s'_R)
               end) match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
              match
                s_R in (list_R _ s₁1 s₂1)
                return
                  (@list_R A₁ A₂ A_R
                     match s₁1 return (list A₁) with
                     | nil => @nil A₁
                     | cons x _ => x
                     end
                     match s₂1 return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end)
              with
              | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
              | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ _ => x_R
              end)) (fix_pmap_1 s₁0) (fix_pmap_2 s₂0) :=
      match
        s_R0 in (list_R _ s₁1 s₂1)
        return
          (@list_R
             (ordinal
                ((fix size (s : list A₁) : nat :=
                    match s return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₁ return (list A₁) with
                   | nil => @nil A₁
                   | cons x _ => x
                   end))
             (ordinal
                ((fix size (s : list A₂) : nat :=
                    match s return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₂ return (list A₂) with
                   | nil => @nil A₂
                   | cons x _ => x
                   end))
             (@ordinal_R
                ((fix size (s : list A₁) : nat :=
                    match s return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₁ return (list A₁) with
                   | nil => @nil A₁
                   | cons x _ => x
                   end)
                ((fix size (s : list A₂) : nat :=
                    match s return nat with
                    | nil => O
                    | cons _ s' => S (size s')
                    end)
                   match s₂ return (list A₂) with
                   | nil => @nil A₂
                   | cons x _ => x
                   end)
                ((let fix_size_1 : forall _ : list A₁, nat :=
                    fix size (s : list A₁) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end in
                  let fix_size_2 : forall _ : list A₂, nat :=
                    fix size (s : list A₂) : nat :=
                      match s return nat with
                      | nil => O
                      | cons _ s' => S (size s')
                      end in
                  fix
                  size_R (s₁2 : list A₁) (s₂2 : list A₂) (s_R2 : @list_R A₁ A₂ A_R s₁2 s₂2)
                         {struct s_R2} : nat_R (fix_size_1 s₁2) (fix_size_2 s₂2) :=
                    match
                      s_R2 in (list_R _ s₁3 s₂3)
                      return (nat_R (fix_size_1 s₁3) (fix_size_2 s₂3))
                    with
                    | @list_R_nil_R _ _ _ => nat_R_O_R
                    | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁ s'₂ s'_R =>
                        @nat_R_S_R (fix_size_1 s'₁) (fix_size_2 s'₂) (size_R s'₁ s'₂ s'_R)
                    end)
                   match s₁ return (list A₁) with
                   | nil => @nil A₁
                   | cons x _ => x
                   end match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end
                   match
                     s_R in (list_R _ s₁2 s₂2)
                     return
                       (@list_R A₁ A₂ A_R
                          match s₁2 return (list A₁) with
                          | nil => @nil A₁
                          | cons x _ => x
                          end
                          match s₂2 return (list A₂) with
                          | nil => @nil A₂
                          | cons x _ => x
                          end)
                   with
                   | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                   | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ _ => x_R
                   end)) (fix_pmap_1 s₁1) (fix_pmap_2 s₂1))
      with
      | @list_R_nil_R _ _ _ =>
          @list_R_nil_R
            (ordinal
               ((fix size (s : list A₁) : nat :=
                   match s return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end))
            (ordinal
               ((fix size (s : list A₂) : nat :=
                   match s return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end))
            (@ordinal_R
               ((fix size (s : list A₁) : nat :=
                   match s return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)
               ((fix size (s : list A₂) : nat :=
                   match s return nat with
                   | nil => O
                   | cons _ s' => S (size s')
                   end) match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)
               ((let fix_size_1 : forall _ : list A₁, nat :=
                   fix size (s : list A₁) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end in
                 let fix_size_2 : forall _ : list A₂, nat :=
                   fix size (s : list A₂) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end in
                 fix
                 size_R (s₁1 : list A₁) (s₂1 : list A₂) (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1)
                        {struct s_R1} : nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                   match
                     s_R1 in (list_R _ s₁2 s₂2)
                     return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                   with
                   | @list_R_nil_R _ _ _ => nat_R_O_R
                   | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁ s'₂ s'_R =>
                       @nat_R_S_R (fix_size_1 s'₁) (fix_size_2 s'₂) (size_R s'₁ s'₂ s'_R)
                   end) match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                  match s₂ return (list A₂) with
                  | nil => @nil A₂
                  | cons x _ => x
                  end
                  match
                    s_R in (list_R _ s₁1 s₂1)
                    return
                      (@list_R A₁ A₂ A_R
                         match s₁1 return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end
                         match s₂1 return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end)
                  with
                  | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                  | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ _ => x_R
                  end))
      | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
          match
            match
              (let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                 fix eqn (m n : nat) {struct m} : bool :=
                   match m return bool with
                   | O => match n return bool with
                          | O => true
                          | S _ => false
                          end
                   | S m' => match n return bool with
                             | O => false
                             | S n' => eqn m' n'
                             end
                   end in
               let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                 fix eqn (m n : nat) {struct m} : bool :=
                   match m return bool with
                   | O => match n return bool with
                          | O => true
                          | S _ => false
                          end
                   | S m' => match n return bool with
                             | O => false
                             | S n' => eqn m' n'
                             end
                   end in
               fix
               eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat) 
                     (n_R : nat_R n₁ n₂) {struct m_R} :
                 bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                 match
                   m_R in (nat_R m₁0 m₂0)
                   return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                 with
                 | nat_R_O_R =>
                     match
                       n_R in (nat_R n₁0 n₂0)
                       return
                         (bool_R match n₁0 return bool with
                                 | O => true
                                 | S _ => false
                                 end
                            match n₂0 return bool with
                            | O => true
                            | S _ => false
                            end)
                     with
                     | nat_R_O_R => bool_R_true_R
                     | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                     end
                 | @nat_R_S_R m'₁ m'₂ m'_R =>
                     match
                       n_R in (nat_R n₁0 n₂0)
                       return
                         (bool_R
                            match n₁0 return bool with
                            | O => false
                            | S n' => fix_eqn_1 m'₁ n'
                            end
                            match n₂0 return bool with
                            | O => false
                            | S n' => fix_eqn_2 m'₂ n'
                            end)
                     with
                     | nat_R_O_R => bool_R_false_R
                     | @nat_R_S_R n'₁ n'₂ n'_R => eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                     end
                 end)
                match
                  (fix size (s : list A₁) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end return nat
                with
                | O => S x₁
                | S l =>
                    (fix sub (n m : nat) {struct n} : nat :=
                       match n return nat with
                       | O => n
                       | S k => match m return nat with
                                | O => n
                                | S l0 => sub k l0
                                end
                       end) x₁ l
                end
                match
                  (fix size (s : list A₂) : nat :=
                     match s return nat with
                     | nil => O
                     | cons _ s' => S (size s')
                     end)
                    match s₂ return (list A₂) with
                    | nil => @nil A₂
                    | cons x _ => x
                    end return nat
                with
                | O => S x₂
                | S l =>
                    (fix sub (n m : nat) {struct n} : nat :=
                       match n return nat with
                       | O => n
                       | S k => match m return nat with
                                | O => n
                                | S l0 => sub k l0
                                end
                       end) x₂ l
                end
                match
                  (let fix_size_1 : forall _ : list A₁, nat :=
                     fix size (s : list A₁) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end in
                   let fix_size_2 : forall _ : list A₂, nat :=
                     fix size (s : list A₂) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end in
                   fix
                   size_R (s₁1 : list A₁) (s₂1 : list A₂)
                          (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                     nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                     match
                       s_R1 in (list_R _ s₁2 s₂2)
                       return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                     with
                     | @list_R_nil_R _ _ _ => nat_R_O_R
                     | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                         @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                           (size_R s'₁0 s'₂0 s'_R0)
                     end)
                    match s₁ return (list A₁) with
                    | nil => @nil A₁
                    | cons x _ => x
                    end match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                    match
                      s_R in (list_R _ s₁1 s₂1)
                      return
                        (@list_R A₁ A₂ A_R
                           match s₁1 return (list A₁) with
                           | nil => @nil A₁
                           | cons x _ => x
                           end
                           match s₂1 return (list A₂) with
                           | nil => @nil A₂
                           | cons x _ => x
                           end)
                    with
                    | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                    | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                    end in (nat_R m₁ m₂)
                  return
                    (nat_R
                       match m₁ return nat with
                       | O => S x₁
                       | S l =>
                           (fix sub (n m : nat) {struct n} : nat :=
                              match n return nat with
                              | O => n
                              | S k =>
                                  match m return nat with
                                  | O => n
                                  | S l0 => sub k l0
                                  end
                              end) x₁ l
                       end
                       match m₂ return nat with
                       | O => S x₂
                       | S l =>
                           (fix sub (n m : nat) {struct n} : nat :=
                              match n return nat with
                              | O => n
                              | S k =>
                                  match m return nat with
                                  | O => n
                                  | S l0 => sub k l0
                                  end
                              end) x₂ l
                       end)
                with
                | nat_R_O_R => @nat_R_S_R x₁ x₂ x_R
                | @nat_R_S_R l₁ l₂ l_R =>
                    (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                       fix sub (n m : nat) {struct n} : nat :=
                         match n return nat with
                         | O => n
                         | S k => match m return nat with
                                  | O => n
                                  | S l => sub k l
                                  end
                         end in
                     let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                       fix sub (n m : nat) {struct n} : nat :=
                         match n return nat with
                         | O => n
                         | S k => match m return nat with
                                  | O => n
                                  | S l => sub k l
                                  end
                         end in
                     fix
                     sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (m₁ m₂ : nat)
                           (m_R : nat_R m₁ m₂) {struct n_R} :
                       nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                       let gen_path :
                         let
                           fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k => match m return nat with
                                      | O => n
                                      | S l => sub k l
                                      end
                             end in
                         forall n m : nat,
                         @eq nat
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l => sub k l
                                    end
                           end (sub n m) :=
                         let
                           fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k => match m return nat with
                                      | O => n
                                      | S l => sub k l
                                      end
                             end in
                         fun n m : nat =>
                         match
                           n as n0
                           return
                             (@eq nat
                                match n0 return nat with
                                | O => n0
                                | S k =>
                                    match m return nat with
                                    | O => n0
                                    | S l => sub k l
                                    end
                                end (sub n0 m))
                         with
                         | O => @Logic.eq_refl nat (sub O m)
                         | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                         end in
                       @eq_rect nat
                         match n₁ return nat with
                         | O => n₁
                         | S k =>
                             match m₁ return nat with
                             | O => n₁
                             | S l => fix_sub_1 k l
                             end
                         end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                         (@eq_rect nat
                            match n₂ return nat with
                            | O => n₂
                            | S k =>
                                match m₂ return nat with
                                | O => n₂
                                | S l => fix_sub_2 k l
                                end
                            end
                            (fun x : nat =>
                             nat_R
                               match n₁ return nat with
                               | O => n₁
                               | S k =>
                                   match m₁ return nat with
                                   | O => n₁
                                   | S l => fix_sub_1 k l
                                   end
                               end x)
                            match
                              n_R in (nat_R n₁0 n₂0)
                              return
                                (nat_R
                                   match n₁0 return nat with
                                   | O => n₁
                                   | S k =>
                                       match m₁ return nat with
                                       | O => n₁
                                       | S l => fix_sub_1 k l
                                       end
                                   end
                                   match n₂0 return nat with
                                   | O => n₂
                                   | S k =>
                                       match m₂ return nat with
                                       | O => n₂
                                       | S l => fix_sub_2 k l
                                       end
                                   end)
                            with
                            | nat_R_O_R => n_R
                            | @nat_R_S_R k₁ k₂ k_R =>
                                match
                                  m_R in (nat_R m₁0 m₂0)
                                  return
                                    (nat_R
                                       match m₁0 return nat with
                                       | O => n₁
                                       | S l => fix_sub_1 k₁ l
                                       end
                                       match m₂0 return nat with
                                       | O => n₂
                                       | S l => fix_sub_2 k₂ l
                                       end)
                                with
                                | nat_R_O_R => n_R
                                | @nat_R_S_R l₁0 l₂0 l_R0 => sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                end
                            end (fix_sub_2 n₂ m₂) (gen_path n₂ m₂)) 
                         (fix_sub_1 n₁ m₁) (gen_path n₁ m₁)) x₁ x₂ x_R l₁ l₂ l_R
                end O O nat_R_O_R as Px_R in (bool_R Px₁ Px₂)
              return
                (forall
                   (H : @eq bool
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₁
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₁ l
                             end O) Px₁)
                   (H0 : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₂
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₂ l
                              end O) Px₂)
                   (_ : @eq_R bool bool bool_R
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₁
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₁ l
                             end O)
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₂
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₂ l
                             end O)
                          ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                              fix eqn (m n : nat) {struct m} : bool :=
                                match m return bool with
                                | O =>
                                    match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                                | S m' =>
                                    match n return bool with
                                    | O => false
                                    | S n' => eqn m' n'
                                    end
                                end in
                            let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                              fix eqn (m n : nat) {struct m} : bool :=
                                match m return bool with
                                | O =>
                                    match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                                | S m' =>
                                    match n return bool with
                                    | O => false
                                    | S n' => eqn m' n'
                                    end
                                end in
                            fix
                            eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                  (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                              bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                              match
                                m_R in (nat_R m₁0 m₂0)
                                return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                              with
                              | nat_R_O_R =>
                                  match
                                    n_R in (nat_R n₁0 n₂0)
                                    return
                                      (bool_R
                                         match n₁0 return bool with
                                         | O => true
                                         | S _ => false
                                         end
                                         match n₂0 return bool with
                                         | O => true
                                         | S _ => false
                                         end)
                                  with
                                  | nat_R_O_R => bool_R_true_R
                                  | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                  end
                              | @nat_R_S_R m'₁ m'₂ m'_R =>
                                  match
                                    n_R in (nat_R n₁0 n₂0)
                                    return
                                      (bool_R
                                         match n₁0 return bool with
                                         | O => false
                                         | S n' => fix_eqn_1 m'₁ n'
                                         end
                                         match n₂0 return bool with
                                         | O => false
                                         | S n' => fix_eqn_2 m'₂ n'
                                         end)
                                  with
                                  | nat_R_O_R => bool_R_false_R
                                  | @nat_R_S_R n'₁ n'₂ n'_R =>
                                      eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                  end
                              end)
                             match
                               (fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₁
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₁ l
                             end
                             match
                               (fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₂
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₂ l
                             end
                             match
                               (let fix_size_1 : forall _ : list A₁, nat :=
                                  fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end in
                                let fix_size_2 : forall _ : list A₂, nat :=
                                  fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end in
                                fix
                                size_R (s₁1 : list A₁) (s₂1 : list A₂)
                                       (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                                  nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                                  match
                                    s_R1 in (list_R _ s₁2 s₂2)
                                    return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                                  with
                                  | @list_R_nil_R _ _ _ => nat_R_O_R
                                  | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                      @nat_R_S_R (fix_size_1 s'₁0) 
                                        (fix_size_2 s'₂0) (size_R s'₁0 s'₂0 s'_R0)
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end
                                 match
                                   s_R in (list_R _ s₁1 s₂1)
                                   return
                                     (@list_R A₁ A₂ A_R
                                        match s₁1 return (list A₁) with
                                        | nil => @nil A₁
                                        | cons x _ => x
                                        end
                                        match s₂1 return (list A₂) with
                                        | nil => @nil A₂
                                        | cons x _ => x
                                        end)
                                 with
                                 | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                 | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                                 end in (nat_R m₁ m₂)
                               return
                                 (nat_R
                                    match m₁ return nat with
                                    | O => S x₁
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₁ l
                                    end
                                    match m₂ return nat with
                                    | O => S x₂
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₂ l
                                    end)
                             with
                             | nat_R_O_R => @nat_R_S_R x₁ x₂ x_R
                             | @nat_R_S_R l₁ l₂ l_R =>
                                 (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                                    fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l => sub k l
                                          end
                                      end in
                                  let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                                    fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l => sub k l
                                          end
                                      end in
                                  fix
                                  sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                                        (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                                    nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                    let gen_path :
                                      let
                                        fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l => sub k l
                                              end
                                          end in
                                      forall n m : nat,
                                      @eq nat
                                        match n return nat with
                                        | O => n
                                        | S k =>
                                            match m return nat with
                                            | O => n
                                            | S l => sub k l
                                            end
                                        end (sub n m) :=
                                      let
                                        fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l => sub k l
                                              end
                                          end in
                                      fun n m : nat =>
                                      match
                                        n as n0
                                        return
                                          (@eq nat
                                             match n0 return nat with
                                             | O => n0
                                             | S k =>
                                                 match m return nat with
                                                 | O => n0
                                                 | S l => sub k l
                                                 end
                                             end (sub n0 m))
                                      with
                                      | O => @Logic.eq_refl nat (sub O m)
                                      | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                      end in
                                    @eq_rect nat
                                      match n₁ return nat with
                                      | O => n₁
                                      | S k =>
                                          match m₁ return nat with
                                          | O => n₁
                                          | S l => fix_sub_1 k l
                                          end
                                      end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                      (@eq_rect nat
                                         match n₂ return nat with
                                         | O => n₂
                                         | S k =>
                                             match m₂ return nat with
                                             | O => n₂
                                             | S l => fix_sub_2 k l
                                             end
                                         end
                                         (fun x : nat =>
                                          nat_R
                                            match n₁ return nat with
                                            | O => n₁
                                            | S k =>
                                                match m₁ return nat with
                                                | O => n₁
                                                | S l => fix_sub_1 k l
                                                end
                                            end x)
                                         match
                                           n_R in (nat_R n₁0 n₂0)
                                           return
                                             (nat_R
                                                match n₁0 return nat with
                                                | O => n₁
                                                | S k =>
                                                    match m₁ return nat with
                                                    | O => n₁
                                                    | S l => fix_sub_1 k l
                                                    end
                                                end
                                                match n₂0 return nat with
                                                | O => n₂
                                                | S k =>
                                                    match m₂ return nat with
                                                    | O => n₂
                                                    | S l => fix_sub_2 k l
                                                    end
                                                end)
                                         with
                                         | nat_R_O_R => n_R
                                         | @nat_R_S_R k₁ k₂ k_R =>
                                             match
                                               m_R in (nat_R m₁0 m₂0)
                                               return
                                                 (nat_R
                                                    match m₁0 return nat with
                                                    | O => n₁
                                                    | S l => fix_sub_1 k₁ l
                                                    end
                                                    match m₂0 return nat with
                                                    | O => n₂
                                                    | S l => fix_sub_2 k₂ l
                                                    end)
                                             with
                                             | nat_R_O_R => n_R
                                             | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                 sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                             end
                                         end (fix_sub_2 n₂ m₂) 
                                         (gen_path n₂ m₂)) (fix_sub_1 n₁ m₁)
                                      (gen_path n₁ m₁)) x₁ x₂ x_R l₁ l₂ l_R
                             end O O nat_R_O_R) Px₁ Px₂ Px_R H H0),
                 @option_R
                   (ordinal
                      ((fix size (s : list A₁) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end))
                   (ordinal
                      ((fix size (s : list A₂) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end))
                   (@ordinal_R
                      ((fix size (s : list A₁) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end)
                      ((fix size (s : list A₂) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end)
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end)
                      ((let fix_size_1 : forall _ : list A₁, nat :=
                          fix size (s : list A₁) : nat :=
                            match s return nat with
                            | nil => O
                            | cons _ s' => S (size s')
                            end in
                        let fix_size_2 : forall _ : list A₂, nat :=
                          fix size (s : list A₂) : nat :=
                            match s return nat with
                            | nil => O
                            | cons _ s' => S (size s')
                            end in
                        fix
                        size_R (s₁1 : list A₁) (s₂1 : list A₂)
                               (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                          nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                          match
                            s_R1 in (list_R _ s₁2 s₂2)
                            return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                          with
                          | @list_R_nil_R _ _ _ => nat_R_O_R
                          | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                              @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                                (size_R s'₁0 s'₂0 s'_R0)
                          end)
                         match s₁ return (list A₁) with
                         | nil => @nil A₁
                         | cons x _ => x
                         end
                         match s₂ return (list A₂) with
                         | nil => @nil A₂
                         | cons x _ => x
                         end
                         match
                           s_R in (list_R _ s₁1 s₂1)
                           return
                             (@list_R A₁ A₂ A_R
                                match s₁1 return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end
                                match s₂1 return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end)
                         with
                         | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                         | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                         end))
                   (match
                      Px₁ as Px
                      return
                        (forall
                           _ : @eq bool
                                 ((fix eqn (m n : nat) {struct m} : bool :=
                                     match m return bool with
                                     | O =>
                                         match n return bool with
                                         | O => true
                                         | S _ => false
                                         end
                                     | S m' =>
                                         match n return bool with
                                         | O => false
                                         | S n' => eqn m' n'
                                         end
                                     end)
                                    match
                                      (fix size (s : list A₁) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₁ return (list A₁) with
                                        | nil => @nil A₁
                                        | cons x _ => x
                                        end return nat
                                    with
                                    | O => S x₁
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₁ l
                                    end O) Px,
                         option
                           (ordinal
                              ((fix size (s : list A₁) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₁ return (list A₁) with
                                 | nil => @nil A₁
                                 | cons x _ => x
                                 end)))
                    with
                    | true =>
                        fun
                          Px : @eq bool
                                 ((fix eqn (m n : nat) {struct m} : bool :=
                                     match m return bool with
                                     | O =>
                                         match n return bool with
                                         | O => true
                                         | S _ => false
                                         end
                                     | S m' =>
                                         match n return bool with
                                         | O => false
                                         | S n' => eqn m' n'
                                         end
                                     end)
                                    match
                                      (fix size (s : list A₁) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₁ return (list A₁) with
                                        | nil => @nil A₁
                                        | cons x _ => x
                                        end return nat
                                    with
                                    | O => S x₁
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₁ l
                                    end O) true =>
                        @Some
                          (ordinal
                             ((fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end))
                          (@Ordinal
                             ((fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end) x₁ Px)
                    | false =>
                        fun
                          _ : @eq bool
                                ((fix eqn (m n : nat) {struct m} : bool :=
                                    match m return bool with
                                    | O =>
                                        match n return bool with
                                        | O => true
                                        | S _ => false
                                        end
                                    | S m' =>
                                        match n return bool with
                                        | O => false
                                        | S n' => eqn m' n'
                                        end
                                    end)
                                   match
                                     (fix size (s : list A₁) : nat :=
                                        match s return nat with
                                        | nil => O
                                        | cons _ s' => S (size s')
                                        end)
                                       match s₁ return (list A₁) with
                                       | nil => @nil A₁
                                       | cons x _ => x
                                       end return nat
                                   with
                                   | O => S x₁
                                   | S l =>
                                       (fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l0 => sub k l0
                                              end
                                          end) x₁ l
                                   end O) false =>
                        @None
                          (ordinal
                             ((fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end))
                    end H)
                   (match
                      Px₂ as Px
                      return
                        (forall
                           _ : @eq bool
                                 ((fix eqn (m n : nat) {struct m} : bool :=
                                     match m return bool with
                                     | O =>
                                         match n return bool with
                                         | O => true
                                         | S _ => false
                                         end
                                     | S m' =>
                                         match n return bool with
                                         | O => false
                                         | S n' => eqn m' n'
                                         end
                                     end)
                                    match
                                      (fix size (s : list A₂) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₂ return (list A₂) with
                                        | nil => @nil A₂
                                        | cons x _ => x
                                        end return nat
                                    with
                                    | O => S x₂
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₂ l
                                    end O) Px,
                         option
                           (ordinal
                              ((fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end)))
                    with
                    | true =>
                        fun
                          Px : @eq bool
                                 ((fix eqn (m n : nat) {struct m} : bool :=
                                     match m return bool with
                                     | O =>
                                         match n return bool with
                                         | O => true
                                         | S _ => false
                                         end
                                     | S m' =>
                                         match n return bool with
                                         | O => false
                                         | S n' => eqn m' n'
                                         end
                                     end)
                                    match
                                      (fix size (s : list A₂) : nat :=
                                         match s return nat with
                                         | nil => O
                                         | cons _ s' => S (size s')
                                         end)
                                        match s₂ return (list A₂) with
                                        | nil => @nil A₂
                                        | cons x _ => x
                                        end return nat
                                    with
                                    | O => S x₂
                                    | S l =>
                                        (fix sub (n m : nat) {struct n} : nat :=
                                           match n return nat with
                                           | O => n
                                           | S k =>
                                               match m return nat with
                                               | O => n
                                               | S l0 => sub k l0
                                               end
                                           end) x₂ l
                                    end O) true =>
                        @Some
                          (ordinal
                             ((fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end))
                          (@Ordinal
                             ((fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end) x₂ Px)
                    | false =>
                        fun
                          _ : @eq bool
                                ((fix eqn (m n : nat) {struct m} : bool :=
                                    match m return bool with
                                    | O =>
                                        match n return bool with
                                        | O => true
                                        | S _ => false
                                        end
                                    | S m' =>
                                        match n return bool with
                                        | O => false
                                        | S n' => eqn m' n'
                                        end
                                    end)
                                   match
                                     (fix size (s : list A₂) : nat :=
                                        match s return nat with
                                        | nil => O
                                        | cons _ s' => S (size s')
                                        end)
                                       match s₂ return (list A₂) with
                                       | nil => @nil A₂
                                       | cons x _ => x
                                       end return nat
                                   with
                                   | O => S x₂
                                   | S l =>
                                       (fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l0 => sub k l0
                                              end
                                          end) x₂ l
                                   end O) false =>
                        @None
                          (ordinal
                             ((fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end))
                    end H0))
            with
            | bool_R_true_R =>
                fun
                  (Px₁ : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₁ return (list A₁) with
                                  | nil => @nil A₁
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₁
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₁ l
                              end O) true)
                  (Px₂ : @eq bool
                           ((fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end)
                              match
                                (fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end)
                                  match s₂ return (list A₂) with
                                  | nil => @nil A₂
                                  | cons x _ => x
                                  end return nat
                              with
                              | O => S x₂
                              | S l =>
                                  (fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l0 => sub k l0
                                         end
                                     end) x₂ l
                              end O) true)
                  (Px_R : @eq_R bool bool bool_R
                            ((fix eqn (m n : nat) {struct m} : bool :=
                                match m return bool with
                                | O =>
                                    match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                                | S m' =>
                                    match n return bool with
                                    | O => false
                                    | S n' => eqn m' n'
                                    end
                                end)
                               match
                                 (fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end return nat
                               with
                               | O => S x₁
                               | S l =>
                                   (fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l0 => sub k l0
                                          end
                                      end) x₁ l
                               end O)
                            ((fix eqn (m n : nat) {struct m} : bool :=
                                match m return bool with
                                | O =>
                                    match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                                | S m' =>
                                    match n return bool with
                                    | O => false
                                    | S n' => eqn m' n'
                                    end
                                end)
                               match
                                 (fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end return nat
                               with
                               | O => S x₂
                               | S l =>
                                   (fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l0 => sub k l0
                                          end
                                      end) x₂ l
                               end O)
                            ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                                fix eqn (m n : nat) {struct m} : bool :=
                                  match m return bool with
                                  | O =>
                                      match n return bool with
                                      | O => true
                                      | S _ => false
                                      end
                                  | S m' =>
                                      match n return bool with
                                      | O => false
                                      | S n' => eqn m' n'
                                      end
                                  end in
                              let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                                fix eqn (m n : nat) {struct m} : bool :=
                                  match m return bool with
                                  | O =>
                                      match n return bool with
                                      | O => true
                                      | S _ => false
                                      end
                                  | S m' =>
                                      match n return bool with
                                      | O => false
                                      | S n' => eqn m' n'
                                      end
                                  end in
                              fix
                              eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                    (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                                bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                                match
                                  m_R in (nat_R m₁0 m₂0)
                                  return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                                with
                                | nat_R_O_R =>
                                    match
                                      n_R in (nat_R n₁0 n₂0)
                                      return
                                        (bool_R
                                           match n₁0 return bool with
                                           | O => true
                                           | S _ => false
                                           end
                                           match n₂0 return bool with
                                           | O => true
                                           | S _ => false
                                           end)
                                    with
                                    | nat_R_O_R => bool_R_true_R
                                    | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                    end
                                | @nat_R_S_R m'₁ m'₂ m'_R =>
                                    match
                                      n_R in (nat_R n₁0 n₂0)
                                      return
                                        (bool_R
                                           match n₁0 return bool with
                                           | O => false
                                           | S n' => fix_eqn_1 m'₁ n'
                                           end
                                           match n₂0 return bool with
                                           | O => false
                                           | S n' => fix_eqn_2 m'₂ n'
                                           end)
                                    with
                                    | nat_R_O_R => bool_R_false_R
                                    | @nat_R_S_R n'₁ n'₂ n'_R =>
                                        eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                    end
                                end)
                               match
                                 (fix size (s : list A₁) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end return nat
                               with
                               | O => S x₁
                               | S l =>
                                   (fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l0 => sub k l0
                                          end
                                      end) x₁ l
                               end
                               match
                                 (fix size (s : list A₂) : nat :=
                                    match s return nat with
                                    | nil => O
                                    | cons _ s' => S (size s')
                                    end)
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end return nat
                               with
                               | O => S x₂
                               | S l =>
                                   (fix sub (n m : nat) {struct n} : nat :=
                                      match n return nat with
                                      | O => n
                                      | S k =>
                                          match m return nat with
                                          | O => n
                                          | S l0 => sub k l0
                                          end
                                      end) x₂ l
                               end
                               match
                                 (let fix_size_1 : forall _ : list A₁, nat :=
                                    fix size (s : list A₁) : nat :=
                                      match s return nat with
                                      | nil => O
                                      | cons _ s' => S (size s')
                                      end in
                                  let fix_size_2 : forall _ : list A₂, nat :=
                                    fix size (s : list A₂) : nat :=
                                      match s return nat with
                                      | nil => O
                                      | cons _ s' => S (size s')
                                      end in
                                  fix
                                  size_R (s₁1 : list A₁) (s₂1 : list A₂)
                                         (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                                    nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                                    match
                                      s_R1 in (list_R _ s₁2 s₂2)
                                      return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                                    with
                                    | @list_R_nil_R _ _ _ => nat_R_O_R
                                    | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                        @nat_R_S_R (fix_size_1 s'₁0) 
                                          (fix_size_2 s'₂0) (size_R s'₁0 s'₂0 s'_R0)
                                    end)
                                   match s₁ return (list A₁) with
                                   | nil => @nil A₁
                                   | cons x _ => x
                                   end
                                   match s₂ return (list A₂) with
                                   | nil => @nil A₂
                                   | cons x _ => x
                                   end
                                   match
                                     s_R in (list_R _ s₁1 s₂1)
                                     return
                                       (@list_R A₁ A₂ A_R
                                          match s₁1 return (list A₁) with
                                          | nil => @nil A₁
                                          | cons x _ => x
                                          end
                                          match s₂1 return (list A₂) with
                                          | nil => @nil A₂
                                          | cons x _ => x
                                          end)
                                   with
                                   | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                   | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                                   end in (nat_R m₁ m₂)
                                 return
                                   (nat_R
                                      match m₁ return nat with
                                      | O => S x₁
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₁ l
                                      end
                                      match m₂ return nat with
                                      | O => S x₂
                                      | S l =>
                                          (fix sub (n m : nat) {struct n} : nat :=
                                             match n return nat with
                                             | O => n
                                             | S k =>
                                                 match m return nat with
                                                 | O => n
                                                 | S l0 => sub k l0
                                                 end
                                             end) x₂ l
                                      end)
                               with
                               | nat_R_O_R => @nat_R_S_R x₁ x₂ x_R
                               | @nat_R_S_R l₁ l₂ l_R =>
                                   (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                                      fix sub (n m : nat) {struct n} : nat :=
                                        match n return nat with
                                        | O => n
                                        | S k =>
                                            match m return nat with
                                            | O => n
                                            | S l => sub k l
                                            end
                                        end in
                                    let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                                      fix sub (n m : nat) {struct n} : nat :=
                                        match n return nat with
                                        | O => n
                                        | S k =>
                                            match m return nat with
                                            | O => n
                                            | S l => sub k l
                                            end
                                        end in
                                    fix
                                    sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                                          (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                                      nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                      let gen_path :
                                        let
                                          fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l => sub k l
                                                end
                                            end in
                                        forall n m : nat,
                                        @eq nat
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l => sub k l
                                              end
                                          end (sub n m) :=
                                        let
                                          fix sub (n m : nat) {struct n} : nat :=
                                            match n return nat with
                                            | O => n
                                            | S k =>
                                                match m return nat with
                                                | O => n
                                                | S l => sub k l
                                                end
                                            end in
                                        fun n m : nat =>
                                        match
                                          n as n0
                                          return
                                            (@eq nat
                                               match n0 return nat with
                                               | O => n0
                                               | S k =>
                                                   match m return nat with
                                                   | O => n0
                                                   | S l => sub k l
                                                   end
                                               end (sub n0 m))
                                        with
                                        | O => @Logic.eq_refl nat (sub O m)
                                        | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                        end in
                                      @eq_rect nat
                                        match n₁ return nat with
                                        | O => n₁
                                        | S k =>
                                            match m₁ return nat with
                                            | O => n₁
                                            | S l => fix_sub_1 k l
                                            end
                                        end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                        (@eq_rect nat
                                           match n₂ return nat with
                                           | O => n₂
                                           | S k =>
                                               match m₂ return nat with
                                               | O => n₂
                                               | S l => fix_sub_2 k l
                                               end
                                           end
                                           (fun x : nat =>
                                            nat_R
                                              match n₁ return nat with
                                              | O => n₁
                                              | S k =>
                                                  match m₁ return nat with
                                                  | O => n₁
                                                  | S l => fix_sub_1 k l
                                                  end
                                              end x)
                                           match
                                             n_R in (nat_R n₁0 n₂0)
                                             return
                                               (nat_R
                                                  match n₁0 return nat with
                                                  | O => n₁
                                                  | S k =>
                                                      match m₁ return nat with
                                                      | O => n₁
                                                      | S l => fix_sub_1 k l
                                                      end
                                                  end
                                                  match n₂0 return nat with
                                                  | O => n₂
                                                  | S k =>
                                                      match m₂ return nat with
                                                      | O => n₂
                                                      | S l => fix_sub_2 k l
                                                      end
                                                  end)
                                           with
                                           | nat_R_O_R => n_R
                                           | @nat_R_S_R k₁ k₂ k_R =>
                                               match
                                                 m_R in (nat_R m₁0 m₂0)
                                                 return
                                                   (nat_R
                                                      match m₁0 return nat with
                                                      | O => n₁
                                                      | S l => fix_sub_1 k₁ l
                                                      end
                                                      match m₂0 return nat with
                                                      | O => n₂
                                                      | S l => fix_sub_2 k₂ l
                                                      end)
                                               with
                                               | nat_R_O_R => n_R
                                               | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                   sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                               end
                                           end (fix_sub_2 n₂ m₂) 
                                           (gen_path n₂ m₂)) (fix_sub_1 n₁ m₁)
                                        (gen_path n₁ m₁)) x₁ x₂ x_R l₁ l₂ l_R
                               end O O nat_R_O_R) true true bool_R_true_R Px₁ Px₂) =>
                @option_R_Some_R
                  (ordinal
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end))
                  (ordinal
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end))
                  (@ordinal_R
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)
                     ((let fix_size_1 : forall _ : list A₁, nat :=
                         fix size (s : list A₁) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       let fix_size_2 : forall _ : list A₂, nat :=
                         fix size (s : list A₂) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       fix
                       size_R (s₁1 : list A₁) (s₂1 : list A₂)
                              (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                         nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                         match
                           s_R1 in (list_R _ s₁2 s₂2)
                           return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                         with
                         | @list_R_nil_R _ _ _ => nat_R_O_R
                         | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                             @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                               (size_R s'₁0 s'₂0 s'_R0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                        match
                          s_R in (list_R _ s₁1 s₂1)
                          return
                            (@list_R A₁ A₂ A_R
                               match s₁1 return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end
                               match s₂1 return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)
                        with
                        | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                        | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                        end))
                  (@Ordinal
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end) x₁ Px₁)
                  (@Ordinal
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end) x₂ Px₂)
                  (@ordinal_R_Ordinal_R
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)
                     ((let fix_size_1 : forall _ : list A₁, nat :=
                         fix size (s : list A₁) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       let fix_size_2 : forall _ : list A₂, nat :=
                         fix size (s : list A₂) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       fix
                       size_R (s₁1 : list A₁) (s₂1 : list A₂)
                              (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                         nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                         match
                           s_R1 in (list_R _ s₁2 s₂2)
                           return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                         with
                         | @list_R_nil_R _ _ _ => nat_R_O_R
                         | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                             @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                               (size_R s'₁0 s'₂0 s'_R0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                        match
                          s_R in (list_R _ s₁1 s₂1)
                          return
                            (@list_R A₁ A₂ A_R
                               match s₁1 return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end
                               match s₂1 return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)
                        with
                        | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                        | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                        end) x₁ x₂ x_R Px₁ Px₂ Px_R)
            | bool_R_false_R =>
                fun
                  (H : @eq bool
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end return nat
                            with
                            | O => S x₁
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x₁ l
                            end O) false)
                  (H0 : @eq bool
                          ((fix eqn (m n : nat) {struct m} : bool :=
                              match m return bool with
                              | O =>
                                  match n return bool with
                                  | O => true
                                  | S _ => false
                                  end
                              | S m' =>
                                  match n return bool with
                                  | O => false
                                  | S n' => eqn m' n'
                                  end
                              end)
                             match
                               (fix size (s : list A₂) : nat :=
                                  match s return nat with
                                  | nil => O
                                  | cons _ s' => S (size s')
                                  end)
                                 match s₂ return (list A₂) with
                                 | nil => @nil A₂
                                 | cons x _ => x
                                 end return nat
                             with
                             | O => S x₂
                             | S l =>
                                 (fix sub (n m : nat) {struct n} : nat :=
                                    match n return nat with
                                    | O => n
                                    | S k =>
                                        match m return nat with
                                        | O => n
                                        | S l0 => sub k l0
                                        end
                                    end) x₂ l
                             end O) false)
                  (_ : @eq_R bool bool bool_R
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end return nat
                            with
                            | O => S x₁
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x₁ l
                            end O)
                         ((fix eqn (m n : nat) {struct m} : bool :=
                             match m return bool with
                             | O => match n return bool with
                                    | O => true
                                    | S _ => false
                                    end
                             | S m' =>
                                 match n return bool with
                                 | O => false
                                 | S n' => eqn m' n'
                                 end
                             end)
                            match
                              (fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end return nat
                            with
                            | O => S x₂
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x₂ l
                            end O)
                         ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                             fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end in
                           let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                             fix eqn (m n : nat) {struct m} : bool :=
                               match m return bool with
                               | O =>
                                   match n return bool with
                                   | O => true
                                   | S _ => false
                                   end
                               | S m' =>
                                   match n return bool with
                                   | O => false
                                   | S n' => eqn m' n'
                                   end
                               end in
                           fix
                           eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) 
                                 (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct m_R} :
                             bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                             match
                               m_R in (nat_R m₁0 m₂0)
                               return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                             with
                             | nat_R_O_R =>
                                 match
                                   n_R in (nat_R n₁0 n₂0)
                                   return
                                     (bool_R
                                        match n₁0 return bool with
                                        | O => true
                                        | S _ => false
                                        end
                                        match n₂0 return bool with
                                        | O => true
                                        | S _ => false
                                        end)
                                 with
                                 | nat_R_O_R => bool_R_true_R
                                 | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                                 end
                             | @nat_R_S_R m'₁ m'₂ m'_R =>
                                 match
                                   n_R in (nat_R n₁0 n₂0)
                                   return
                                     (bool_R
                                        match n₁0 return bool with
                                        | O => false
                                        | S n' => fix_eqn_1 m'₁ n'
                                        end
                                        match n₂0 return bool with
                                        | O => false
                                        | S n' => fix_eqn_2 m'₂ n'
                                        end)
                                 with
                                 | nat_R_O_R => bool_R_false_R
                                 | @nat_R_S_R n'₁ n'₂ n'_R =>
                                     eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                                 end
                             end)
                            match
                              (fix size (s : list A₁) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end return nat
                            with
                            | O => S x₁
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x₁ l
                            end
                            match
                              (fix size (s : list A₂) : nat :=
                                 match s return nat with
                                 | nil => O
                                 | cons _ s' => S (size s')
                                 end)
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end return nat
                            with
                            | O => S x₂
                            | S l =>
                                (fix sub (n m : nat) {struct n} : nat :=
                                   match n return nat with
                                   | O => n
                                   | S k =>
                                       match m return nat with
                                       | O => n
                                       | S l0 => sub k l0
                                       end
                                   end) x₂ l
                            end
                            match
                              (let fix_size_1 : forall _ : list A₁, nat :=
                                 fix size (s : list A₁) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end in
                               let fix_size_2 : forall _ : list A₂, nat :=
                                 fix size (s : list A₂) : nat :=
                                   match s return nat with
                                   | nil => O
                                   | cons _ s' => S (size s')
                                   end in
                               fix
                               size_R (s₁1 : list A₁) (s₂1 : list A₂)
                                      (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                                 nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                                 match
                                   s_R1 in (list_R _ s₁2 s₂2)
                                   return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                                 with
                                 | @list_R_nil_R _ _ _ => nat_R_O_R
                                 | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                                     @nat_R_S_R (fix_size_1 s'₁0) 
                                       (fix_size_2 s'₂0) (size_R s'₁0 s'₂0 s'_R0)
                                 end)
                                match s₁ return (list A₁) with
                                | nil => @nil A₁
                                | cons x _ => x
                                end
                                match s₂ return (list A₂) with
                                | nil => @nil A₂
                                | cons x _ => x
                                end
                                match
                                  s_R in (list_R _ s₁1 s₂1)
                                  return
                                    (@list_R A₁ A₂ A_R
                                       match s₁1 return (list A₁) with
                                       | nil => @nil A₁
                                       | cons x _ => x
                                       end
                                       match s₂1 return (list A₂) with
                                       | nil => @nil A₂
                                       | cons x _ => x
                                       end)
                                with
                                | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                                | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                                end in (nat_R m₁ m₂)
                              return
                                (nat_R
                                   match m₁ return nat with
                                   | O => S x₁
                                   | S l =>
                                       (fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l0 => sub k l0
                                              end
                                          end) x₁ l
                                   end
                                   match m₂ return nat with
                                   | O => S x₂
                                   | S l =>
                                       (fix sub (n m : nat) {struct n} : nat :=
                                          match n return nat with
                                          | O => n
                                          | S k =>
                                              match m return nat with
                                              | O => n
                                              | S l0 => sub k l0
                                              end
                                          end) x₂ l
                                   end)
                            with
                            | nat_R_O_R => @nat_R_S_R x₁ x₂ x_R
                            | @nat_R_S_R l₁ l₂ l_R =>
                                (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                                   fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l => sub k l
                                         end
                                     end in
                                 let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                                   fix sub (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => n
                                     | S k =>
                                         match m return nat with
                                         | O => n
                                         | S l => sub k l
                                         end
                                     end in
                                 fix
                                 sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                                       (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                                   nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                                   let gen_path :
                                     let
                                       fix sub (n m : nat) {struct n} : nat :=
                                         match n return nat with
                                         | O => n
                                         | S k =>
                                             match m return nat with
                                             | O => n
                                             | S l => sub k l
                                             end
                                         end in
                                     forall n m : nat,
                                     @eq nat
                                       match n return nat with
                                       | O => n
                                       | S k =>
                                           match m return nat with
                                           | O => n
                                           | S l => sub k l
                                           end
                                       end (sub n m) :=
                                     let
                                       fix sub (n m : nat) {struct n} : nat :=
                                         match n return nat with
                                         | O => n
                                         | S k =>
                                             match m return nat with
                                             | O => n
                                             | S l => sub k l
                                             end
                                         end in
                                     fun n m : nat =>
                                     match
                                       n as n0
                                       return
                                         (@eq nat
                                            match n0 return nat with
                                            | O => n0
                                            | S k =>
                                                match m return nat with
                                                | O => n0
                                                | S l => sub k l
                                                end
                                            end (sub n0 m))
                                     with
                                     | O => @Logic.eq_refl nat (sub O m)
                                     | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                                     end in
                                   @eq_rect nat
                                     match n₁ return nat with
                                     | O => n₁
                                     | S k =>
                                         match m₁ return nat with
                                         | O => n₁
                                         | S l => fix_sub_1 k l
                                         end
                                     end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                                     (@eq_rect nat
                                        match n₂ return nat with
                                        | O => n₂
                                        | S k =>
                                            match m₂ return nat with
                                            | O => n₂
                                            | S l => fix_sub_2 k l
                                            end
                                        end
                                        (fun x : nat =>
                                         nat_R
                                           match n₁ return nat with
                                           | O => n₁
                                           | S k =>
                                               match m₁ return nat with
                                               | O => n₁
                                               | S l => fix_sub_1 k l
                                               end
                                           end x)
                                        match
                                          n_R in (nat_R n₁0 n₂0)
                                          return
                                            (nat_R
                                               match n₁0 return nat with
                                               | O => n₁
                                               | S k =>
                                                   match m₁ return nat with
                                                   | O => n₁
                                                   | S l => fix_sub_1 k l
                                                   end
                                               end
                                               match n₂0 return nat with
                                               | O => n₂
                                               | S k =>
                                                   match m₂ return nat with
                                                   | O => n₂
                                                   | S l => fix_sub_2 k l
                                                   end
                                               end)
                                        with
                                        | nat_R_O_R => n_R
                                        | @nat_R_S_R k₁ k₂ k_R =>
                                            match
                                              m_R in (nat_R m₁0 m₂0)
                                              return
                                                (nat_R
                                                   match m₁0 return nat with
                                                   | O => n₁
                                                   | S l => fix_sub_1 k₁ l
                                                   end
                                                   match m₂0 return nat with
                                                   | O => n₂
                                                   | S l => fix_sub_2 k₂ l
                                                   end)
                                            with
                                            | nat_R_O_R => n_R
                                            | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                                sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                            end
                                        end (fix_sub_2 n₂ m₂) (gen_path n₂ m₂))
                                     (fix_sub_1 n₁ m₁) (gen_path n₁ m₁)) x₁ x₂ x_R l₁ l₂
                                  l_R
                            end O O nat_R_O_R) false false bool_R_false_R H H0) =>
                @option_R_None_R
                  (ordinal
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end))
                  (ordinal
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end))
                  (@ordinal_R
                     ((fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end)
                     ((fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end)
                     ((let fix_size_1 : forall _ : list A₁, nat :=
                         fix size (s : list A₁) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       let fix_size_2 : forall _ : list A₂, nat :=
                         fix size (s : list A₂) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       fix
                       size_R (s₁1 : list A₁) (s₂1 : list A₂)
                              (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                         nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                         match
                           s_R1 in (list_R _ s₁2 s₂2)
                           return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                         with
                         | @list_R_nil_R _ _ _ => nat_R_O_R
                         | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                             @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                               (size_R s'₁0 s'₂0 s'_R0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                        match
                          s_R in (list_R _ s₁1 s₂1)
                          return
                            (@list_R A₁ A₂ A_R
                               match s₁1 return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end
                               match s₂1 return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)
                        with
                        | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                        | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                        end))
            end
              (@Logic.eq_refl bool
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₁
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₁ l
                    end O))
              (@Logic.eq_refl bool
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₂
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₂ l
                    end O))
              (@eq_R_eq_refl_R bool bool bool_R
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₁
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₁ l
                    end O)
                 ((fix eqn (m n : nat) {struct m} : bool :=
                     match m return bool with
                     | O => match n return bool with
                            | O => true
                            | S _ => false
                            end
                     | S m' =>
                         match n return bool with
                         | O => false
                         | S n' => eqn m' n'
                         end
                     end)
                    match
                      (fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₂
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₂ l
                    end O)
                 ((let fix_eqn_1 : forall (_ : nat) (_ : nat), bool :=
                     fix eqn (m n : nat) {struct m} : bool :=
                       match m return bool with
                       | O => match n return bool with
                              | O => true
                              | S _ => false
                              end
                       | S m' =>
                           match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                       end in
                   let fix_eqn_2 : forall (_ : nat) (_ : nat), bool :=
                     fix eqn (m n : nat) {struct m} : bool :=
                       match m return bool with
                       | O => match n return bool with
                              | O => true
                              | S _ => false
                              end
                       | S m' =>
                           match n return bool with
                           | O => false
                           | S n' => eqn m' n'
                           end
                       end in
                   fix
                   eqn_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat)
                         (n_R : nat_R n₁ n₂) {struct m_R} :
                     bool_R (fix_eqn_1 m₁ n₁) (fix_eqn_2 m₂ n₂) :=
                     match
                       m_R in (nat_R m₁0 m₂0)
                       return (bool_R (fix_eqn_1 m₁0 n₁) (fix_eqn_2 m₂0 n₂))
                     with
                     | nat_R_O_R =>
                         match
                           n_R in (nat_R n₁0 n₂0)
                           return
                             (bool_R
                                match n₁0 return bool with
                                | O => true
                                | S _ => false
                                end
                                match n₂0 return bool with
                                | O => true
                                | S _ => false
                                end)
                         with
                         | nat_R_O_R => bool_R_true_R
                         | @nat_R_S_R n₁0 n₂0 _ => bool_R_false_R
                         end
                     | @nat_R_S_R m'₁ m'₂ m'_R =>
                         match
                           n_R in (nat_R n₁0 n₂0)
                           return
                             (bool_R
                                match n₁0 return bool with
                                | O => false
                                | S n' => fix_eqn_1 m'₁ n'
                                end
                                match n₂0 return bool with
                                | O => false
                                | S n' => fix_eqn_2 m'₂ n'
                                end)
                         with
                         | nat_R_O_R => bool_R_false_R
                         | @nat_R_S_R n'₁ n'₂ n'_R => eqn_R m'₁ m'₂ m'_R n'₁ n'₂ n'_R
                         end
                     end)
                    match
                      (fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₁
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₁ l
                    end
                    match
                      (fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end)
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end return nat
                    with
                    | O => S x₂
                    | S l =>
                        (fix sub (n m : nat) {struct n} : nat :=
                           match n return nat with
                           | O => n
                           | S k => match m return nat with
                                    | O => n
                                    | S l0 => sub k l0
                                    end
                           end) x₂ l
                    end
                    match
                      (let fix_size_1 : forall _ : list A₁, nat :=
                         fix size (s : list A₁) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       let fix_size_2 : forall _ : list A₂, nat :=
                         fix size (s : list A₂) : nat :=
                           match s return nat with
                           | nil => O
                           | cons _ s' => S (size s')
                           end in
                       fix
                       size_R (s₁1 : list A₁) (s₂1 : list A₂)
                              (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                         nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                         match
                           s_R1 in (list_R _ s₁2 s₂2)
                           return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                         with
                         | @list_R_nil_R _ _ _ => nat_R_O_R
                         | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                             @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                               (size_R s'₁0 s'₂0 s'_R0)
                         end)
                        match s₁ return (list A₁) with
                        | nil => @nil A₁
                        | cons x _ => x
                        end
                        match s₂ return (list A₂) with
                        | nil => @nil A₂
                        | cons x _ => x
                        end
                        match
                          s_R in (list_R _ s₁1 s₂1)
                          return
                            (@list_R A₁ A₂ A_R
                               match s₁1 return (list A₁) with
                               | nil => @nil A₁
                               | cons x _ => x
                               end
                               match s₂1 return (list A₂) with
                               | nil => @nil A₂
                               | cons x _ => x
                               end)
                        with
                        | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                        | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                        end in (nat_R m₁ m₂)
                      return
                        (nat_R
                           match m₁ return nat with
                           | O => S x₁
                           | S l =>
                               (fix sub (n m : nat) {struct n} : nat :=
                                  match n return nat with
                                  | O => n
                                  | S k =>
                                      match m return nat with
                                      | O => n
                                      | S l0 => sub k l0
                                      end
                                  end) x₁ l
                           end
                           match m₂ return nat with
                           | O => S x₂
                           | S l =>
                               (fix sub (n m : nat) {struct n} : nat :=
                                  match n return nat with
                                  | O => n
                                  | S k =>
                                      match m return nat with
                                      | O => n
                                      | S l0 => sub k l0
                                      end
                                  end) x₂ l
                           end)
                    with
                    | nat_R_O_R => @nat_R_S_R x₁ x₂ x_R
                    | @nat_R_S_R l₁ l₂ l_R =>
                        (let fix_sub_1 : forall (_ : nat) (_ : nat), nat :=
                           fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k => match m return nat with
                                      | O => n
                                      | S l => sub k l
                                      end
                             end in
                         let fix_sub_2 : forall (_ : nat) (_ : nat), nat :=
                           fix sub (n m : nat) {struct n} : nat :=
                             match n return nat with
                             | O => n
                             | S k => match m return nat with
                                      | O => n
                                      | S l => sub k l
                                      end
                             end in
                         fix
                         sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
                               (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
                           nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
                           let gen_path :
                             let
                               fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l => sub k l
                                     end
                                 end in
                             forall n m : nat,
                             @eq nat
                               match n return nat with
                               | O => n
                               | S k =>
                                   match m return nat with
                                   | O => n
                                   | S l => sub k l
                                   end
                               end (sub n m) :=
                             let
                               fix sub (n m : nat) {struct n} : nat :=
                                 match n return nat with
                                 | O => n
                                 | S k =>
                                     match m return nat with
                                     | O => n
                                     | S l => sub k l
                                     end
                                 end in
                             fun n m : nat =>
                             match
                               n as n0
                               return
                                 (@eq nat
                                    match n0 return nat with
                                    | O => n0
                                    | S k =>
                                        match m return nat with
                                        | O => n0
                                        | S l => sub k l
                                        end
                                    end (sub n0 m))
                             with
                             | O => @Logic.eq_refl nat (sub O m)
                             | S n0 => @Logic.eq_refl nat (sub (S n0) m)
                             end in
                           @eq_rect nat
                             match n₁ return nat with
                             | O => n₁
                             | S k =>
                                 match m₁ return nat with
                                 | O => n₁
                                 | S l => fix_sub_1 k l
                                 end
                             end (fun x : nat => nat_R x (fix_sub_2 n₂ m₂))
                             (@eq_rect nat
                                match n₂ return nat with
                                | O => n₂
                                | S k =>
                                    match m₂ return nat with
                                    | O => n₂
                                    | S l => fix_sub_2 k l
                                    end
                                end
                                (fun x : nat =>
                                 nat_R
                                   match n₁ return nat with
                                   | O => n₁
                                   | S k =>
                                       match m₁ return nat with
                                       | O => n₁
                                       | S l => fix_sub_1 k l
                                       end
                                   end x)
                                match
                                  n_R in (nat_R n₁0 n₂0)
                                  return
                                    (nat_R
                                       match n₁0 return nat with
                                       | O => n₁
                                       | S k =>
                                           match m₁ return nat with
                                           | O => n₁
                                           | S l => fix_sub_1 k l
                                           end
                                       end
                                       match n₂0 return nat with
                                       | O => n₂
                                       | S k =>
                                           match m₂ return nat with
                                           | O => n₂
                                           | S l => fix_sub_2 k l
                                           end
                                       end)
                                with
                                | nat_R_O_R => n_R
                                | @nat_R_S_R k₁ k₂ k_R =>
                                    match
                                      m_R in (nat_R m₁0 m₂0)
                                      return
                                        (nat_R
                                           match m₁0 return nat with
                                           | O => n₁
                                           | S l => fix_sub_1 k₁ l
                                           end
                                           match m₂0 return nat with
                                           | O => n₂
                                           | S l => fix_sub_2 k₂ l
                                           end)
                                    with
                                    | nat_R_O_R => n_R
                                    | @nat_R_S_R l₁0 l₂0 l_R0 =>
                                        sub_R k₁ k₂ k_R l₁0 l₂0 l_R0
                                    end
                                end (fix_sub_2 n₂ m₂) (gen_path n₂ m₂)) 
                             (fix_sub_1 n₁ m₁) (gen_path n₁ m₁)) x₁ x₂ x_R l₁ l₂ l_R
                    end O O nat_R_O_R)) in (option_R _ u₁ u₂)
            return
              (@list_R
                 (ordinal
                    ((fix size (s : list A₁) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end))
                 (ordinal
                    ((fix size (s : list A₂) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end))
                 (@ordinal_R
                    ((fix size (s : list A₁) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end)
                    ((fix size (s : list A₂) : nat :=
                        match s return nat with
                        | nil => O
                        | cons _ s' => S (size s')
                        end)
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end)
                    ((let fix_size_1 : forall _ : list A₁, nat :=
                        fix size (s : list A₁) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end in
                      let fix_size_2 : forall _ : list A₂, nat :=
                        fix size (s : list A₂) : nat :=
                          match s return nat with
                          | nil => O
                          | cons _ s' => S (size s')
                          end in
                      fix
                      size_R (s₁1 : list A₁) (s₂1 : list A₂)
                             (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                        nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                        match
                          s_R1 in (list_R _ s₁2 s₂2)
                          return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                        with
                        | @list_R_nil_R _ _ _ => nat_R_O_R
                        | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                            @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                              (size_R s'₁0 s'₂0 s'_R0)
                        end)
                       match s₁ return (list A₁) with
                       | nil => @nil A₁
                       | cons x _ => x
                       end
                       match s₂ return (list A₂) with
                       | nil => @nil A₂
                       | cons x _ => x
                       end
                       match
                         s_R in (list_R _ s₁1 s₂1)
                         return
                           (@list_R A₁ A₂ A_R
                              match s₁1 return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end
                              match s₂1 return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end)
                       with
                       | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                       | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                       end))
                 match
                   u₁
                   return
                     (list
                        (ordinal
                           ((fix size (s : list A₁) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₁ return (list A₁) with
                              | nil => @nil A₁
                              | cons x _ => x
                              end)))
                 with
                 | Some y =>
                     @cons
                       (ordinal
                          ((fix size (s : list A₁) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₁ return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end)) y (fix_pmap_1 s'₁)
                 | None => fix_pmap_1 s'₁
                 end
                 match
                   u₂
                   return
                     (list
                        (ordinal
                           ((fix size (s : list A₂) : nat :=
                               match s return nat with
                               | nil => O
                               | cons _ s' => S (size s')
                               end)
                              match s₂ return (list A₂) with
                              | nil => @nil A₂
                              | cons x _ => x
                              end)))
                 with
                 | Some y =>
                     @cons
                       (ordinal
                          ((fix size (s : list A₂) : nat :=
                              match s return nat with
                              | nil => O
                              | cons _ s' => S (size s')
                              end)
                             match s₂ return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end)) y (fix_pmap_2 s'₂)
                 | None => fix_pmap_2 s'₂
                 end)
          with
          | @option_R_Some_R _ _ _ y₁ y₂ y_R =>
              @list_R_cons_R
                (ordinal
                   ((fix size (s : list A₁) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x _ => x
                      end))
                (ordinal
                   ((fix size (s : list A₂) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end))
                (@ordinal_R
                   ((fix size (s : list A₁) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x _ => x
                      end)
                   ((fix size (s : list A₂) : nat :=
                       match s return nat with
                       | nil => O
                       | cons _ s' => S (size s')
                       end)
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end)
                   ((let fix_size_1 : forall _ : list A₁, nat :=
                       fix size (s : list A₁) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end in
                     let fix_size_2 : forall _ : list A₂, nat :=
                       fix size (s : list A₂) : nat :=
                         match s return nat with
                         | nil => O
                         | cons _ s' => S (size s')
                         end in
                     fix
                     size_R (s₁1 : list A₁) (s₂1 : list A₂)
                            (s_R1 : @list_R A₁ A₂ A_R s₁1 s₂1) {struct s_R1} :
                       nat_R (fix_size_1 s₁1) (fix_size_2 s₂1) :=
                       match
                         s_R1 in (list_R _ s₁2 s₂2)
                         return (nat_R (fix_size_1 s₁2) (fix_size_2 s₂2))
                       with
                       | @list_R_nil_R _ _ _ => nat_R_O_R
                       | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁0 s'₂0 s'_R0 =>
                           @nat_R_S_R (fix_size_1 s'₁0) (fix_size_2 s'₂0)
                             (size_R s'₁0 s'₂0 s'_R0)
                       end)
                      match s₁ return (list A₁) with
                      | nil => @nil A₁
                      | cons x _ => x
                      end
                      match s₂ return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end
                      match
                        s_R in (list_R _ s₁1 s₂1)
                        return
                          (@list_R A₁ A₂ A_R
                             match s₁1 return (list A₁) with
                             | nil => @nil A₁
                             | cons x _ => x
                             end
                             match s₂1 return (list A₂) with
                             | nil => @nil A₂
                             | cons x _ => x
                             end)
                      with
                      | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
                      | @list_R_cons_R _ _ _ x₁0 x₂0 x_R0 s'₁0 s'₂0 _ => x_R0
                      end)) y₁ y₂ y_R (fix_pmap_1 s'₁) (fix_pmap_2 s'₂)
                (pmap_R s'₁ s'₂ s'_R)
          | @option_R_None_R _ _ _ => pmap_R s'₁ s'₂ s'_R
          end
      end)
     ((fix iota (m n : nat) {struct n} : list nat :=
         match n return (list nat) with
         | O => @nil nat
         | S n' => @cons nat m (iota (S m) n')
         end) O
        ((fix size (s : list A₁) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₁ return (list A₁) with
                 | nil => @nil A₁
                 | cons x _ => x
                 end))
     ((fix iota (m n : nat) {struct n} : list nat :=
         match n return (list nat) with
         | O => @nil nat
         | S n' => @cons nat m (iota (S m) n')
         end) O
        ((fix size (s : list A₂) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₂ return (list A₂) with
                 | nil => @nil A₂
                 | cons x _ => x
                 end))
     ((let fix_iota_1 : forall (_ : nat) (_ : nat), list nat :=
         fix iota (m n : nat) {struct n} : list nat :=
           match n return (list nat) with
           | O => @nil nat
           | S n' => @cons nat m (iota (S m) n')
           end in
       let fix_iota_2 : forall (_ : nat) (_ : nat), list nat :=
         fix iota (m n : nat) {struct n} : list nat :=
           match n return (list nat) with
           | O => @nil nat
           | S n' => @cons nat m (iota (S m) n')
           end in
       fix
       iota_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct
              n_R} : @list_R nat nat nat_R (fix_iota_1 m₁ n₁) (fix_iota_2 m₂ n₂) :=
         match
           n_R in (nat_R n₁0 n₂0)
           return (@list_R nat nat nat_R (fix_iota_1 m₁ n₁0) (fix_iota_2 m₂ n₂0))
         with
         | nat_R_O_R => @list_R_nil_R nat nat nat_R
         | @nat_R_S_R n'₁ n'₂ n'_R =>
             @list_R_cons_R nat nat nat_R m₁ m₂ m_R (fix_iota_1 (S m₁) n'₁)
               (fix_iota_2 (S m₂) n'₂)
               (iota_R (S m₁) (S m₂) (@nat_R_S_R m₁ m₂ m_R) n'₁ n'₂ n'_R)
         end) O O nat_R_O_R
        ((fix size (s : list A₁) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₁ return (list A₁) with
                 | nil => @nil A₁
                 | cons x _ => x
                 end)
        ((fix size (s : list A₂) : nat :=
            match s return nat with
            | nil => O
            | cons _ s' => S (size s')
            end) match s₂ return (list A₂) with
                 | nil => @nil A₂
                 | cons x _ => x
                 end)
        ((let fix_size_1 : forall _ : list A₁, nat :=
            fix size (s : list A₁) : nat :=
              match s return nat with
              | nil => O
              | cons _ s' => S (size s')
              end in
          let fix_size_2 : forall _ : list A₂, nat :=
            fix size (s : list A₂) : nat :=
              match s return nat with
              | nil => O
              | cons _ s' => S (size s')
              end in
          fix
          size_R (s₁0 : list A₁) (s₂0 : list A₂) (s_R0 : @list_R A₁ A₂ A_R s₁0 s₂0) {struct
                 s_R0} : nat_R (fix_size_1 s₁0) (fix_size_2 s₂0) :=
            match
              s_R0 in (list_R _ s₁1 s₂1) return (nat_R (fix_size_1 s₁1) (fix_size_2 s₂1))
            with
            | @list_R_nil_R _ _ _ => nat_R_O_R
            | @list_R_cons_R _ _ _ t₁ t₂ _ s'₁ s'₂ s'_R =>
                @nat_R_S_R (fix_size_1 s'₁) (fix_size_2 s'₂) (size_R s'₁ s'₂ s'_R)
            end) match s₁ return (list A₁) with
                 | nil => @nil A₁
                 | cons x _ => x
                 end match s₂ return (list A₂) with
                     | nil => @nil A₂
                     | cons x _ => x
                     end
           match
             s_R in (list_R _ s₁0 s₂0)
             return
               (@list_R A₁ A₂ A_R
                  match s₁0 return (list A₁) with
                  | nil => @nil A₁
                  | cons x _ => x
                  end match s₂0 return (list A₂) with
                      | nil => @nil A₂
                      | cons x _ => x
                      end)
           with
           | @list_R_nil_R _ _ _ => @list_R_nil_R A₁ A₂ A_R
           | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ _ => x_R
           end))).
Realizer diag_seqmx as diag_seqmx_R := diag_seqmx_simpl_R.
Parametricity scalar_seqmx.
Parametricity seqmx1.
Parametricity opp_seqmx.
Parametricity add_seqmx.
Parametricity sub_seqmx.
Parametricity trseqmx.
Parametricity mul_seqmx.
Parametricity scale_seqmx.
Parametricity eq_seq.
Parametricity eq_seqmx.
Definition top_left_seqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂),
       (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂ ->
       (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (B₁ B₂ : Type)
          (B_R : B₁ -> B₂ -> Type) (H : A₁0 -> B₁) (H0 : A₂0 -> B₂) =>
        forall (H1 : A₁0) (H2 : A₂0), A_R0 H1 H2 -> B_R (H H1) (H0 H2)) seqmx seqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) => list_R (list_R A_R0)) A₁ A₂
            A_R) A₁ A₂ A_R (top_left_seqmx (A:=A₁)) (top_left_seqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (H₁ : zero_of A₁) (H₂ : zero_of A₂)
  (H_R : (fun A₁0 A₂0 : Type => id) A₁ A₂ A_R H₁ H₂) (M₁ M₂ : seqmx)
  (M_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) => list_R (list_R A_R0)) A₁ A₂
           A_R M₁ M₂) =>
nth_R
  ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (zero_of₁ : zero_of A₁0)
      (zero_of₂ : zero_of A₂0) => id) A₁ A₂ A_R H₁ H₂ H_R)
  (nth_R (list_R_nil_R A_R) M_R nat_R_O_R) nat_R_O_R.
Parametricity usubseqmx.
Definition dsubseqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type),
       (fun (B₁ B₂ : nat -> nat -> Type)
          (B_R : forall x₁ x₂ : nat,
                 nat_R x₁ x₂ ->
                 forall x0₁ x0₂ : nat, nat_R x0₁ x0₂ -> B₁ x₁ x0₁ -> B₂ x₂ x0₂ -> Type)
          (H : forall m1 m2 n : nat, B₁ (m1 + m2)%N n -> B₁ m2 n)
          (H0 : forall m1 m2 n : nat, B₂ (m1 + m2)%N n -> B₂ m2 n) =>
        forall (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂) (m2₁ m2₂ : nat)
          (m2_R : nat_R m2₁ m2₂) (n₁ n₂ : nat) (n_R : nat_R n₁ n₂)
          (H1 : B₁ (m1₁ + m2₁)%N n₁) (H2 : B₂ (m1₂ + m2₂)%N n₂),
        B_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R) n₁ n₂ n_R H1 H2 ->
        B_R m2₁ m2₂ m2_R n₁ n₂ n_R (H m1₁ m2₁ n₁ H1) (H0 m1₂ m2₂ n₂ H2)) hseqmx hseqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
             (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
           (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
             A₂0 A_R0) A₁ A₂ A_R) (dsubseqmx (A:=A₁)) (dsubseqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂)
  (m2₁ m2₂ : nat) (_ : nat_R m2₁ m2₂) (n₁ n₂ : nat) (_ : nat_R n₁ n₂) 
  (M₁ M₂ : seqmx) => [eta drop_R m1_R (s₂:=M₂)].
Parametricity lsubseqmx.
Definition rsubseqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type),
       (fun (B₁ B₂ : nat -> nat -> Type)
          (B_R : forall x₁ x₂ : nat,
                 nat_R x₁ x₂ ->
                 forall x0₁ x0₂ : nat, nat_R x0₁ x0₂ -> B₁ x₁ x0₁ -> B₂ x₂ x0₂ -> Type)
          (H : forall m n1 n2 : nat, B₁ m (n1 + n2)%N -> B₁ m n2)
          (H0 : forall m n1 n2 : nat, B₂ m (n1 + n2)%N -> B₂ m n2) =>
        forall (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n1₁ n1₂ : nat) 
          (n1_R : nat_R n1₁ n1₂) (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂)
          (H1 : B₁ m₁ (n1₁ + n2₁)%N) (H2 : B₂ m₂ (n1₂ + n2₂)%N),
        B_R m₁ m₂ m_R (n1₁ + n2₁)%N (n1₂ + n2₂)%N (addn_R n1_R n2_R) H1 H2 ->
        B_R m₁ m₂ m_R n2₁ n2₂ n2_R (H m₁ n1₁ n2₁ H1) (H0 m₂ n1₂ n2₂ H2)) hseqmx hseqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
             (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
           (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
             A₂0 A_R0) A₁ A₂ A_R) (rsubseqmx (A:=A₁)) (rsubseqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (m₁ m₂ : nat) (_ : nat_R m₁ m₂) 
  (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂) (n2₁ n2₂ : nat) (_ : nat_R n2₁ n2₂)
  (M₁ M₂ : seqmx) => [eta map_R (drop_R n1_R) (s₂:=M₂)].
Parametricity ulsubseqmx.
Definition ursubseqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type),
       (fun (B₁ B₂ : nat -> nat -> Type)
          (B_R : forall x₁ x₂ : nat,
                 nat_R x₁ x₂ ->
                 forall x0₁ x0₂ : nat, nat_R x0₁ x0₂ -> B₁ x₁ x0₁ -> B₂ x₂ x0₂ -> Type)
          (H : forall m1 m2 n1 n2 : nat, B₁ (m1 + m2)%N (n1 + n2)%N -> B₁ m1 n2)
          (H0 : forall m1 m2 n1 n2 : nat, B₂ (m1 + m2)%N (n1 + n2)%N -> B₂ m1 n2) =>
        forall (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂) (m2₁ m2₂ : nat)
          (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂) 
          (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (H1 : B₁ (m1₁ + m2₁)%N (n1₁ + n2₁)%N)
          (H2 : B₂ (m1₂ + m2₂)%N (n1₂ + n2₂)%N),
        B_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R) (n1₁ + n2₁)%N 
          (n1₂ + n2₂)%N (addn_R n1_R n2_R) H1 H2 ->
        B_R m1₁ m1₂ m1_R n2₁ n2₂ n2_R (H m1₁ m2₁ n1₁ n2₁ H1) (H0 m1₂ m2₂ n1₂ n2₂ H2))
         hseqmx hseqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
             (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
           (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
             A₂0 A_R0) A₁ A₂ A_R) (ursubseqmx (A:=A₁)) (ursubseqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂)
  (m2₁ m2₂ : nat) (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂)
  (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (M₁ : hseqmx (m1₁ + m2₁) (n1₁ + n2₁))
  (M₂ : hseqmx (m1₂ + m2₂) (n1₂ + n2₂))
  (M_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
            (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
          (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
            A₂0 A_R0) A₁ A₂ A_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R)
           (n1₁ + n2₁)%N (n1₂ + n2₂)%N (addn_R n1_R n2_R) M₁ M₂) =>
rsubseqmx_R (usubseqmx_R M_R).
Definition dlsubseqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type),
       (fun (B₁ B₂ : nat -> nat -> Type)
          (B_R : forall x₁ x₂ : nat,
                 nat_R x₁ x₂ ->
                 forall x0₁ x0₂ : nat, nat_R x0₁ x0₂ -> B₁ x₁ x0₁ -> B₂ x₂ x0₂ -> Type)
          (H : forall m1 m2 n1 n2 : nat, B₁ (m1 + m2)%N (n1 + n2)%N -> B₁ m2 n1)
          (H0 : forall m1 m2 n1 n2 : nat, B₂ (m1 + m2)%N (n1 + n2)%N -> B₂ m2 n1) =>
        forall (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂) (m2₁ m2₂ : nat)
          (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂) 
          (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (H1 : B₁ (m1₁ + m2₁)%N (n1₁ + n2₁)%N)
          (H2 : B₂ (m1₂ + m2₂)%N (n1₂ + n2₂)%N),
        B_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R) (n1₁ + n2₁)%N 
          (n1₂ + n2₂)%N (addn_R n1_R n2_R) H1 H2 ->
        B_R m2₁ m2₂ m2_R n1₁ n1₂ n1_R (H m1₁ m2₁ n1₁ n2₁ H1) (H0 m1₂ m2₂ n1₂ n2₂ H2))
         hseqmx hseqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
             (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
           (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
             A₂0 A_R0) A₁ A₂ A_R) (dlsubseqmx (A:=A₁)) (dlsubseqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂)
  (m2₁ m2₂ : nat) (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂)
  (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (M₁ : hseqmx (m1₁ + m2₁) (n1₁ + n2₁))
  (M₂ : hseqmx (m1₂ + m2₂) (n1₂ + n2₂))
  (M_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
            (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
          (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
            A₂0 A_R0) A₁ A₂ A_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R)
           (n1₁ + n2₁)%N (n1₂ + n2₂)%N (addn_R n1_R n2_R) M₁ M₂) =>
lsubseqmx_R (dsubseqmx_R M_R).
Definition drsubseqmx_R     : forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type),
       (fun (B₁ B₂ : nat -> nat -> Type)
          (B_R : forall x₁ x₂ : nat,
                 nat_R x₁ x₂ ->
                 forall x0₁ x0₂ : nat, nat_R x0₁ x0₂ -> B₁ x₁ x0₁ -> B₂ x₂ x0₂ -> Type)
          (H : forall m1 m2 n1 n2 : nat, B₁ (m1 + m2)%N (n1 + n2)%N -> B₁ m2 n2)
          (H0 : forall m1 m2 n1 n2 : nat, B₂ (m1 + m2)%N (n1 + n2)%N -> B₂ m2 n2) =>
        forall (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂) (m2₁ m2₂ : nat)
          (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂) 
          (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (H1 : B₁ (m1₁ + m2₁)%N (n1₁ + n2₁)%N)
          (H2 : B₂ (m1₂ + m2₂)%N (n1₂ + n2₂)%N),
        B_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R) (n1₁ + n2₁)%N 
          (n1₂ + n2₂)%N (addn_R n1_R n2_R) H1 H2 ->
        B_R m2₁ m2₂ m2_R n2₁ n2₂ n2_R (H m1₁ m2₁ n1₁ n2₁ H1) (H0 m1₂ m2₂ n1₂ n2₂ H2))
         hseqmx hseqmx
         ((fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
             (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
           (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
             A₂0 A_R0) A₁ A₂ A_R) (drsubseqmx (A:=A₁)) (drsubseqmx (A:=A₂))
 := 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂)
  (m2₁ m2₂ : nat) (m2_R : nat_R m2₁ m2₂) (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂)
  (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) (M₁ : hseqmx (m1₁ + m2₁) (n1₁ + n2₁))
  (M₂ : hseqmx (m1₂ + m2₂) (n1₂ + n2₂))
  (M_R : (fun (A₁0 A₂0 : Type) (A_R0 : A₁0 -> A₂0 -> Type) (H H0 : nat) 
            (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
          (fun (A₁1 A₂1 : Type) (A_R1 : A₁1 -> A₂1 -> Type) => list_R (list_R A_R1)) A₁0
            A₂0 A_R0) A₁ A₂ A_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R)
           (n1₁ + n2₁)%N (n1₂ + n2₂)%N (addn_R n1_R n2_R) M₁ M₂) =>
rsubseqmx_R (dsubseqmx_R M_R).
Parametricity row_seqmx.
Parametricity col_seqmx.
Parametricity block_seqmx.
Parametricity delta_seqmx.
Definition trace_seqmx_R     : forall (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) 
         (H₁ : zero_of A₁) (H₂ : zero_of A₂)
         (_ : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁
                A₂ A_R H₁ H₂) (H1₁ : add_of A₁) (H1₂ : add_of A₂)
         (_ : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                 (H : forall (_ : A₁0) (_ : A₁0), A₁0)
                 (H0 : forall (_ : A₂0) (_ : A₂0), A₂0) =>
               forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) (H3 : A₁0) 
                 (H4 : A₂0) (_ : A_R0 H3 H4), A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R H1₁ H1₂)
         (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (s₁ : @hseqmx A₁ m₁ m₁) 
         (s₂ : @hseqmx A₂ m₂ m₂)
         (_ : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) 
                 (H H0 : nat) (_ : nat_R H H0) (H1 H2 : nat) (_ : nat_R H1 H2) =>
               (fun (A₁1 A₂1 : Type) (A_R1 : forall (_ : A₁1) (_ : A₂1), Type) =>
                @list_R (list A₁1) (list A₂1) (@list_R A₁1 A₂1 A_R1)) A₁0 A₂0 A_R0) A₁ A₂
                A_R m₁ m₂ m_R m₁ m₂ m_R s₁ s₂),
       A_R (@trace_seqmx A₁ H₁ H1₁ m₁ s₁) (@trace_seqmx A₂ H₂ H1₂ m₂ s₂)
 := 
fun (A₁ A₂ : Type) (A_R : forall (_ : A₁) (_ : A₂), Type) (H₁ : zero_of A₁)
  (H₂ : zero_of A₂)
  (H_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type) => A_R0) A₁ A₂ A_R
           H₁ H₂) (H1₁ : add_of A₁) (H1₂ : add_of A₂)
  (H1_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
             (H : forall (_ : A₁0) (_ : A₁0), A₁0) (H0 : forall (_ : A₂0) (_ : A₂0), A₂0)
           =>
           forall (H1 : A₁0) (H2 : A₂0) (_ : A_R0 H1 H2) (H3 : A₁0) 
             (H4 : A₂0) (_ : A_R0 H3 H4), A_R0 (H H1 H3) (H0 H2 H4)) A₁ A₂ A_R H1₁ H1₂) =>
let fix_trace_seqmx_1 : forall (m : nat) (_ : @hseqmx A₁ m m), A₁ :=
  fix trace_seqmx (m : nat) (s : @hseqmx A₁ m m) {struct m} : A₁ :=
    match m return A₁ with
    | O => @zero_op A₁ H₁
    | S n =>
        @add_op A₁ H1₁ (@top_left_seqmx A₁ H₁ s)
          (trace_seqmx n (@drsubseqmx A₁ (S O) n (S O) n s))
    end in
let fix_trace_seqmx_2 : forall (m : nat) (_ : @hseqmx A₂ m m), A₂ :=
  fix trace_seqmx (m : nat) (s : @hseqmx A₂ m m) {struct m} : A₂ :=
    match m return A₂ with
    | O => @zero_op A₂ H₂
    | S n =>
        @add_op A₂ H1₂ (@top_left_seqmx A₂ H₂ s)
          (trace_seqmx n (@drsubseqmx A₂ (S O) n (S O) n s))
    end in
fix
trace_seqmx_R (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (s₁ : @hseqmx A₁ m₁ m₁)
              (s₂ : @hseqmx A₂ m₂ m₂)
              (s_R : (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
                        (H H0 : nat) (_ : nat_R H H0) (H1 H2 : nat) 
                        (_ : nat_R H1 H2) =>
                      (fun (A₁1 A₂1 : Type) (A_R1 : forall (_ : A₁1) (_ : A₂1), Type) =>
                       @list_R (list A₁1) (list A₂1) (@list_R A₁1 A₂1 A_R1)) A₁0 A₂0 A_R0)
                       A₁ A₂ A_R m₁ m₂ m_R m₁ m₂ m_R s₁ s₂) {struct m_R} :
  A_R (fix_trace_seqmx_1 m₁ s₁) (fix_trace_seqmx_2 m₂ s₂) :=
  match
    m_R in (nat_R m₁0 m₂0)
    return (A_R (fix_trace_seqmx_1 m₁0 s₁) (fix_trace_seqmx_2 m₂0 s₂))
  with
  | nat_R_O_R =>
      (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
         (zero_of₁ : zero_of A₁0) (zero_of₂ : zero_of A₂0)
         (zero_of_R : (fun (A₁1 A₂1 : Type) (A_R1 : forall (_ : A₁1) (_ : A₂1), Type) =>
                       A_R1) A₁0 A₂0 A_R0 zero_of₁ zero_of₂) => zero_of_R) A₁ A₂ A_R H₁ H₂
        H_R
  | @nat_R_S_R n₁ n₂ n_R =>
      (fun (A₁0 A₂0 : Type) (A_R0 : forall (_ : A₁0) (_ : A₂0), Type)
         (add_of₁ : add_of A₁0) (add_of₂ : add_of A₂0)
         (add_of_R : (fun (A₁1 A₂1 : Type) (A_R1 : forall (_ : A₁1) (_ : A₂1), Type)
                        (H : forall (_ : A₁1) (_ : A₁1), A₁1)
                        (H0 : forall (_ : A₂1) (_ : A₂1), A₂1) =>
                      forall (H1 : A₁1) (H2 : A₂1) (_ : A_R1 H1 H2) 
                        (H3 : A₁1) (H4 : A₂1) (_ : A_R1 H3 H4), 
                      A_R1 (H H1 H3) (H0 H2 H4)) A₁0 A₂0 A_R0 add_of₁ add_of₂) => add_of_R)
        A₁ A₂ A_R H1₁ H1₂ H1_R (@top_left_seqmx A₁ H₁ s₁) (@top_left_seqmx A₂ H₂ s₂)
        (@top_left_seqmx_R A₁ A₂ A_R H₁ H₂ H_R s₁ s₂ s_R)
        (fix_trace_seqmx_1 n₁ (@drsubseqmx A₁ (S O) n₁ (S O) n₁ s₁))
        (fix_trace_seqmx_2 n₂ (@drsubseqmx A₂ (S O) n₂ (S O) n₂ s₂))
        (trace_seqmx_R n₁ n₂ n_R (@drsubseqmx A₁ (S O) n₁ (S O) n₁ s₁)
           (@drsubseqmx A₂ (S O) n₂ (S O) n₂ s₂)
           (@drsubseqmx_R A₁ A₂ A_R (S O) (S O) (@nat_R_S_R O O nat_R_O_R) n₁ n₂ n_R 
              (S O) (S O) (@nat_R_S_R O O nat_R_O_R) n₁ n₂ n_R s₁ s₂ s_R))
  end.
Parametricity pid_seqmx.
Parametricity copid_seqmx.

Section seqmx_more_op.

Variable R : Type.
Context `{zero_of R}.
Context (C : Type).
Context `{spec_of C R}.

Global Instance spec_seqmx m n : spec_of (@seqmx C) 'M[R]_(m, n) :=
  fun s => \matrix_(i, j) nth 0%C (nth [::] (map_seqmx spec s) i) j.

End seqmx_more_op.

Arguments spec_seqmx / _ _ _ _ _ _ _ : assert.

Section seqmx_theory.

Section seqmx.

Variable R : Type.
Context `{zero_of R, one_of R, opp_of R, add_of R, mul_of R, eq_of R}.

Local Instance specR : spec_of R R := spec_id.

Local Instance implem_ord : forall n, (implem_of 'I_n 'I_n) :=
  fun _ => implem_id.

Local Open Scope rel_scope.

CoInductive Rseqmx {m1 m2} (rm : nat_R m1 m2) {n1 n2} (rn : nat_R n1 n2) :
  'M[R]_(m1,n1) -> hseqmx m2 n2 -> Type :=
  Rseqmx_spec (A : 'M[R]_(m1, n1)) M of
    size M = m2
  & forall i, i < m2 -> size (nth [::] M i) = n2
  & (forall i j, (A i j = nth 0%C (nth [::] M i) j)) : Rseqmx rm rn A M.

(* Definition Rord n (i : 'I_n) j := i = j :> nat. *)

Lemma ord_enum_eqE p : ord_enum_eq p = enum 'I_p.
Proof. by rewrite enumT unlock; apply:eq_pmap ; exact:insub_eqE. Qed.

Instance Rseqmx_seqmx_of_fun m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
         f g :
  refines (eq ==> eq ==> eq) f g ->
  refines (Rseqmx rm rn) (\matrix_(i, j) f i j)
          (seqmx_of_fun (I:=(fun n => 'I_n)) g).
Proof.
  move=> h.
  rewrite refinesE; constructor; rewrite -?(nat_R_eq rm) -?(nat_R_eq rn).
      by rewrite !size_map ord_enum_eqE size_enum_ord.
    move=> i ltim.
    by rewrite (nth_map (Ordinal ltim)) !size_map ord_enum_eqE size_enum_ord.
  move=> i j.
  rewrite mxE /seqmx_of_fun !ord_enum_eqE /implem /implem_ord /implem_id.
  rewrite !map_id (nth_map i) ?size_enum_ord // nth_ord_enum.
  rewrite (nth_map j) ?size_enum_ord // nth_ord_enum.
  apply refinesP; eapply refines_apply.
    eapply refines_apply; tc.
    by rewrite refinesE.
  by rewrite refinesE.
Qed.

Instance Rseqmx_mkseqmx_ord m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx rm rn) (matrix_of_fun matrix_key)
          (@mkseqmx_ord R m1 n1).
Proof.
rewrite refinesE=> _ M ->; constructor; rewrite -?(nat_R_eq rm) -?(nat_R_eq rn).
    by rewrite size_map ord_enum_eqE size_enum_ord.
  move=> i ltim.
  rewrite (nth_map (Ordinal ltim)) ?ord_enum_eqE ?size_enum_ord // size_map.
  by rewrite size_enum_ord.
move=> i j.
by rewrite mxE (nth_map i) ?ord_enum_eqE ?size_enum_ord // (nth_map j)
           ?size_enum_ord // !nth_ord_enum.
Qed.

Instance Rseqmx_const_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx rm rn) matrix.const_mx (const_seqmx m2 n2).
Proof.
  rewrite refinesE=> _ x ->; constructor=> [|i ltim|i j].
      by rewrite size_nseq.
    by rewrite nth_nseq ltim size_nseq.
  by rewrite -(nat_R_eq rm) -(nat_R_eq rn);
    do 2 (rewrite nth_nseq ltn_ord); rewrite mxE.
Qed.

Instance Rseqmx_0 m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn) (const_mx 0%C) (seqmx0 m2 n2).
Proof.
rewrite refinesE; constructor=>[|i|i j]; first by rewrite size_nseq.
  by rewrite nth_nseq => ->; rewrite size_nseq.
by rewrite mxE nth_nseq -(nat_R_eq rm) ltn_ord nth_nseq -(nat_R_eq rn) ltn_ord.
Qed.

Instance Rseqmx_top_left_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx (nat_R_S_R rm) (nat_R_S_R rm) ==> eq)
          (fun M => M ord0 ord0) top_left_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  by rewrite /top_left_op /top_left_seqmx h3.
Qed.

Lemma if_add_eq m n : (if m < m + n then m else (m + n)%N) = m.
Proof.
  case: n=> [|?]; first by rewrite addn0 ltnn.
  by rewrite ifT // -addn1 leq_add.
Qed.

Instance Rseqmx_usubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (addn_R rm1 rm2) rn ==> Rseqmx rm1 rn)
          (@matrix.usubmx R m11 m21 n1) (@usubseqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /usubseqmx.
      by rewrite size_take h1 if_add_eq.
    by rewrite nth_take ?h2 ?ltn_addr.
  by rewrite mxE nth_take ?h3 -?(nat_R_eq rm1).
Qed.

Instance Rseqmx_dsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (addn_R rm1 rm2) rn ==> Rseqmx rm2 rn)
          (@matrix.dsubmx R m11 m21 n1) (@dsubseqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dsubseqmx.
      by rewrite size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite nth_drop h2 ?ltn_add2l.
  by rewrite mxE nth_drop h3 (nat_R_eq rm1).
Qed.

Instance Rseqmx_lsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm (addn_R rn1 rn2) ==> Rseqmx rm rn1)
          (@matrix.lsubmx R m1 n11 n21) (@lsubseqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /lsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_take ?h1 ?h2 // if_add_eq.
  by rewrite mxE h3 (nth_map [::]) ?nth_take ?h1 -?(nat_R_eq rn1)
             -?(nat_R_eq rm).
Qed.

Instance Rseqmx_rsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm (addn_R rn1 rn2) ==> Rseqmx rm rn2)
          (@matrix.rsubmx R m1 n11 n21) (@rsubseqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /rsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_drop ?h1 ?h2 // addnC -addnBA ?subnn ?addn0.
  by rewrite mxE h3 (nth_map [::]) ?nth_drop ?h1 -?(nat_R_eq rm)
             ?(nat_R_eq rn1).
Qed.

Instance Rseqmx_ulsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm1 rn1)
          (@matrix.ulsubmx R m11 m21 n11 n21) (@ulsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ulsubseqmx /lsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    by rewrite (nth_map [::]) size_take ?nth_take ?h1 ?h2 ?if_add_eq ?ltn_addr.
  by rewrite !mxE h3 (nth_map [::]) ?size_take ?h1 ?if_add_eq ?nth_take
             -?(nat_R_eq rm1) -?(nat_R_eq rn1).
Qed.

Instance Rseqmx_ursubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm1 rn2)
          (@matrix.ursubmx R m11 m21 n11 n21) (@ursubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ursubseqmx /rsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    by rewrite (nth_map [::]) ?size_take ?size_drop ?nth_take ?h1 ?h2 ?if_add_eq
               ?ltn_addr // addnC -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_take ?nth_take ?h1
             ?if_add_eq -?(nat_R_eq rm1) ?(nat_R_eq rn1).
Qed.

Instance Rseqmx_dlsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm2 rn1)
          (@matrix.dlsubmx R m11 m21 n11 n21) (@dlsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dlsubseqmx /lsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite (nth_map [::]) ?size_take ?nth_drop ?size_drop ?h1 ?h2 ?if_add_eq
               ?ltn_add2l // addnC -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_take ?nth_drop ?size_drop ?h1
             -?(nat_R_eq rn1) -?(nat_R_eq rm1) // -(nat_R_eq rm2) addnC -addnBA
             ?subnn ?addn0.
Qed.

Instance Rseqmx_drsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm2 rn2)
          (@matrix.drsubmx R m11 m21 n11 n21) (@drsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /drsubseqmx /rsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite (nth_map [::]) size_drop ?nth_drop ?h1 ?h2 ?ltn_add2l // addnC
               -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_drop ?h1 -?(nat_R_eq rm1)
             -?(nat_R_eq rn1) // addnC -addnBA ?subnn ?addn0 -?(nat_R_eq rm2).
Qed.

Instance Rseqmx_row_seqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm rn1 ==> Rseqmx rm rn2 ==> Rseqmx rm (addn_R rn1 rn2))
          (@matrix.row_mx R m1 n11 n21) (@row_seqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite /row_seqmx zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size_cat ?size1_zip ?h1 ?h'1
               ?h2 ?h'2.
  rewrite mxE (nth_map ([::], [::])) ?nth_zip /= ?nth_cat ?size1_zip ?h1 ?h'1
          ?h2 ?h'2 //.
  case: (splitP j)=> k hk; rewrite ?(h3, h'3) hk -?(nat_R_eq rn1).
        by rewrite ltn_ord.
      rewrite ifN; first by rewrite addnC -addnBA ?subnn ?addn0.
      by rewrite ltnNge leq_addr.
    by rewrite -(nat_R_eq rm).
  by rewrite -(nat_R_eq rm).
Qed.

Instance Rseqmx_col_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm1 rn ==> Rseqmx rm2 rn ==> Rseqmx (addn_R rm1 rm2) rn)
          (@matrix.col_mx R m11 m21 n1) (@col_seqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim12|i j]; rewrite /col_seqmx.
      by rewrite size_cat h1 h'1.
    rewrite nth_cat h1 -(nat_R_eq rm1); case: (ltnP i m11)=> [ltim1|leqm1i];
      rewrite ?(h2, h'2) -?(nat_R_eq rm1) //.
    by rewrite -subn_gt0 subnBA // addnC subn_gt0 (nat_R_eq rm1).
  rewrite mxE nth_cat h1.
  case: (splitP i)=> k hk; rewrite ?(h3, h'3) hk -(nat_R_eq rm1).
    by rewrite ltn_ord.
  rewrite ifN; last by rewrite ltnNge leq_addr.
  by rewrite addnC -addnBA ?subnn ?addn0.
Qed.

Instance Rseqmx_block_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm1 rn1 ==> Rseqmx rm1 rn2 ==> Rseqmx rm2 rn1 ==>
                  Rseqmx rm2 rn2 ==> Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2))
          (@matrix.block_mx R m11 m21 n11 n21) (@block_seqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M1 sM1 h11 h21 h31] _ _ [M2 sM2 h12 h22 h32]
                     _ _ [M3 sM3 h13 h23 h33] _ _ [M4 sM4 h14 h24 h34].
  constructor=> [|i ltim12|i j]; rewrite /block_seqmx /col_seqmx /row_seqmx.
      by rewrite !zipwithE size_cat !size_map !size1_zip ?h11 ?h12 ?h13 ?h14.
    rewrite !zipwithE nth_cat size_map size1_zip ?h11 ?h12 // -(nat_R_eq rm1).
     case: (ltnP i m11)=> [ltim1|leqm1i];
     by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?size_cat
                ?(h11, h13) ?(h12, h14) ?(h21, h23) ?(h22, h24) -?(nat_R_eq rm1)
                // -subn_gt0 subnBA // addnC subn_gt0 (nat_R_eq rm1).
  rewrite mxE !zipwithE nth_cat size_map size1_zip h11 ?h12 // -(nat_R_eq rm1).
  case: (splitP i)=> k hk;
    rewrite (nth_map ([::], [::])) ?nth_zip ?size1_zip ?(h11, h13) ?(h12, h14)
            ?hk -?(nat_R_eq rm1) //= ?nth_cat ?(h21, h23) -?(nat_R_eq rm1) //
            ?mxE;
    case: (splitP j)=> l hl;
      rewrite ?(h31, h33) ?(h32, h34) ?hl -?(nat_R_eq rn1) ?ltn_ord // addnC
              -?[in _ < _]addnBA ?subnn ?addn0 -?(nat_R_eq rm2) // ?ifN ?ltnNge
              ?leq_addl //.
      by rewrite -addnBA ?subnn ?addn0.
    by rewrite -addnBA ?subnn ?addn0.
  by rewrite addnC -addnBA ?subnn ?addn0 -?addnBA ?subnn ?addn0.
Qed.

Lemma minSS (p q : nat) : minn p.+1 q.+1 = (minn p q).+1.
Proof. by rewrite /minn ltnS; case:ifP. Qed.

Lemma size_fold (s : seq (seq R)) k
      (hs : forall i : nat, i < size s -> size (nth [::] s i) = k) :
  size (foldr (zipwith cons) (nseq k [::]) s) = k.
Proof.
  elim: s hs=> [_|a s ihs hs] /=; first by rewrite size_nseq.
  rewrite zipwithE size_map size1_zip ?ihs; have /= ha := hs 0%N;
    rewrite ?ha //.
  by move=> q hq; rewrite -(hs q.+1).
Qed.

Lemma size_nth_fold (s : seq (seq R)) j k (ltkj : k < j)
      (hs : forall l : nat, l < size s -> size (nth [::] s l) = j) :
  size (nth [::] (foldr (zipwith cons) (nseq j [::]) s) k) = size s.
Proof.
  elim: s hs=> [_|a s ihs hs] /=.
    by rewrite nth_nseq if_same.
  rewrite zipwithE (nth_map (0%C, [::])) ?nth_zip /= ?ihs // ?size1_zip
          ?size_fold; have /= ha := hs 0%N; rewrite ?ha //;
    by move=> l hl; rewrite -(hs l.+1).
Qed.

Lemma nth_fold (s : seq (seq R)) j k l (ltks : k < size s) (ltlj : l < j)
      (hs : forall l : nat, l < size s -> size (nth [::] s l) = j) :
  nth 0%C (nth [::] (foldr (zipwith cons) (nseq j [::]) s) l) k
  = nth 0%C (nth [::] s k) l.
Proof.
  elim: s k ltks hs=> [_ _ _|a s ihs k ltks hs] //=.
  rewrite zipwithE (nth_map (0%C, [::])) ?nth_zip /= ?size1_zip ?size_fold;
    have /= ha := hs 0%N; rewrite ?ha //;
    first (case: k ltks=> [|k' ltk's] //=; rewrite ?ihs //);
    by move=> q hq; rewrite -(hs q.+1).
Qed.

Instance Rseqmx_trseqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rn rm) trmx (@trseqmx R m2 n2).
Proof.
  rewrite /trseqmx.
  case: rm=> [|k1 k2 rk] /=;
    rewrite refinesE=> _ _ [M sM h1 h2 h3];
    constructor=> [|i ltim|i j].
            by rewrite size_nseq.
          by rewrite nth_nseq ltim.
        by rewrite -(nat_R_eq rn) nth_nseq ltn_ord mxE h3 (size0nil h1)
                   !nth_nil.
      by rewrite size_fold ?h1.
    by rewrite size_nth_fold ?h1.
  by rewrite mxE h3 nth_fold ?h1 // -?(nat_R_eq rn) -?(nat_R_eq rk).
Qed.

Section seqmx_param.

Context (C : Type) (rAC : R -> C -> Type).
Context (I : nat -> Type)
        (rI : forall n1 n2, nat_R n1 n2 -> 'I_n1 -> I n2 -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C}.
Context `{spec_of C R}.
Context `{forall n, implem_of 'I_n (I n)}.
Context `{!refines rAC 0%C 0%C, !refines rAC 1%C 1%C}.
Context `{!refines (rAC ==> rAC) -%C -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%C +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%C *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eq_op eq_op}.
Context `{!refines (rAC ==> Logic.eq) spec_id spec}.
Context `{forall n1 n2 (rn : nat_R n1 n2),
             refines (ordinal_R rn ==> rI rn) implem_id implem}.

Definition RseqmxC {m1 m2} (rm : nat_R m1 m2) {n1 n2} (rn : nat_R n1 n2) :
  'M[R]_(m1, n1) -> hseqmx m2 n2 -> Type :=
  (Rseqmx rm rn \o (list_R (list_R rAC)))%rel.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: nat_Rxx. Qed.

(* Local Instance refines_refl_ord : forall m (i : 'I_m), refines nat_R i i | 999. *)
(* Proof. rewrite refinesE; elim=> *; exact: nat_Rxx. Qed. *)

(* Local Instance refines_eq_refl_nat : forall (m : nat), refines eq m m | 999.  *)
(* Proof. by rewrite refinesE. Qed. *)

Local Instance refines_ordinal_eq (m : nat) (i j : 'I_m) :
  refines (ordinal_R (nat_Rxx m)) i j -> refines eq i j.
Proof.
rewrite !refinesE=> [[m0 m1 mR i0 i1 _]].
apply: ord_inj; exact: nat_R_eq.
Qed.

Local Instance refines_fun_refl m n (f : 'I_m -> 'I_n -> R) :
  refines (eq ==> eq ==> eq) f f.
Proof.
  by rewrite refinesE=> _ x -> _ y ->.
Qed.

Global Instance RseqmxC_seqmx_of_fun m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) f g
       `{forall x y, refines (rI rm) x y ->
         forall z t, refines (rI rn) z t ->
         refines (rAC \o (@unify _)) (f x z) (g y t)} :
  refines (RseqmxC rm rn)
          (\matrix_(i, j) f i j) (seqmx_of_fun (I:=I) g).
Proof.
  eapply refines_trans; tc.
  rewrite refinesE.
  eapply (seqmx_of_fun_R (I_R:=rI))=> // *; apply refinesP.
    eapply refines_apply; tc.
  eapply refines_comp_unify; tc.
Qed.

Global Instance refine_seqmx_of_fun m n f g
       `{forall x y, refines (rI (nat_Rxx m)) x y ->
         forall z t, refines (rI (nat_Rxx n)) z t ->
         refines (rAC \o (@unify _)) (f x z) (g y t)} :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n))
          (\matrix_(i, j) f i j) (seqmx_of_fun (I:=I) g).
Proof. exact: RseqmxC_seqmx_of_fun. Qed.

Global Instance RseqmxC_mkseqmx_ord m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) :
  refines ((eq ==> eq ==> rAC) ==> RseqmxC rm rn)
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m1 n1).
Proof. param_comp mkseqmx_ord_R. Qed.

Global Instance refine_mkseqmx_ord m n :
  refines ((eq ==> eq ==> rAC) ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m n).
Proof. exact: RseqmxC_mkseqmx_ord. Qed.

Global Instance RseqmxC_const_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) :
  refines (rAC ==> RseqmxC rm rn) (@matrix.const_mx R m1 n1)
          (const_seqmx m2 n2).
Proof. param_comp const_seqmx_R. Qed.

Global Instance refine_const_seqmx m n :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx n)) (@matrix.const_mx R m n)
          (const_seqmx m n).
Proof. exact: RseqmxC_const_seqmx. Qed.

Global Instance RseqmxC_0 m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn) (const_mx 0%C) (@hzero_op _ _ _ m2 n2).
Proof. param_comp seqmx0_R. Qed.

Global Instance refine_0_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n)) (const_mx 0%C) (@hzero_op _ _ _ m n).
Proof. exact: RseqmxC_0. Qed.

Global Instance RseqmxC_top_left_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC (nat_R_S_R rm) (nat_R_S_R rm) ==> rAC)
          (fun M => M ord0 ord0)
          (@top_left_seqmx C _).
Proof. param_comp top_left_seqmx_R. Qed.

Global Instance refine_top_left_seqmx m :
  refines (RseqmxC (nat_R_S_R (nat_Rxx m)) (nat_R_S_R (nat_Rxx m)) ==> rAC)
          (fun M => M ord0 ord0)
          (@top_left_seqmx C _).
Proof. exact: RseqmxC_top_left_seqmx. Qed.

Global Instance RseqmxC_usubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC (addn_R rm1 rm2) rn ==> RseqmxC rm1 rn)
          (@matrix.usubmx R m11 m21 n1) (@usubseqmx C m12 m22 n2).
Proof. param_comp usubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_usubseqmx m1 m2 n :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n))
          (@matrix.usubmx R m1 m2 n) (@usubseqmx C m1 m2 n).
Proof. exact: RseqmxC_usubseqmx. Qed.

Global Instance RseqmxC_dsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC (addn_R rm1 rm2) rn ==> RseqmxC rm2 rn)
          (@matrix.dsubmx R m11 m21 n1) (@dsubseqmx C m12 m22 n2).
Proof. param_comp dsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_dsubseqmx m1 m2 n :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n))
          (@matrix.dsubmx R m1 m2 n) (@dsubseqmx C m1 m2 n).
Proof. exact: RseqmxC_dsubseqmx. Qed.

Global Instance RseqmxC_lsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm (addn_R rn1 rn2) ==> RseqmxC rm rn1)
          (@matrix.lsubmx R m1 n11 n21) (@lsubseqmx C m2 n12 n22).
Proof. param_comp lsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_lsubseqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m) (nat_Rxx n1))
          (@matrix.lsubmx R m n1 n2) (@lsubseqmx C m n1 n2).
Proof. exact: RseqmxC_lsubseqmx. Qed.

Global Instance RseqmxC_rsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm (addn_R rn1 rn2) ==> RseqmxC rm rn2)
          (@matrix.rsubmx R m1 n11 n21) (@rsubseqmx C m2 n12 n22).
Proof. param_comp rsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_rsubseqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m) (nat_Rxx n2))
          (@matrix.rsubmx R m n1 n2) (@rsubseqmx C m n1 n2).
Proof. exact: RseqmxC_rsubseqmx. Qed.

Global Instance RseqmxC_ulsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm1 rn1)
          (@matrix.ulsubmx R m11 m21 n11 n21) (@ulsubseqmx C m12 m22 n12 n22).
Proof. param_comp ulsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_ulsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n1))
          (@matrix.ulsubmx R m1 m2 n1 n2) (@ulsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_ulsubseqmx. Qed.

Global Instance RseqmxC_ursubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm1 rn2)
          (@matrix.ursubmx R m11 m21 n11 n21) (@ursubseqmx C m12 m22 n12 n22).
Proof. param_comp ursubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_ursubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n2))
          (@matrix.ursubmx R m1 m2 n1 n2) (@ursubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_ursubseqmx. Qed.

Global Instance RseqmxC_dlsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm2 rn1)
          (@matrix.dlsubmx R m11 m21 n11 n21) (@dlsubseqmx C m12 m22 n12 n22).
Proof. param_comp dlsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_dlsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n1))
          (@matrix.dlsubmx R m1 m2 n1 n2) (@dlsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_dlsubseqmx. Qed.

Global Instance RseqmxC_drsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm2 rn2)
          (@matrix.drsubmx R m11 m21 n11 n21) (@drsubseqmx C m12 m22 n12 n22).
Proof. param_comp drsubseqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_drsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n2))
          (@matrix.drsubmx R m1 m2 n1 n2) (@drsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_drsubseqmx. Qed.

Global Instance RseqmxC_row_seqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm rn1 ==> RseqmxC rm rn2 ==> RseqmxC rm (addn_R rn1 rn2))
          (@matrix.row_mx R m1 n11 n21) (@row_seqmx C m2 n12 n22).
Proof. param_comp row_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_row_seqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n1) ==> RseqmxC (nat_Rxx m) (nat_Rxx n2)
                   ==> RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)))
          (@matrix.row_mx R m n1 n2) (@row_seqmx C m n1 n2).
Proof. exact: RseqmxC_row_seqmx. Qed.

Global Instance RseqmxC_col_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm1 rn ==> RseqmxC rm2 rn ==> RseqmxC (addn_R rm1 rm2) rn)
          (@matrix.col_mx R m11 m21 n1) (@col_seqmx C m12 m22 n2).
Proof. param_comp col_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_col_seqmx m1 m2 n :
  refines (RseqmxC (nat_Rxx m1) (nat_Rxx n) ==> RseqmxC (nat_Rxx m2) (nat_Rxx n)
                   ==> RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n))
          (@matrix.col_mx R m1 m2 n) (@col_seqmx C m1 m2 n).
Proof. exact: RseqmxC_col_seqmx. Qed.

Global Instance RseqmxC_block_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm1 rn1 ==> RseqmxC rm1 rn2 ==> RseqmxC rm2 rn1 ==>
           RseqmxC rm2 rn2 ==> RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2))
    (@matrix.block_mx R m11 m21 n11 n21) (@block_seqmx C m12 m22 n12 n22).
Proof. param_comp block_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_block_seqmx m1 m2 n1 n2 :
  refines (RseqmxC (nat_Rxx m1) (nat_Rxx n1) ==>
           RseqmxC (nat_Rxx m1) (nat_Rxx n2) ==>
           RseqmxC (nat_Rxx m2) (nat_Rxx n1) ==>
           RseqmxC (nat_Rxx m2) (nat_Rxx n2) ==>
           RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)))
    (@matrix.block_mx R m1 m2 n1 n2) (@block_seqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_block_seqmx. Qed.

Global Instance RseqmxC_tr m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rn rm) trmx (@trseqmx C m2 n2).
Proof. param_comp trseqmx_R. Qed.

Global Instance refine_trseqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx n) (nat_Rxx m))
          trmx (@trseqmx C m n).
Proof. exact: RseqmxC_tr. Qed.

End seqmx_param.
End seqmx.

Section seqmx_ring.

Variable R : ringType.

(* The "Global" is needed for lemma RseqmxC_char_poly_mx below. *)
Global Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R := 1%R.
Local Instance oppR  : opp_of R := -%R.
Local Instance addR  : add_of R := +%R.
Local Instance mulR  : mul_of R := *%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.
Local Instance specR_ring : spec_of R R := spec_id.

Local Instance implem_ord_ring : forall n, (implem_of 'I_n 'I_n) :=
  fun _ => implem_id.

Local Open Scope rel_scope.

Instance Rseqmx_diag_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx (nat_R_S_R nat_R_O_R) rm ==> Rseqmx rm rm)
          diag_mx (diag_seqmx (A:=R)).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j].
      by rewrite size_map ord_enum_eqE size_enum_ord h2.
    by rewrite /diag_seqmx /mkseqmx_ord ord_enum_eqE h2 //
               (nth_map (Ordinal ltim)) ?size_enum_ord //
               size_map size_enum_ord.
  rewrite mxE h3 /diag_seqmx /mkseqmx_ord ord_enum_eqE h2 // -(nat_R_eq rm)
          (nth_map i) ?size_enum_ord // (nth_map j) ?size_enum_ord //
          !nth_ord_enum.
  by case: (i == j).
Qed.

Existing Instance Rseqmx_const_seqmx.

Instance Rseqmx_scalar_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (eq ==> Rseqmx rm rm) scalar_mx (scalar_seqmx (A:=R) m2).
Proof.
  rewrite refinesE=> x y rxy.
  rewrite /scalar_seqmx -diag_const_mx.
  exact: refinesP.
Qed.

Instance Rseqmx_1 m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm rm) 1%:M (seqmx1 (A:=R) m2).
Proof.
  rewrite /seqmx1.
  eapply refines_apply; first exact: Rseqmx_scalar_seqmx.
  by rewrite refinesE.
Qed.

Instance Rseqmx_opp m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rm rn) -%R -%C.
Proof.
rewrite refinesE=> ? ? [A M h1 h2 h3].
constructor=> [|i ltim|i j]; first by rewrite size_map h1.
  rewrite (nth_map [::]); last by rewrite h1.
  by rewrite size_map h2.
rewrite mxE (nth_map [::]); last by rewrite h1 -(nat_R_eq rm) ltn_ord.
rewrite (nth_map 0); first by rewrite h3.
by rewrite h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ltn_ord.
Qed.

Instance Rseqmx_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rm rn ==> Rseqmx rm rn) +%R +%C.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ + _)%C]zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?h1 ?h'1
             -?(nat_R_eq rm) ?ltn_ord // mxE h3 h'3 zipwithE
             -[[seq _ | _ <- _]](mkseq_nth 0%C) nth_mkseq /=
             ?(nth_map (0%C, 0%C)) ?nth_zip ?size_map /= ?size1_zip ?h2 ?h'2
             -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord.
Qed.

Instance Rseqmx_sub m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rm rn ==> Rseqmx rm rn)
          (fun M N => M - N) sub_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ - _)%C]zipwithE.
      by rewrite size_map size1_zip ?size_map h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?(nth_map [::]) ?size_map ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  by rewrite !mxE h3 h'3 (nth_map ([::], [::])) ?zipwithE ?(nth_map (0%C, 0%C))
             ?nth_zip /= ?(nth_map [::]) ?size1_zip ?size_map ?(nth_map 0%C)
             ?h1 ?h'1 ?h2 ?h'2 -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord.
Qed.

Instance Rseqmx_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
         p1 p2 (rp : nat_R p1 p2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rn rp ==> Rseqmx rm rp)
          mulmx (@hmul_op _ _ _  m2 n2 p2).
Proof.
  case: rn=> [|k1 k2 rk];
    rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
    constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx /seqmx0.
        by rewrite size_nseq.
      by rewrite nth_nseq h1 ltim size_nseq.
    by rewrite nth_nseq h1 -(nat_R_eq rm) ltn_ord nth_nseq -(nat_R_eq rp)
               ltn_ord mxE big_ord0.
  constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?h1 // size_map /trseqmx /= size_fold ?h'1.
  rewrite (nth_map [::]) ?h1 -?(nat_R_eq rm) // (nth_map [::]) /trseqmx
          ?size_fold ?h'1 ?h'2 // -?(nat_R_eq rp) //.
  set F := (fun z x y => _).
  have ->: forall s1 s2 (t : R), (foldl2 F t s1 s2) =
    (t + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k).
    elim=>[s2 t|t1 s1 IHs s2 t].
      by rewrite min0n big_mkord big_ord0 GRing.addr0.
    case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
    by rewrite /= IHs minSS big_nat_recl // /F [(_ + t)%C]addrC addrA.
  rewrite add0r big_mkord size_nth_fold ?h'1 ?h2 -?(nat_R_eq rm) //
          ?(nat_R_eq rp) // /minn if_same mxE -(nat_R_eq rk).
  apply: eq_bigr=> k _.
  by rewrite h3 h'3 nth_fold ?h'1 ?(nat_R_eq rp) // -(nat_R_eq rk).
Qed.

Instance Rseqmx_scale m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx (R:=R) rm rn ==> Rseqmx rm rn) *:%R *:%C.
Proof.
  rewrite refinesE=> _ x -> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite [(_ *: _)%C]/scale_seqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_map ?h1 ?h2.
  by rewrite mxE (nth_map [::]) ?(nth_map 0%C) ?h1 ?h2 ?h3 -?(nat_R_eq rm)
             -?(nat_R_eq rn).
Qed.

Lemma eq_seqE (T : Type) (f : T -> T -> bool) s1 s2 : size s1 = size s2 ->
  eq_seq f s1 s2 = all (fun xy => f xy.1 xy.2) (zip s1 s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [] //= x2 s2 /eqP eq_sz.
by rewrite IHs //; apply/eqP.
Qed.

Instance Rseqmx_eq m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rm rn ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  suff ->: (M == N) = (eq_seq (eq_seq eqR) sM sN).
    exact: bool_Rxx.
  apply/eqP/idP=> [/matrixP heq|].
    rewrite eq_seqE ?h1 ?h'1 //.
    apply/(all_nthP ([::], [::]))=> i.
    rewrite size1_zip ?nth_zip ?h1 ?h'1 //=; move=> ltim.
    rewrite eq_seqE ?h2 ?h'2 //.
    apply/(all_nthP (0, 0))=> j.
    rewrite size1_zip ?nth_zip ?h2 ?h'2 //= -(nat_R_eq rn); move=> ltjn.
    rewrite -(nat_R_eq rm) in ltim.
    have := heq (Ordinal ltim) (Ordinal ltjn); rewrite h3 h'3=> ->.
    by apply/eqP.
  rewrite eq_seqE ?h1 ?h'1 //.
  move/(all_nthP ([::], [::])).
  rewrite size1_zip ?h1 ?h'1 //; move=> heq.
  apply/matrixP=> i j.
  have := heq i; rewrite -(nat_R_eq rm) ltn_ord; move/implyP; rewrite implyTb.
  rewrite nth_zip ?h1 ?h'1 //= eq_seqE ?h2 ?h'2 -?(nat_R_eq rm) //.
  move/(all_nthP (0, 0))=> /(_ j).
  rewrite nth_zip ?size1_zip ?h2 ?h'2 -?(nat_R_eq rm) //= h3 h'3 -?(nat_R_eq rn)
          (ltn_ord _) /eqR.
  move=> he.
  by apply/eqP; rewrite he.
Qed.

Instance Rseqmx_delta_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
         (i1 : 'I_m1) (i2 : 'I_m2) (ri : nat_R i1 i2) (j1 : 'I_n1) (j2 : 'I_n2)
         (rj : nat_R j1 j2) :
  refines (Rseqmx (R:=R) rm rn) (delta_mx i1 j1) (delta_seqmx m2 n2 i2 j2).
Proof.
  rewrite refinesE -(nat_R_eq ri) -(nat_R_eq rj); constructor=> [|k ltkm|k l].
      by rewrite size_map ord_enum_eqE size_enum_ord.
    by rewrite (nth_map (Ordinal ltkm)) !ord_enum_eqE ?size_enum_ord // size_map
               size_enum_ord.
  rewrite mxE /delta_seqmx /mkseqmx_ord !ord_enum_eqE -(nat_R_eq rm)
          -(nat_R_eq rn) (nth_map k) ?size_enum_ord // (nth_map l)
          ?size_enum_ord // !nth_ord_enum.
  by case: ifP.
Qed.

Instance Rseqmx_trace_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm rm ==> eq) mxtrace (trace_seqmx (A:=R) (m:=m2)).
Proof.
  apply refines_abstr.
  rewrite !refinesE /mxtrace.
  elim: rm=> [|n1 n2 rn ih] /= M sM rM.
    by rewrite big_ord0.
  rewrite big_ord_recl -(ih (drsubmx (M : 'M_(1 + n1, 1 + n1)))).
    have <- : M ord0 ord0 = top_left_seqmx sM.
      apply refinesP; rewrite -[M _ _]/((fun (M : 'M_(_)) => M _ _) _).
      eapply refines_apply.
        apply Rseqmx_top_left_seqmx.
      rewrite refinesE; eassumption.
    apply: congr2=> //; apply eq_bigr=> i _.
    by rewrite -[in LHS](@submxK R 1 n1 1 n1 M) -zmodp.rshift1
               [LHS](@block_mxEdr R 1 n1 1 n1).
  apply refinesP; eapply refines_apply.
    apply Rseqmx_drsubseqmx.
  rewrite refinesE.
  have H : nat_R_S_R rn = addn_R (nat_R_S_R nat_R_O_R) rn by [].
  rewrite H in rM.
  eassumption.
Qed.

Instance Rseqmx_pid_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
         r1 r2 (rr : nat_R r1 r2) :
  refines (Rseqmx (R:=R) rm rn) (pid_mx r1) (pid_seqmx m2 n2 r2).
Proof.
  rewrite refinesE; constructor=> [|i ltim|i j].
      by rewrite size_map ord_enum_eqE size_enum_ord.
    by rewrite (nth_map (Ordinal ltim)) !ord_enum_eqE ?size_enum_ord // size_map
               size_enum_ord.
  rewrite mxE /pid_seqmx /mkseqmx_ord !ord_enum_eqE -(nat_R_eq rm)
          -(nat_R_eq rn) (nth_map i) ?size_enum_ord // (nth_map j)
          ?size_enum_ord // !nth_ord_enum -(nat_R_eq rr).
  by case: ifP.
Qed.

Instance Rseqmx_copid_seqmx m1 m2 (rm : nat_R m1 m2) r1 r2 (rr : nat_R r1 r2) :
  refines (Rseqmx (R:=R) rm rm) (copid_mx r1) (copid_seqmx m2 r2).
Proof.
  rewrite /copid_mx /copid_seqmx /sub_op /sub_seqmx.
  eapply refines_apply; tc.
  eapply refines_apply; tc.
  exact: Rseqmx_pid_seqmx.
Qed.

Instance Rseqmx_spec_l m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Logic.eq) spec_id spec.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  rewrite /spec /spec_seqmx /spec_id /spec /specR /spec_id /map_seqmx map_id_in;
    last first.
    by move=> x; rewrite map_id.
  by apply/matrixP=> i j; rewrite h3 mxE.
Qed.

Section seqmx_ring_param.

Context (C : Type) (rAC : R -> C -> Type).
Context (I : nat -> Type)
        (rI : forall n1 n2, nat_R n1 n2 -> 'I_n1 -> I n2 -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C}.
Context `{spec_of C R}.
Context `{forall n, implem_of 'I_n (I n)}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (rAC ==> Logic.eq) spec_id spec}.
Context `{forall n1 n2 (rn : nat_R n1 n2),
             refines (ordinal_R rn ==> rI rn) implem_id implem}.

Notation RseqmxC := (RseqmxC rAC).

Global Instance RseqmxC_diag_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC (nat_R_S_R nat_R_O_R) rm ==> RseqmxC rm rm)
          diag_mx (diag_seqmx (A:=C)).
Proof. param_comp diag_seqmx_R. Qed.

Global Instance refine_diag_seqmx m :
  refines (RseqmxC (nat_R_S_R nat_R_O_R) (nat_Rxx m) ==>
           RseqmxC (nat_Rxx m) (nat_Rxx m))
          diag_mx (diag_seqmx (A:=C)).
Proof. exact: RseqmxC_diag_seqmx. Qed.

Global Instance RseqmxC_scalar_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (rAC ==> RseqmxC rm rm) scalar_mx (scalar_seqmx m2).
Proof. param_comp scalar_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_scalar_seqmx m :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx m)) scalar_mx (scalar_seqmx m).
Proof. exact: RseqmxC_scalar_seqmx. Qed.

Global Instance RseqmxC_1 m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm rm) 1%:M (seqmx1 m2).
Proof. param_comp seqmx1_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_1_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx m)) 1%:M (seqmx1 m).
Proof. exact: RseqmxC_1. Qed.

Global Instance RseqmxC_opp m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn) -%R -%C.
Proof. param_comp opp_seqmx_R. Qed.

Global Instance refine_opp_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          -%R -%C.
Proof. exact: RseqmxC_opp. Qed.

Global Instance RseqmxC_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> RseqmxC rm rn) +%R +%C.
Proof. param_comp add_seqmx_R. Qed.

Global Instance refine_add_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx n)) +%R +%C.
Proof. exact: RseqmxC_add. Qed.

Global Instance RseqmxC_sub m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> RseqmxC rm rn)
          (fun M N => M - N) sub_op.
Proof. param_comp sub_seqmx_R. Qed.

Global Instance refine_sub_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          (fun M N => M - N) sub_op.
Proof. exact: RseqmxC_sub. Qed.

Global Instance RseqmxC_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
       p1 p2 (rp : nat_R p1 p2) :
  refines (RseqmxC rm rn ==> RseqmxC rn rp ==> RseqmxC rm rp)
          mulmx (@hmul_op _ _ _  m2 n2 p2).
Proof. param_comp mul_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_mul_seqmx m n p :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx n) (nat_Rxx p)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx p))
          mulmx (@hmul_op _ _ _  m n p).
Proof. exact: RseqmxC_mul. Qed.

Global Instance RseqmxC_scale m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
  : refines (rAC ==> RseqmxC rm rn ==> RseqmxC rm rn) *:%R *:%C.
Proof. param_comp scale_seqmx_R. Qed.

Global Instance refine_scale_seqmx m n :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx n) ==>
               RseqmxC (nat_Rxx m) (nat_Rxx n)) *:%R *:%C.
Proof. exact: RseqmxC_scale. Qed.

Global Instance RseqmxC_eq m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> bool_R)
          eqtype.eq_op eq_op.
Proof. param_comp eq_seqmx_R. Qed.

Global Instance refine_eq_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> bool_R) eqtype.eq_op eq_op.
Proof. exact: RseqmxC_eq. Qed.

Global Instance RseqmxC_delta_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) (i1 : 'I_m1) (i2 : 'I_m2) (ri : nat_R i1 i2)
       (j1 : 'I_n1) (j2 : 'I_n2) (rj : nat_R j1 j2) :
  refines (RseqmxC rm rn) (delta_mx i1 j1) (delta_seqmx (A:=C) m2 n2 i2 j2).
Proof.
  eapply refines_trans; tc.
    eapply Rseqmx_delta_seqmx; eassumption.
  rewrite refinesE; eapply delta_seqmx_R; try exact: refinesP; apply nat_Rxx.
Qed.

Global Instance refine_delta_seqmx m n i j :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n))
          (delta_mx i j) (delta_seqmx m n i j).
Proof. apply RseqmxC_delta_seqmx; exact: nat_Rxx. Qed.

Global Instance RseqmxC_trace_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm rm ==> rAC) mxtrace (trace_seqmx (A:=C) (m:=m2)).
Proof. param_comp trace_seqmx_R; rewrite refinesE; apply nat_Rxx. Qed.

Global Instance refine_trace_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx m) ==> rAC)
          mxtrace (trace_seqmx (A:=C) (m:=m)).
Proof. exact: RseqmxC_trace_seqmx. Qed.

Global Instance RseqmxC_pid_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) r1 r2 (rr : nat_R r1 r2) :
  refines (RseqmxC rm rn) (pid_mx r1) (pid_seqmx m2 n2 r2).
Proof.
  eapply refines_trans; tc.
    eapply Rseqmx_pid_seqmx; eassumption.
  rewrite refinesE; eapply pid_seqmx_R; try exact: refinesP; apply nat_Rxx.
Qed.

Global Instance refine_pid_seqmx m n r :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n)) (pid_mx r) (pid_seqmx m n r).
Proof. apply RseqmxC_pid_seqmx; exact: nat_Rxx. Qed.

Global Instance RseqmxC_copid_seqmx m1 m2 (rm : nat_R m1 m2) r1 r2
       (rr : nat_R r1 r2) :
  refines (RseqmxC rm rm) (copid_mx r1) (copid_seqmx m2 r2).
Proof.
  eapply refines_trans; tc.
    eapply Rseqmx_copid_seqmx; eassumption.
  rewrite refinesE.
  eapply copid_seqmx_R=> *; try exact: refinesP; apply nat_Rxx.
Qed.

Global Instance refine_copid_seqmx m r :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx m)) (copid_mx r) (copid_seqmx m r).
Proof. apply RseqmxC_copid_seqmx; exact: nat_Rxx. Qed.

Global Instance RseqmxC_spec m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> Logic.eq) spec_id spec.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE /spec /spec_seqmx /spec /specR=> l l' rl.
  have -> : map_seqmx spec l = (map_seqmx spec l' : @seqmx R).
    elim: rl=> [|a b ra p q rp ih] //=.
    rewrite ih.
    apply: congr2=> //.
    elim: ra=> [|x y rxy s t rst ihs] //=.
    by rewrite ihs [specR_ring _]refines_eq.
  by [].
Qed.

Global Instance refine_spec_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> Logic.eq) spec_id spec.
Proof. exact: RseqmxC_spec. Qed.

End seqmx_ring_param.
End seqmx_ring.

Section seqmx2.

Local Open Scope rel_scope.

Variable R R' : Type.
Context `{!zero_of R, !zero_of R'}.

Instance Rseqmx_map_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx (R:=R) rm rn ==> Rseqmx (R:=R') rm rn)
          (fun f => @map_mx _ _ f m1 n1) map_mx_op.
Proof.
  rewrite refinesE=> _ f -> _ _ [M sM h1 h2 h3]; constructor=> [|i ltim|i j].
      by rewrite size_map.
    by rewrite (nth_map [::]) ?h1 // size_map h2.
  rewrite mxE (nth_map [::]) ?h1 -?(nat_R_eq rm) ?ltn_ord //.
  rewrite (nth_map (M i j)) ?h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord //.
  apply: congr1; rewrite {1}h3; apply set_nth_default.
  by rewrite h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ltn_ord.
Qed.

Section seqmx2_param.

Context (C : Type) (rAC : R -> C -> Type).
Context (D : Type) (rBD : R' -> D -> Type).

Global Instance RseqmxC_map_mx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
  : refines ((rAC ==> rBD) ==> RseqmxC rAC rm rn ==> RseqmxC rBD rm rn)
            (fun f => @map_mx _ _ f m1 n1) map_mx_op.
Proof. param_comp map_seqmx_R. Qed.

Global Instance refine_map_seqmx m n :
  refines ((rAC ==> rBD) ==> RseqmxC rAC (nat_Rxx m) (nat_Rxx n) ==>
                         RseqmxC rBD (nat_Rxx m) (nat_Rxx n))
          (fun f => @map_mx _ _ f m n) map_mx_op.
Proof. exact: RseqmxC_map_mx. Qed.

End seqmx2_param.
End seqmx2.

Section seqmx_poly.

Local Open Scope rel_scope.

Variable R : ringType.
Context (C : Type) (rAC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Variable polyX : polyC.
Context `{zero_of polyC, one_of polyC, add_of polyC, mul_of polyC,
          opp_of polyC}.
Context `{cast_of C polyC}.
Context `{!refines RpolyC 'X polyX}.
Context `{!refines RpolyC 0 0%C, !refines RpolyC 1 1%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC) -%R -%C}.
Context `{!refines (rAC ==> RpolyC) poly.polyC cast}.

Global Instance RseqmxC_char_poly_mx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rAC rm rm ==> RseqmxC RpolyC rm rm)
          (char_poly_mx (n:=m1))
          (fun s => (scalar_seqmx m2 polyX) - (map_seqmx cast s))%C.
Proof.
rewrite refinesE /char_poly_mx /sub_op /sub_seqmx=> M sM rM.
apply refinesP; eapply refines_apply.
eapply refines_apply; tc.
eapply refines_apply. tc.
eapply refines_apply; tc.
rewrite -[map_mx _ (n:=_)]/((fun f => @map_mx _ _ f _ _) _).
tc.
Qed.

Global Instance refine_char_poly_seqmx m :
  refines (RseqmxC rAC (nat_Rxx m) (nat_Rxx m)
           ==> RseqmxC RpolyC (nat_Rxx m) (nat_Rxx m))
          (char_poly_mx (n:=m))
          (fun s => (scalar_seqmx m polyX) - (map_seqmx cast s))%C.
Proof. exact: RseqmxC_char_poly_mx. Qed.

End seqmx_poly.

End seqmx_theory.

Section testmx.

From mathcomp Require Import ssrint poly.
From CoqEAL Require Import binint seqpoly binord.

Goal ((0 : 'M[int]_(2,2)) == 0).
by coqeal.
Abort.

Goal (1 : 'M[int]_(2)) == 1.
by coqeal.
Abort.

Goal ((- 0 : 'M[int]_(2,2)) == - - - 0).
by coqeal.
Abort.

Goal ((- 0 : 'M[{poly int}]_(2,2)) == - - - 0).
by coqeal.
Abort.

Goal (\tr (1 : 'M[{poly int}]_(10)) == 10%:Z%:P).
by coqeal.
Abort.

Goal (pid_mx 3 + copid_mx 3 == 1 :> 'M[int]_(10)).
by coqeal.
Abort.

Goal (pid_mx 4 * copid_mx 4 == 0 :> 'M[{poly {poly int}}]_(5)).
by coqeal.
Abort.

Definition Maddm : 'M[int]_(2) := \matrix_(i, j < 2) (i + j * i)%:Z.

Goal (Maddm == Maddm).
by coqeal.
Abort.

Definition M3 : 'M[int]_(2,2) := \matrix_(i,j < 2) 3%:Z.
Definition Mn3 : 'M[int]_(2,2) := \matrix_(i,j < 2) - 3%:Z.
Definition M6 : 'M[int]_(2,2) := \matrix_(i,j < 2) 6%:Z.

Definition V : 'rV[int]_(3) := \matrix_(i < 1, j < 3) 3%:Z.

Goal (diag_mx V == 2%:Z *: diag_mx V - diag_mx V).
by coqeal.
Abort.

Goal (delta_mx ord0 ord0 + delta_mx (Ordinal (ltnSn 1)) (Ordinal (ltnSn 1)) ==
      1 :> 'M[{poly int}]_(2)).
by coqeal.
Abort.

Goal (- - M3 == M3).
by coqeal.
Abort.

Goal (- M3 == Mn3).
by coqeal.
Abort.

Goal (M3 - M3 == 0).
by coqeal.
Abort.

Goal (M3 + M3 == M6).
rewrite -[X in X == _]/(spec_id _) [spec_id _]refines_eq /=.
by coqeal.
Abort.

Definition Mp : 'M[{poly {poly int}}]_(2,2) :=
  \matrix_(i,j < 2) (Poly [:: Poly [:: 3%:Z; 0; 1]; 0]).

Goal (Mp + -Mp == 0).
by coqeal.
Abort.

Goal (Mp *m 0 == 0 :> 'M[_]_(2,2)).
by coqeal.
Abort.

Definition M := \matrix_(i,j < 2) 1%num%:Z.
Definition N := \matrix_(i,j < 2) 2%num%:Z.
Definition P := \matrix_(i,j < 2) 14%num%:Z.

Goal (M + N + M + N + M + N + N + M + N) *m
   (M + N + M + N + M + N + N + M + N) =
  (P *m M + P *m N + P *m M + P *m N +
   P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
Time by coqeal.
Abort.

End testmx.
