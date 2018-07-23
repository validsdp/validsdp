From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare ML Module "paramcoq".

Global Ltac destruct_reflexivity :=
  intros ; repeat match goal with
  | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Global Parametricity Tactic := destruct_reflexivity.

(** Automation: for turning [sth_R a b] goals into mere [a = b] goals,
do [suff_eq sth_Rxx]. *)
Ltac suff_eq Rxx :=
  match goal with
  | [ |- ?R ?a ?b ] =>
    let H := fresh in
    suff H : a = b; first (rewrite H; eapply Rxx =>//)
  end.

Require Import ProofIrrelevance. (* for opaque terms *)

(* data types *)
Parametricity option.
Parametricity unit.
Parametricity bool.
Hint Resolve bool_R_true_R bool_R_false_R.
Parametricity nat.
Parametricity list.
Parametricity prod.

Lemma bool_Rxx b : bool_R b b.
Proof. by case: b. Qed.

Lemma nat_Rxx n : nat_R n n.
Proof.
  elim: n=> [|n];
    [ exact: nat_R_O_R | exact: nat_R_S_R ].
Qed.

Lemma list_Rxx T (rT : T -> T -> Type) l :
  (forall x, rT x x) -> list_R rT l l.
Proof.
move=> Hr; elim: l=> [|h t IH]; [exact: list_R_nil_R|].
exact: list_R_cons_R.
Qed.

Lemma option_Rxx T (rT : T -> T -> Type) l :
  (forall x, rT x x) -> option_R rT l l.
Proof. by move=> Hr; case: l => *; constructor. Qed.

(** ssrfun *)
Parametricity simpl_fun.

(** ssrbool *)
Parametricity SimplRel.
Parametricity orb.
Parametricity andb.
Parametricity implb.
Parametricity negb.
Parametricity addb.
Parametricity eqb.

(** ssrnat *)
Definition subn_rec_R : forall n₁ n₂ : nat,
       nat_R n₁ n₂ ->
       forall m₁ m₂ : nat, nat_R m₁ m₂ -> nat_R (n₁ - m₁)%Nrec (n₂ - m₂)%Nrec
 :=
let fix_sub_1 :=
  fix sub (n m : nat) {struct n} : nat :=
    match n with
    | 0 => n
    | succn k => match m with
                 | 0 => n
                 | succn l => sub k l
                 end
    end in
let fix_sub_2 :=
  fix sub (n m : nat) {struct n} : nat :=
    match n with
    | 0 => n
    | succn k => match m with
                 | 0 => n
                 | succn l => sub k l
                 end
    end in
fix
sub_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) {struct n_R} :
  nat_R (fix_sub_1 n₁ m₁) (fix_sub_2 n₂ m₂) :=
  let gen_path :
    let
      fix sub (n m : nat) {struct n} : nat :=
        match n with
        | 0 => n
        | succn k => match m with
                     | 0 => n
                     | succn l => sub k l
                     end
        end in
    forall n m : nat,
    match n with
    | 0 => n
    | succn k => match m with
                 | 0 => n
                 | succn l => sub k l
                 end
    end = sub n m :=
    let
      fix sub (n m : nat) {struct n} : nat :=
        match n with
        | 0 => n
        | succn k => match m with
                     | 0 => n
                     | succn l => sub k l
                     end
        end in
    fun n m : nat =>
    match
      n as n0
      return
        (match n0 with
         | 0 => n0
         | succn k => match m with
                      | 0 => n0
                      | succn l => sub k l
                      end
         end = sub n0 m)
    with
    | 0 => erefl (sub 0 m)
    | succn n0 => erefl (sub (succn n0) m)
    end in
  eq_rect
    match n₁ with
    | 0 => n₁
    | succn k => match m₁ with
                 | 0 => n₁
                 | succn l => fix_sub_1 k l
                 end
    end (nat_R^~ (fix_sub_2 n₂ m₂))
    (eq_rect
       match n₂ with
       | 0 => n₂
       | succn k => match m₂ with
                    | 0 => n₂
                    | succn l => fix_sub_2 k l
                    end
       end
       [eta nat_R
              match n₁ with
              | 0 => n₁
              | succn k => match m₁ with
                           | 0 => n₁
                           | succn l => fix_sub_1 k l
                           end
              end]
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R
              match n₁0 with
              | 0 => n₁
              | succn k => match m₁ with
                           | 0 => n₁
                           | succn l => fix_sub_1 k l
                           end
              end
              match n₂0 with
              | 0 => n₂
              | succn k => match m₂ with
                           | 0 => n₂
                           | succn l => fix_sub_2 k l
                           end
              end)
       with
       | nat_R_O_R => n_R
       | @nat_R_S_R k₁ k₂ k_R =>
           match
             m_R in (nat_R m₁0 m₂0)
             return
               (nat_R match m₁0 with
                      | 0 => n₁
                      | succn l => fix_sub_1 k₁ l
                      end match m₂0 with
                          | 0 => n₂
                          | succn l => fix_sub_2 k₂ l
                          end)
           with
           | nat_R_O_R => n_R
           | @nat_R_S_R l₁ l₂ l_R => sub_R k₁ k₂ k_R l₁ l₂ l_R
           end
       end (fix_sub_2 n₂ m₂) (gen_path n₂ m₂)) (fix_sub_1 n₁ m₁) 
    (gen_path n₁ m₁).
Definition subn_R : forall n₁ n₂ : nat,
       nat_R n₁ n₂ -> forall m₁ m₂ : nat, nat_R m₁ m₂ -> nat_R (n₁ - m₁) (n₂ - m₂) :=
let
'unit_R_tt_R in (unit_R x₁ x₂) := unit_R_tt_R
 return
   (forall n₁ n₂ : nat,
    nat_R n₁ n₂ ->
    forall m₁ m₂ : nat,
    nat_R m₁ m₂ ->
    nat_R ((let 'tt := x₁ in subn_rec) n₁ m₁) ((let 'tt := x₂ in subn_rec) n₂ m₂)) in
 subn_rec_R.
Parametricity addn_rec.
Parametricity addn.
Parametricity eqn.

(* This trick avoids having to apply Parametricity to eqtype structure *)
Opaque eqn subn.
Definition leqn := Eval cbv in leq.
Definition leqn_R : forall m₁ m₂ : nat,
       nat_R m₁ m₂ -> forall n₁ n₂ : nat, nat_R n₁ n₂ -> bool_R (leqn m₁ n₁) (leqn m₂ n₂) := 
fun (m₁ m₂ : nat) (m_R : nat_R m₁ m₂) (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) =>
eqn_R (subn_R m_R n_R) nat_R_O_R.
Realizer leq as leq_R := leqn_R.

Parametricity Logic.eq.

(* geq, ltn and gtn use SimplRel, not sure how well they will work in
   proofs... *)
Parametricity geq.
Parametricity ltn.
Parametricity gtn.

Parametricity maxn.
Parametricity minn.
Parametricity iter.
Parametricity iteri.
Parametricity iterop.
Parametricity muln_rec.
Parametricity muln.
Parametricity expn_rec.
Parametricity expn.
Definition fact_rec_R : forall n₁ n₂ : nat, nat_R n₁ n₂ -> nat_R (fact_rec n₁) (fact_rec n₂)
 :=
let fix_fact_rec_1 :=
  fix fact_rec (n : nat) : nat := match n with
                                  | 0 => 1
                                  | succn n' => n * fact_rec n'
                                  end in
let fix_fact_rec_2 :=
  fix fact_rec (n : nat) : nat := match n with
                                  | 0 => 1
                                  | succn n' => n * fact_rec n'
                                  end in
fix fact_rec_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  nat_R (fix_fact_rec_1 n₁) (fix_fact_rec_2 n₂) :=
  let gen_path :
    let
      fix fact_rec (n : nat) : nat :=
        match n with
        | 0 => 1
        | succn n' => n * fact_rec n'
        end in
    forall n : nat, match n with
                    | 0 => 1
                    | succn n' => n * fact_rec n'
                    end = fact_rec n :=
    let
      fix fact_rec (n : nat) : nat :=
        match n with
        | 0 => 1
        | succn n' => n * fact_rec n'
        end in
    fun n : nat =>
    match
      n as n0
      return (match n0 with
              | 0 => 1
              | succn n' => n0 * fact_rec n'
              end = fact_rec n0)
    with
    | 0 => erefl (fact_rec 0)
    | succn n0 => erefl (fact_rec (succn n0))
    end in
  eq_rect match n₁ with
          | 0 => 1
          | succn n' => n₁ * fix_fact_rec_1 n'
          end (nat_R^~ (fix_fact_rec_2 n₂))
    (eq_rect match n₂ with
             | 0 => 1
             | succn n' => n₂ * fix_fact_rec_2 n'
             end
       [eta nat_R match n₁ with
                  | 0 => 1
                  | succn n' => n₁ * fix_fact_rec_1 n'
                  end]
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R match n₁0 with
                  | 0 => 1
                  | succn n' => n₁ * fix_fact_rec_1 n'
                  end match n₂0 with
                      | 0 => 1
                      | succn n' => n₂ * fix_fact_rec_2 n'
                      end)
       with
       | nat_R_O_R => nat_R_S_R nat_R_O_R
       | @nat_R_S_R n'₁ n'₂ n'_R => muln_R n_R (fact_rec_R n'₁ n'₂ n'_R)
       end (fix_fact_rec_2 n₂) (gen_path n₂)) (fix_fact_rec_1 n₁) 
    (gen_path n₁).
Definition factorial_R     : forall n₁ n₂ : nat, nat_R n₁ n₂ -> nat_R n₁`! n₂`! := 
let
'unit_R_tt_R in (unit_R x₁ x₂) := unit_R_tt_R
 return
   (forall n₁ n₂ : nat,
    nat_R n₁ n₂ -> nat_R ((let 'tt := x₁ in fact_rec) n₁) ((let 'tt := x₂ in fact_rec) n₂))
 in fact_rec_R.
Parametricity odd.
Parametricity double_rec.
Parametricity double.
Definition half_R     : forall n₁ n₂ : nat, nat_R n₁ n₂ -> nat_R n₁./2 n₂./2
 := 
let fix_half_1 :=
  fix half (n : nat) : nat := match n with
                              | 0 => n
                              | succn n' => uphalf n'
                              end
  with uphalf (n : nat) : nat := match n with
                                 | 0 => n
                                 | succn n' => succn (half n')
                                 end
  for half in
let fix_half_2 :=
  fix half (n : nat) : nat := match n with
                              | 0 => n
                              | succn n' => uphalf n'
                              end
  with uphalf (n : nat) : nat := match n with
                                 | 0 => n
                                 | succn n' => succn (half n')
                                 end
  for half in
let fix_uphalf_1 :=
  fix half (n : nat) : nat := match n with
                              | 0 => n
                              | succn n' => uphalf n'
                              end
  with uphalf (n : nat) : nat := match n with
                                 | 0 => n
                                 | succn n' => succn (half n')
                                 end
  for uphalf in
let fix_uphalf_2 :=
  fix half (n : nat) : nat := match n with
                              | 0 => n
                              | succn n' => uphalf n'
                              end
  with uphalf (n : nat) : nat := match n with
                                 | 0 => n
                                 | succn n' => succn (half n')
                                 end
  for uphalf in
fix half_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  nat_R (fix_half_1 n₁) (fix_half_2 n₂) :=
  let gen_path :
    let half :=
      fix half (n : nat) : nat := match n with
                                  | 0 => n
                                  | succn n' => uphalf n'
                                  end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half n')
        end
      for half in
    let uphalf :=
      fix half0 (n : nat) : nat := match n with
                                   | 0 => n
                                   | succn n' => uphalf n'
                                   end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half0 n')
        end
      for uphalf in
    forall n : nat, match n with
                    | 0 => n
                    | succn n' => uphalf n'
                    end = half n :=
    let half :=
      fix half (n : nat) : nat := match n with
                                  | 0 => n
                                  | succn n' => uphalf n'
                                  end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half n')
        end
      for half in
    let uphalf :=
      fix half0 (n : nat) : nat := match n with
                                   | 0 => n
                                   | succn n' => uphalf n'
                                   end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half0 n')
        end
      for uphalf in
    fun n : nat =>
    match
      n as n0 return (match n0 with
                      | 0 => n0
                      | succn n' => uphalf n'
                      end = half n0)
    with
    | 0 => erefl (half 0)
    | succn n0 => erefl (half (succn n0))
    end in
  eq_rect match n₁ with
          | 0 => n₁
          | succn n' => fix_uphalf_1 n'
          end (nat_R^~ (fix_half_2 n₂))
    (eq_rect match n₂ with
             | 0 => n₂
             | succn n' => fix_uphalf_2 n'
             end [eta nat_R match n₁ with
                            | 0 => n₁
                            | succn n' => fix_uphalf_1 n'
                            end]
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R match n₁0 with
                  | 0 => n₁
                  | succn n' => fix_uphalf_1 n'
                  end match n₂0 with
                      | 0 => n₂
                      | succn n' => fix_uphalf_2 n'
                      end)
       with
       | nat_R_O_R => n_R
       | @nat_R_S_R n'₁ n'₂ n'_R => uphalf_R n'₁ n'₂ n'_R
       end (fix_half_2 n₂) (gen_path n₂)) (fix_half_1 n₁) (gen_path n₁)
with uphalf_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} :
  nat_R (fix_uphalf_1 n₁) (fix_uphalf_2 n₂) :=
  let gen_path :
    let half :=
      fix half (n : nat) : nat := match n with
                                  | 0 => n
                                  | succn n' => uphalf n'
                                  end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half n')
        end
      for half in
    let uphalf :=
      fix half0 (n : nat) : nat := match n with
                                   | 0 => n
                                   | succn n' => uphalf n'
                                   end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half0 n')
        end
      for uphalf in
    forall n : nat, match n with
                    | 0 => n
                    | succn n' => succn (half n')
                    end = uphalf n :=
    let half :=
      fix half (n : nat) : nat := match n with
                                  | 0 => n
                                  | succn n' => uphalf n'
                                  end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half n')
        end
      for half in
    let uphalf :=
      fix half0 (n : nat) : nat := match n with
                                   | 0 => n
                                   | succn n' => uphalf n'
                                   end
      with uphalf (n : nat) : nat :=
        match n with
        | 0 => n
        | succn n' => succn (half0 n')
        end
      for uphalf in
    fun n : nat =>
    match
      n as n0
      return (match n0 with
              | 0 => n0
              | succn n' => succn (half n')
              end = uphalf n0)
    with
    | 0 => erefl (uphalf 0)
    | succn n0 => erefl (uphalf (succn n0))
    end in
  eq_rect match n₁ with
          | 0 => n₁
          | succn n' => succn (fix_half_1 n')
          end (nat_R^~ (fix_uphalf_2 n₂))
    (eq_rect match n₂ with
             | 0 => n₂
             | succn n' => succn (fix_half_2 n')
             end
       [eta nat_R match n₁ with
                  | 0 => n₁
                  | succn n' => succn (fix_half_1 n')
                  end]
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R match n₁0 with
                  | 0 => n₁
                  | succn n' => succn (fix_half_1 n')
                  end match n₂0 with
                      | 0 => n₂
                      | succn n' => succn (fix_half_2 n')
                      end)
       with
       | nat_R_O_R => n_R
       | @nat_R_S_R n'₁ n'₂ n'_R => nat_R_S_R (half_R n'₁ n'₂ n'_R)
       end (fix_uphalf_2 n₂) (gen_path n₂)) (fix_uphalf_1 n₁) (gen_path n₁)
for half_R.

(** seq *)

(* Here we must make the implicit argument in size explicit *)
Parametricity size.

Definition nilp' T (s : seq T) := eqn (size s) 0.
Parametricity nilp'.
Realizer nilp as nilp_R := nilp'_R.

Parametricity ohead.
Parametricity head.
Parametricity behead.
Parametricity ncons.
Parametricity nseq.
Parametricity cat.
Parametricity rcons.
Parametricity last.
Parametricity belast.
Definition nth_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (x0₁ : T₁) (x0₂ : T₂),
       T_R x0₁ x0₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ ->
       forall n₁ n₂ : nat, nat_R n₁ n₂ -> T_R (nth x0₁ s₁ n₁) (nth x0₂ s₂ n₂)
 :=
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (x0₁ : T₁) (x0₂ : T₂) (x0_R : T_R x0₁ x0₂) =>
let fix_nth_1 :=
  fix nth (s : seq T₁) (n : nat) {struct n} : T₁ :=
    match s with
    | [::] => x0₁
    | x :: s' => match n with
                 | 0 => x
                 | succn n' => nth s' n'
                 end
    end in
let fix_nth_2 :=
  fix nth (s : seq T₂) (n : nat) {struct n} : T₂ :=
    match s with
    | [::] => x0₂
    | x :: s' => match n with
                 | 0 => x
                 | succn n' => nth s' n'
                 end
    end in
fix
nth_R (s₁ : seq T₁) (s₂ : seq T₂) (s_R : list_R T_R s₁ s₂) (n₁ n₂ : nat)
      (n_R : nat_R n₁ n₂) {struct n_R} : T_R (fix_nth_1 s₁ n₁) (fix_nth_2 s₂ n₂) :=
  match s_R in (list_R _ s₁0 s₂0) return (T_R (fix_nth_1 s₁0 n₁) (fix_nth_2 s₂0 n₂)) with
  | @list_R_nil_R _ _ _ =>
      let gen_path :
        forall (T : Type) (x0 : T),
        let
          fix nth (s : seq T) (n : nat) {struct n} : T :=
            match s with
            | [::] => x0
            | x :: s' => match n with
                         | 0 => x
                         | succn n' => nth s' n'
                         end
            end in
        forall n : nat, x0 = nth [::] n :=
        fun (T : Type) (x0 : T) =>
        let
          fix nth (s : seq T) (n : nat) {struct n} : T :=
            match s with
            | [::] => x0
            | x :: s' => match n with
                         | 0 => x
                         | succn n' => nth s' n'
                         end
            end in
        fun n : nat =>
        match n as n0 return (x0 = nth [::] n0) with
        | 0 => erefl (nth [::] 0)
        | succn n0 => erefl (nth [::] (succn n0))
        end in
      eq_rect x0₁ (T_R^~ (fix_nth_2 [::] n₂))
        (eq_rect x0₂ [eta T_R x0₁] x0_R (fix_nth_2 [::] n₂) (gen_path T₂ x0₂ n₂))
        (fix_nth_1 [::] n₁) (gen_path T₁ x0₁ n₁)
  | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
      match
        n_R in (nat_R n₁0 n₂0)
        return (T_R (fix_nth_1 (x₁ :: s'₁) n₁0) (fix_nth_2 (x₂ :: s'₂) n₂0))
      with
      | nat_R_O_R => x_R
      | @nat_R_S_R n'₁ n'₂ n'_R => nth_R s'₁ s'₂ s'_R n'₁ n'₂ n'_R
      end
  end.
Definition set_nth_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (x0₁ : T₁) (x0₂ : T₂),
       T_R x0₁ x0₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ ->
       forall n₁ n₂ : nat,
       nat_R n₁ n₂ ->
       forall (y₁ : T₁) (y₂ : T₂),
       T_R y₁ y₂ -> list_R T_R (set_nth x0₁ s₁ n₁ y₁) (set_nth x0₂ s₂ n₂ y₂)
 := 
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (x0₁ : T₁) (x0₂ : T₂) (x0_R : T_R x0₁ x0₂) =>
let fix_set_nth_1 :=
  fix set_nth (s : seq T₁) (n : nat) (y : T₁) {struct n} : seq T₁ :=
    match s with
    | [::] => ncons n x0₁ [:: y]
    | x :: s' => match n with
                 | 0 => y :: s'
                 | succn n' => x :: set_nth s' n' y
                 end
    end in
let fix_set_nth_2 :=
  fix set_nth (s : seq T₂) (n : nat) (y : T₂) {struct n} : seq T₂ :=
    match s with
    | [::] => ncons n x0₂ [:: y]
    | x :: s' => match n with
                 | 0 => y :: s'
                 | succn n' => x :: set_nth s' n' y
                 end
    end in
fix
set_nth_R (s₁ : seq T₁) (s₂ : seq T₂) (s_R : list_R T_R s₁ s₂) 
          (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (y₁ : T₁) (y₂ : T₂) 
          (y_R : T_R y₁ y₂) {struct n_R} :
  list_R T_R (fix_set_nth_1 s₁ n₁ y₁) (fix_set_nth_2 s₂ n₂ y₂) :=
  match
    s_R in (list_R _ s₁0 s₂0)
    return (list_R T_R (fix_set_nth_1 s₁0 n₁ y₁) (fix_set_nth_2 s₂0 n₂ y₂))
  with
  | @list_R_nil_R _ _ _ =>
      let gen_path :
        forall (T : Type) (x0 : T),
        let
          fix set_nth (s : seq T) (n : nat) (y : T) {struct n} : 
          seq T :=
            match s with
            | [::] => ncons n x0 [:: y]
            | x :: s' => match n with
                         | 0 => y :: s'
                         | succn n' => x :: set_nth s' n' y
                         end
            end in
        forall (n : nat) (y : T), ncons n x0 [:: y] = set_nth [::] n y :=
        fun (T : Type) (x0 : T) =>
        let
          fix set_nth (s : seq T) (n : nat) (y : T) {struct n} : 
          seq T :=
            match s with
            | [::] => ncons n x0 [:: y]
            | x :: s' => match n with
                         | 0 => y :: s'
                         | succn n' => x :: set_nth s' n' y
                         end
            end in
        fun (n : nat) (y : T) =>
        match n as n0 return (ncons n0 x0 [:: y] = set_nth [::] n0 y) with
        | 0 => erefl (set_nth [::] 0 y)
        | succn n0 => erefl (set_nth [::] (succn n0) y)
        end in
      eq_rect (ncons n₁ x0₁ [:: y₁]) ((list_R T_R)^~ (fix_set_nth_2 [::] n₂ y₂))
        (eq_rect (ncons n₂ x0₂ [:: y₂]) [eta list_R T_R (ncons n₁ x0₁ [:: y₁])]
           (ncons_R n_R x0_R (list_R_cons_R y_R (list_R_nil_R T_R)))
           (fix_set_nth_2 [::] n₂ y₂) (gen_path T₂ x0₂ n₂ y₂)) 
        (fix_set_nth_1 [::] n₁ y₁) (gen_path T₁ x0₁ n₁ y₁)
  | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
      match
        n_R in (nat_R n₁0 n₂0)
        return
          (list_R T_R (fix_set_nth_1 (x₁ :: s'₁) n₁0 y₁) (fix_set_nth_2 (x₂ :: s'₂) n₂0 y₂))
      with
      | nat_R_O_R => list_R_cons_R y_R s'_R
      | @nat_R_S_R n'₁ n'₂ n'_R =>
          list_R_cons_R x_R (set_nth_R s'₁ s'₂ s'_R n'₁ n'₂ n'_R y₁ y₂ y_R)
      end
  end.
Parametricity find.
Parametricity filter.
Parametricity count.
Parametricity has.
Parametricity all.
Definition drop_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (n₁ n₂ : nat),
       nat_R n₁ n₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ -> list_R T_R (drop n₁ s₁) (drop n₂ s₂)
 :=
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) =>
let fix_drop_1 :=
  fix drop (n : nat) (s : seq T₁) {struct s} : seq T₁ :=
    match s with
    | [::] => s
    | _ :: s' => match n with
                 | 0 => s
                 | succn n' => drop n' s'
                 end
    end in
let fix_drop_2 :=
  fix drop (n : nat) (s : seq T₂) {struct s} : seq T₂ :=
    match s with
    | [::] => s
    | _ :: s' => match n with
                 | 0 => s
                 | succn n' => drop n' s'
                 end
    end in
fix
drop_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) (s₁ : seq T₁) (s₂ : seq T₂)
       (s_R : list_R T_R s₁ s₂) {struct s_R} :
  list_R T_R (fix_drop_1 n₁ s₁) (fix_drop_2 n₂ s₂) :=
  let gen_path :
    forall T : Type,
    let
      fix drop (n : nat) (s : seq T) {struct s} : seq T :=
        match s with
        | [::] => s
        | _ :: s' => match n with
                     | 0 => s
                     | succn n' => drop n' s'
                     end
        end in
    forall (n : nat) (s : seq T),
    match s with
    | [::] => s
    | _ :: s' => match n with
                 | 0 => s
                 | succn n' => drop n' s'
                 end
    end = drop n s :=
    fun T : Type =>
    let
      fix drop (n : nat) (s : seq T) {struct s} : seq T :=
        match s with
        | [::] => s
        | _ :: s' => match n with
                     | 0 => s
                     | succn n' => drop n' s'
                     end
        end in
    fun (n : nat) (s : seq T) =>
    match
      s as l
      return
        (match l with
         | [::] => l
         | _ :: s' => match n with
                      | 0 => l
                      | succn n' => drop n' s'
                      end
         end = drop n l)
    with
    | [::] => erefl (drop n [::])
    | t :: s0 => erefl (drop n (t :: s0))
    end in
  eq_rect
    match s₁ with
    | [::] => s₁
    | _ :: s' => match n₁ with
                 | 0 => s₁
                 | succn n' => fix_drop_1 n' s'
                 end
    end ((list_R T_R)^~ (fix_drop_2 n₂ s₂))
    (eq_rect
       match s₂ with
       | [::] => s₂
       | _ :: s' => match n₂ with
                    | 0 => s₂
                    | succn n' => fix_drop_2 n' s'
                    end
       end
       [eta list_R T_R
              match s₁ with
              | [::] => s₁
              | _ :: s' => match n₁ with
                           | 0 => s₁
                           | succn n' => fix_drop_1 n' s'
                           end
              end]
       match
         s_R in (list_R _ s₁0 s₂0)
         return
           (list_R T_R
              match s₁0 with
              | [::] => s₁
              | _ :: s' => match n₁ with
                           | 0 => s₁
                           | succn n' => fix_drop_1 n' s'
                           end
              end
              match s₂0 with
              | [::] => s₂
              | _ :: s' => match n₂ with
                           | 0 => s₂
                           | succn n' => fix_drop_2 n' s'
                           end
              end)
       with
       | @list_R_nil_R _ _ _ => s_R
       | @list_R_cons_R _ _ _ _ _ _ s'₁ s'₂ s'_R =>
           match
             n_R in (nat_R n₁0 n₂0)
             return
               (list_R T_R match n₁0 with
                           | 0 => s₁
                           | succn n' => fix_drop_1 n' s'₁
                           end match n₂0 with
                               | 0 => s₂
                               | succn n' => fix_drop_2 n' s'₂
                               end)
           with
           | nat_R_O_R => s_R
           | @nat_R_S_R n'₁ n'₂ n'_R => drop_R n'₁ n'₂ n'_R s'₁ s'₂ s'_R
           end
       end (fix_drop_2 n₂ s₂) (gen_path T₂ n₂ s₂)) (fix_drop_1 n₁ s₁) 
    (gen_path T₁ n₁ s₁).
Parametricity take.
Definition rot_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (n₁ n₂ : nat),
       nat_R n₁ n₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ -> list_R T_R (rot n₁ s₁) (rot n₂ s₂)
 := 
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
  (s₁ : seq T₁) (s₂ : seq T₂) (s_R : list_R T_R s₁ s₂) =>
cat_R (drop_R n_R s_R) (take_R n_R s_R).
Definition rotr_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (n₁ n₂ : nat),
       nat_R n₁ n₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ -> list_R T_R (rotr n₁ s₁) (rotr n₂ s₂)
 := 
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) 
  (s₁ : seq T₁) (s₂ : seq T₂) (s_R : list_R T_R s₁ s₂) =>
rot_R (subn_R (size_R s_R) n_R) s_R.
Parametricity catrev.
Parametricity rev.
Parametricity map.
Parametricity pmap.
Parametricity iota.
Parametricity mkseq.
Parametricity foldr.
Parametricity sumn.
Parametricity foldl.
Parametricity pairmap.
Parametricity scanl.
Definition zip_R     : forall (S₁ S₂ : Type) (S_R : S₁ -> S₂ -> Type) (T₁ T₂ : Type)
         (T_R : T₁ -> T₂ -> Type) (s₁ : seq S₁) (s₂ : seq S₂),
       list_R S_R s₁ s₂ ->
       forall (t₁ : seq T₁) (t₂ : seq T₂),
       list_R T_R t₁ t₂ -> list_R (prod_R S_R T_R) (zip s₁ t₁) (zip s₂ t₂)
 := 
fun (S₁ S₂ : Type) (S_R : S₁ -> S₂ -> Type) (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) =>
let fix_zip_1 :=
  fix zip (s : seq S₁) (t : seq T₁) {struct t} : seq (S₁ * T₁) :=
    match s with
    | [::] => [::]
    | x :: s' => match t with
                 | [::] => [::]
                 | y :: t' => (x, y) :: zip s' t'
                 end
    end in
let fix_zip_2 :=
  fix zip (s : seq S₂) (t : seq T₂) {struct t} : seq (S₂ * T₂) :=
    match s with
    | [::] => [::]
    | x :: s' => match t with
                 | [::] => [::]
                 | y :: t' => (x, y) :: zip s' t'
                 end
    end in
fix
zip_R (s₁ : seq S₁) (s₂ : seq S₂) (s_R : list_R S_R s₁ s₂) (t₁ : seq T₁) 
      (t₂ : seq T₂) (t_R : list_R T_R t₁ t₂) {struct t_R} :
  list_R (prod_R S_R T_R) (fix_zip_1 s₁ t₁) (fix_zip_2 s₂ t₂) :=
  match
    s_R in (list_R _ s₁0 s₂0)
    return (list_R (prod_R S_R T_R) (fix_zip_1 s₁0 t₁) (fix_zip_2 s₂0 t₂))
  with
  | @list_R_nil_R _ _ _ =>
      let gen_path :
        forall S T : Type,
        let
          fix zip (s : seq S) (t : seq T) {struct t} : seq (S * T) :=
            match s with
            | [::] => [::]
            | x :: s' => match t with
                         | [::] => [::]
                         | y :: t' => (x, y) :: zip s' t'
                         end
            end in
        forall t : seq T, [::] = zip [::] t :=
        fun S T : Type =>
        let
          fix zip (s : seq S) (t : seq T) {struct t} : seq (S * T) :=
            match s with
            | [::] => [::]
            | x :: s' => match t with
                         | [::] => [::]
                         | y :: t' => (x, y) :: zip s' t'
                         end
            end in
        fun t : seq T =>
        match t as l return ([::] = zip [::] l) with
        | [::] => erefl (zip [::] [::])
        | t0 :: t1 => erefl (zip [::] (t0 :: t1))
        end in
      eq_rect [::] ((list_R (prod_R S_R T_R))^~ (fix_zip_2 [::] t₂))
        (eq_rect [::] [eta list_R (prod_R S_R T_R) [::]] (list_R_nil_R (prod_R S_R T_R))
           (fix_zip_2 [::] t₂) (gen_path S₂ T₂ t₂)) (fix_zip_1 [::] t₁) 
        (gen_path S₁ T₁ t₁)
  | @list_R_cons_R _ _ _ x₁ x₂ x_R s'₁ s'₂ s'_R =>
      match
        t_R in (list_R _ t₁0 t₂0)
        return
          (list_R (prod_R S_R T_R) (fix_zip_1 (x₁ :: s'₁) t₁0) (fix_zip_2 (x₂ :: s'₂) t₂0))
      with
      | @list_R_nil_R _ _ _ => list_R_nil_R (prod_R S_R T_R)
      | @list_R_cons_R _ _ _ y₁ y₂ y_R t'₁ t'₂ t'_R =>
          list_R_cons_R (prod_R_pair_R x_R y_R) (zip_R s'₁ s'₂ s'_R t'₁ t'₂ t'_R)
      end
  end.
Parametricity unzip1.
Parametricity unzip2.
Parametricity flatten.
Parametricity shape.
Definition reshape_R     : forall (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) (sh₁ sh₂ : seq nat),
       list_R nat_R sh₁ sh₂ ->
       forall (s₁ : seq T₁) (s₂ : seq T₂),
       list_R T_R s₁ s₂ -> list_R (list_R T_R) (reshape sh₁ s₁) (reshape sh₂ s₂)
 := 
fun (T₁ T₂ : Type) (T_R : T₁ -> T₂ -> Type) =>
let fix_reshape_1 :=
  fix reshape (sh : seq nat) (s : seq T₁) {struct sh} : seq (seq T₁) :=
    match sh with
    | [::] => [::]
    | n :: sh' => take n s :: reshape sh' (drop n s)
    end in
let fix_reshape_2 :=
  fix reshape (sh : seq nat) (s : seq T₂) {struct sh} : seq (seq T₂) :=
    match sh with
    | [::] => [::]
    | n :: sh' => take n s :: reshape sh' (drop n s)
    end in
fix
reshape_R (sh₁ sh₂ : seq nat) (sh_R : list_R nat_R sh₁ sh₂) (s₁ : seq T₁) 
          (s₂ : seq T₂) (s_R : list_R T_R s₁ s₂) {struct sh_R} :
  list_R (list_R T_R) (fix_reshape_1 sh₁ s₁) (fix_reshape_2 sh₂ s₂) :=
  match
    sh_R in (list_R _ sh₁0 sh₂0)
    return (list_R (list_R T_R) (fix_reshape_1 sh₁0 s₁) (fix_reshape_2 sh₂0 s₂))
  with
  | @list_R_nil_R _ _ _ => list_R_nil_R (list_R T_R)
  | @list_R_cons_R _ _ _ n₁ n₂ n_R sh'₁ sh'₂ sh'_R =>
      list_R_cons_R (take_R n_R s_R)
        (reshape_R sh'₁ sh'₂ sh'_R (drop n₁ s₁) (drop n₂ s₂) (drop_R n_R s_R))
  end.
Parametricity allpairs.

(* fintype *)

Parametricity ordinal.
