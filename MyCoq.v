
(** * Introduction *)


(** printing  *token* %...LATEX...% #...html...# *)

Module NatDef.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint add (a b : nat) : nat :=
  match a with
    | O => b
    | (S a') => S (add a' b)
  end.

End NatDef.

Theorem add_0_n : forall (n : nat), 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem add_n_0 : forall (n : nat), n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma add_n_S_m : forall (n : nat) (m : nat), n + S m = S (n + m).
Proof.
  induction n.
  - intros m. simpl. reflexivity.
  - intros m. simpl. destruct (IHn m). (* rewrite IHn. *) reflexivity.
Qed.

Theorem add_comm : forall (n : nat) (m : nat), n + m = m + n.
Proof.
  induction n.
  - intros m. simpl. rewrite add_n_0. reflexivity.
  - intros m. simpl. rewrite IHn. rewrite add_n_S_m. reflexivity.
Qed.

Theorem add_assoc : forall (k n m : nat), k + (n + m) = (k + n) + m.
intros.
Proof.
  induction k.
   - simpl. reflexivity.
   - simpl. rewrite IHk. reflexivity.
Qed.


Print eq_refl.

Check eq_refl : 1 = 1.

Inductive equality (A : Type) : A -> A -> Type :=
  | refl : forall (x : A), equality A x x.

Arguments refl {A}.

Check refl 1 : equality nat 1 1.

Check Type @{ Set + 0 }.


(* Module BoolPlay. *)

Inductive boolean : Set :=
  | true
  | false.

Definition negb (b : boolean) :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 b2 : boolean) : boolean :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 b2 : boolean) : boolean :=
  match b1 with
    | true => true
    | false => b2
  end.
Notation "x && y" := (andb x y) (at level 40, left associativity) .
Notation "x || y" := (orb x y) (at level 50, left associativity) .


Theorem demorgan_and : forall (a b : boolean), negb(a && b) = (negb a) || (negb b).
Proof.
  intros a.
  destruct a.
  - intros b. simpl. reflexivity.
  - intros b. simpl. reflexivity.
Qed.
Theorem demorgan_or : forall (a b : boolean), negb (a || b) = (negb a) && (negb b).
Proof.
  intros a.
  destruct a.
  - intros b. simpl. reflexivity.
  - intros b. simpl. reflexivity.
Qed.

Theorem excluded_middle : forall (b : boolean), b || (negb b) = true.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.


Definition predicate_on (A : Type) := A -> boolean.
Definition subset {U : Type} (P Q : predicate_on U) : Prop := 
  forall x, (P x = true) -> (Q x = true). 

Definition whole {A : Type} : A -> boolean := fun _ => true.

Fixpoint even (n : nat) : boolean :=
  match n with
  | 0 => true 
  | (S m) => (negb (even m))
  end.

Theorem nat_even_subset : subset even whole.
Proof.
  unfold subset.
  induction x.
  - simpl. intros. unfold whole. reflexivity.
  - intros. unfold whole. reflexivity. 
Qed.

Definition odd := fun n => negb (even n).

Theorem nat_odd_subset : subset odd whole.
Proof.
  unfold subset.
  intros x.
  unfold odd.
  intros.
  unfold whole.
  reflexivity.
Qed.

Definition union_of {U : Type} (R P Q : predicate_on U) : Prop :=
  forall (x : U), P x || Q x = true -> R x = true.

Definition intersection_of {U : Type} (R P Q : predicate_on U) : Prop :=
  forall (x : U), (negb (P x && Q x)) || R x = true.

Definition pred_comp_union {U : Type} (P Q : predicate_on U) : Prop := 
  forall (x : U), P x = true \/ Q x = true.

Definition pred_comp_indersection {U : Type} (P Q : predicate_on U) : predicate_on U :=
  fun x => P x && Q x.


Definition pred_equal {U : Type} (P Q : U -> Prop) : Prop := 
  forall (x : U), P x <-> Q x.

Definition pred_implies {U : Type} (P Q : U -> Prop) : Prop := 
  forall (x : U), P x -> Q x.
  
Definition subset_equals {U : Type} (P Q : U -> Prop) : Prop :=
  pred_equal P Q.


Definition sem {U : Type} (P : predicate_on U) : U -> Prop :=
  fun x => P x = true.

Notation "x =*= y" := (subset_equals x y) (at level 50, left associativity).
Notation "x <* y" := (subset x y) (at level 50, left associativity).
Notation "x [.] y" := (pred_comp_union x y) (at level 50, left associativity).
Notation "x [^] y" := (pred_comp_indersection x y) (at level 50, left associativity).
Notation "[[ x ]]" := (sem x).

Definition null {A : Type} : A -> boolean := fun _ => false.
Notation "{/}" := null.

(* Notation "x [.] y" := (fun z => union_of z x y = true) (at level 50, left associativity).
Notation "x [!] y *= z" := (intersection_of z x y = true) (at level 50, left associativity). *)


Theorem nat_evens_odds_disjoint : forall (x : nat), [[ even [^] odd ]] x <-> [[ {/} ]] x.
Proof.
  unfold subset_equals.
  unfold sem.
  unfold pred_equal.
  unfold pred_comp_indersection.
  unfold null.
  intros x.
  simpl.
  induction x.
  - simpl. unfold odd. simpl. split. intros. assumption. intros. assumption.
  - simpl. unfold odd. simpl. rewrite <- demorgan_or. rewrite excluded_middle. simpl. split. intros. assumption. intros. assumption. 
Qed.


(*
[[ P ]] x   <-> P x = true
~ [[ P ]] x <-> P x = false

*)



Lemma pred_boolean_negation_false_1 : forall {U : Type} (P : predicate_on U), 
  forall (x : U), P x = false -> negb (P x) = true.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma boolean_negation_em : forall (b : boolean), negb b = false <-> b = true.
Proof.
  intros.
  split.
  destruct b.
  intros. reflexivity. intros. rewrite <- H. reflexivity.
  destruct b.
  simpl. auto.
  simpl. auto.
Qed.

Lemma pred_boolean_negation_false_2 : forall {U : Type} (P : predicate_on U), 
  forall (x : U), negb (P x) = false -> P x = true.
Proof.
  intros.
  apply boolean_negation_em in H.
  assumption.
Qed.

Lemma double_negation : forall (b : boolean), negb (negb b) = b.
Proof.
  intros.
  destruct b.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma pred_boolean_negation_true_2 : forall {U : Type} (P : predicate_on U), 
  forall (x : U), negb (P x) = true -> P x = false.
Proof.
  intros U P x.
  intros H.
  apply boolean_negation_em in H as H1.
  rewrite <- H1.
  rewrite double_negation.
  reflexivity.
Qed.

Lemma pred_boolean_excluded_middle : forall {U : Type} (P : predicate_on U), 
  forall (b : boolean) (x : U), P x = b <-> negb (P x) = negb b.
Proof.
  intros U P b.
  
  intros x.
  destruct b.
  - simpl. split. intros. rewrite H. simpl. reflexivity. apply pred_boolean_negation_false_2.
  - simpl. split. apply pred_boolean_negation_false_1. destruct (boolean_negation_em (P x)). apply pred_boolean_negation_true_2.
Qed.

Lemma sem_truth_base_true : forall {U : Type} (P : predicate_on U), 
  forall (x : U), [[ P ]] x <-> P x = true.
Proof.
  intros.
  unfold sem.
  destruct (P x).
  tauto.
  tauto.
Qed.

Lemma sem_truth_base_false : forall {U : Type} (P : predicate_on U), 
  forall (x : U), ~ [[ P ]] x <-> P x = false.
Proof.
  intros.
  split.
  unfold sem.
  intros.
  destruct (P x).
  tauto.
  reflexivity.
  simpl.
  intros.
  unfold sem.
  rewrite H.
  discriminate.
Qed.




Axiom boolean_eq_1 : forall (a b : boolean), a = b <-> ~ (a <> b).
Axiom boolean_eq_2 : false <> true.


Lemma sem_truth_excluded_middle_1 : forall {U : Type} (P : predicate_on U), 
  forall (x : U), [[ P ]] x \/ ~ [[ P ]] x.
Proof.
  intros.
  unfold sem.
  destruct (P x).
  - left. reflexivity.
  - right. discriminate.
Qed.

Lemma sem_truth_excluded_middle_2 : forall {U : Type} (P : predicate_on U), 
  forall (x : U), [[ P ]] x <-> ~ ~ [[ P ]] x.
Proof.
  intros.
  unfold sem.
  split.
  destruct (P x).
  - intros. tauto.
  - intros. rewrite H. tauto.
  - simpl. intros. apply boolean_eq_1. assumption.
Qed.


  

(* 

Module Bbox.

Inductive bbox : nat -> nat -> Type :=
  | box : bbox 1 1
  | hor : forall {n m i j : nat}, bbox n m -> bbox i j -> bbox (n + i) (max m j)
  | ver : forall {n m i j : nat}, bbox n m -> bbox i j -> bbox (max n i) (m + j).

Theorem t : forall (x1 x2 y1 y2 : nat) (a : bbox x1 y1) (b : bbox x2 y2),.
Proof.

End Bbox.

Module MySets.

(* Require Coq.Logic.ClassicalChoice. *)

Definition subset {U : Type} (P Q : U -> Prop) : Prop := forall x, P x -> Q x.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
  with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

    Hint Constructors even: arith.
Hint Constructors odd: arith.

Check even.


Inductive whole {A : Type} : A -> Prop := whole_id : forall (x : A), whole x.

Definition predicate_on (A : Type) := A -> Prop.

Check even : predicate_on nat.
Check whole : predicate_on nat.

Example even_nats_subset : subset even whole.
Proof.
  unfold subset.
  intros.
  destruct x.
  - apply whole_id.
  - apply whole_id.
Qed.

Inductive multiples_of (n : nat) : nat -> Prop := 
  | mult_O : multiples_of n 0
  | mult_S : forall (k : nat), multiples_of n k -> multiples_of n (n + k).


Definition multiple_of (n m : nat) := exists (k : nat), n = k * m.

Compute (even 1).

(* Arguments mult_O {n}.
Arguments mult_S {n}. *)

(* Lemma multiple_comm : forall (n k : nat), 
  multiple_of n k <-> exists (m : nat), n * m = k.
Proof. admitted. Qed. *)


(* Lemma odd_succ_even : forall (n : nat), even (S n) -> n = n. *)



(* Fixpoint nat_even (n : nat) : Prop :=
  match even n with
    | even_O => even_O
    | even_S _ _ => even n 
    | odd_S _ _  => not (even n)
  end. *)


Axiom nat_odd_not_even : forall (n : nat), odd n -> not (even n).
Axiom nat_even_not_odd : forall (n : nat), even n -> not (odd n).
Theorem nat_even_or_odd : forall (n : nat), even n \/ odd n.
Proof.
  induction n.
  - left. apply even_O.
  - destruct IHn as [IHne | IHno]. 
    right. apply odd_S in IHne. assumption.
    left. apply even_S in IHno. assumption.
Qed.


Theorem nat_even_decomp : forall (n : nat), even n -> exists (m : nat), m * 2 = n.
Proof.
  induction n.
  - exists 0. reflexivity.
  - simpl. inversion H. apply nat_odd_not_even in H1. exists 0.

(* Theorem nat_odd_not_even : forall (n : nat), nat_even n -> odd (S n).
Proof.
  intros.
  destruct (nat_even_odd_exclude n).
  apply odd_S.
  destruct n.
  - simpl. 
  induction n.
  - intros. apply odd_S. apply even_O.
  - . intros. simpl .
  simpl.
  induction n.
  - intros. simpl. inversion H. 
  - apply nat_even_odd_exclude. simpl. intros.  inversion H. simpl. unfold nat_even. simpl. destruct H as H1.  *)



Lemma multiple_even : forall (n : nat), even n ->
  forall (m : nat), multiple_of n m -> even m.
Proof.
  unfold multiple_of.
  intros.

Lemma not_even_and_odd : forall n, even n -> odd n -> False.
Proof.
  induction n.
    intros even_0 odd_0. inversion odd_0.
    intros even_Sn odd_Sn. inversion even_Sn. inversion odd_Sn. auto with arith.
Qed.

(* Definition q_false : forall (p q : Prop), (p -> q)  *)



Example multiples_10_even : subset (multiples_of 10) even.
Proof.
  unfold subset.
  intros.
  auto.
  induction x.
  - apply even_O.
  - auto.






End MySets.


(* 
Inductive monoid (M : Set) (op : (M -> M -> M)) (e : M) : Type :=
  | M_Ax :
    (forall (m : M), op e m = m) ->
    (forall (m : M), op m e = m) ->
    (forall (a b c : M), op a (op b c) = op (op a b) c) ->
    monoid M op e.
Arguments M_Ax {M} {op} {e}.

Definition add_monoid : monoid nat Nat.add 0 :=
  M_Ax add_0_n add_n_0 add_assoc.


Theorem monoid_id_eq : 
  forall (M : Set) (op : (M -> M -> M)) (e : M) (Mon : monoid M op e),
    forall (m : M), op m e = op e m.
Proof.
  intros.
  destruct Mon.
  rewrite e0.
  rewrite e1.
  reflexivity.
Qed.

Theorem monoid_cancelation :
  forall {M : Set} {op} {e} (Mon : monoid M op e),
    forall (a b c : M), 
      op a b = op a c -> b = c.
Proof.
  intros. 
  destruct Mon.



Inductive comm_monoid (M : Set) (op : (M -> M -> M)) (e : M) : Type :=
  | CM : 
    monoid M op e -> 
    (forall (a b : M), op a b = op b a) -> 
    comm_monoid M op e. *)




 *)
