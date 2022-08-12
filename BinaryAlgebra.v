Require Import Coq.Init.Peano.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.


Require Import List.
Import ListNotations.
Check [1].


Inductive bit : Set :=
  | I : bit
  | O : bit.


Definition binary := list bit.

Fixpoint bit_inc (bs : binary) : binary :=
  match bs with
    | []       => [I]
    | I :: bs' => O :: bit_inc bs'
    | O :: bs' => I :: bs'
    end.

Fixpoint bin_add (b1 b2 : binary) : binary :=
  match b1,b2 with
    | I :: b1', b :: b2' => bit_inc (b :: bin_add b1' b2')
    | O :: b1', b :: b2' => b :: bin_add b1' b2'
    | [],_               => b2
    | _,[]               => b1
    end.


Notation "x +.+ y" := (bin_add x y) (at level 40, left associativity).


Fixpoint bin_to_nat (b : binary) : nat :=
  match b with
    | I :: b' => S (2 * bin_to_nat b')
    | O :: b' => (2 * bin_to_nat b')
    | []      => 0
    end.

Fixpoint nat_to_bin (n : nat) : binary :=
  match n with
    | 0    => []
    | S n' => bit_inc (nat_to_bin n')
    end.


Definition bin_eq (a b : binary) := bin_to_nat a = bin_to_nat b.

Notation "x ~= y" := (bin_eq x y) (at level 40,left associativity).


Lemma corollary_1 : forall (a b : binary), a ~= b -> bin_to_nat a = bin_to_nat b.
Proof.
  unfold bin_eq. intros. auto.
Qed.

Lemma corollary_2 : forall (a b : binary), bin_to_nat a = bin_to_nat b -> a ~= b.
Proof.
  unfold bin_eq. intros. auto.
Qed.

Theorem nat_bin_succ : forall (n : nat), nat_to_bin (S n) ~= bit_inc (nat_to_bin n) .
Proof.
  unfold bin_eq. intros n. simpl. reflexivity.
Qed.

Theorem bin_nat_succ : forall (b : binary), bin_to_nat (bit_inc b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b.
  - simpl. reflexivity.
  - destruct a. all: simpl. rewrite IHb. simpl. auto. reflexivity. 
Qed.


Theorem nat_to_bin_to_nat_eq : forall (n : nat), bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - rewrite (nat_bin_succ n). rewrite (bin_nat_succ (nat_to_bin n)). rewrite IHn. reflexivity.
Qed.

Theorem bin_to_nat_to_bin_eq : forall (b : binary), nat_to_bin (bin_to_nat b) ~= b.
Proof.
  unfold bin_eq.
  intros.
  destruct (bin_to_nat b).
  - simpl. reflexivity.
  - rewrite (nat_to_bin_to_nat_eq (S n)). reflexivity.
Qed.


Theorem equality_equivelence_1 : forall (n m : nat), n = m -> nat_to_bin n ~= nat_to_bin m.
Proof.
  unfold bin_eq. intros. rewrite H. reflexivity.
Qed.

Theorem equality_equivelence_2 : forall (n m : nat), nat_to_bin n ~= nat_to_bin m -> n = m.
Proof.
  unfold bin_eq.
  intros n m.
  rewrite (nat_to_bin_to_nat_eq n).
  rewrite (nat_to_bin_to_nat_eq m).
  auto.
Qed.

Theorem equality_equivelence_3 : forall (n m : nat), n = m -> nat_to_bin n = nat_to_bin m.
Proof. 
  intros. rewrite H. reflexivity.
Qed.




Lemma bin_add_identity : forall (b : binary), (nat_to_bin 0) +.+ b = b.
Proof.
  induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma bin_add_left_identity : forall (b : binary), [] +.+ b = b.
Proof.
  intros.
  simpl. reflexivity.
Qed. 


Lemma bin_add_succ_1 : forall (b : binary), [I] +.+ b = bit_inc b.
Proof.
  induction b.
  simpl. reflexivity.
  destruct a.
  all: simpl; reflexivity.
Qed.


Compute (nat_to_bin 11) +.+ (nat_to_bin 1).
Compute (nat_to_bin 1) +.+ (nat_to_bin 11).


Definition bin_add' (b1 b2 : binary) : binary := nat_to_bin (bin_to_nat b1 + bin_to_nat b2).

Notation "x *.* y" := (bin_add' x y) (at level 40, left associativity).


Theorem nat_to_bin_add_hom : forall (n m : nat), nat_to_bin (n + m) = ((nat_to_bin n) *.* (nat_to_bin m)).
Proof.
  unfold bin_add'.
  intros.
  rewrite (nat_to_bin_to_nat_eq m). rewrite (nat_to_bin_to_nat_eq n). reflexivity.
Qed.


Theorem bin_to_nat_add_hom : forall (a b : binary), bin_to_nat (a *.* b) = bin_to_nat a + bin_to_nat b.
Proof.
  unfold bin_add'.
  intros.
  rewrite (nat_to_bin_to_nat_eq (bin_to_nat a + bin_to_nat b)).
  reflexivity.
Qed.



Theorem bits_to_nat_bits_inc :
  forall b, bin_to_nat (bit_inc b) = S (bin_to_nat b).
Proof.
  induction b as [|b bs ih].
  - reflexivity.
  - destruct b; simpl.
    + rewrite ih.
      Search (_ + 0).
      rewrite <-2 plus_n_O.
      Search (_ + S _).
      rewrite <- plus_n_Sm.
      reflexivity.
    + reflexivity.
Qed.


