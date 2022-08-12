Require Import Coq.Init.Peano.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.


Require Import List.
Import ListNotations.
Check [1].

From Coq Require Vector.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Definition vector : Type -> nat -> Type := t.

Inductive bit : Set :=
  | I : bit
  | O : bit.

  
Definition binary := list bit.

Definition block (n : nat) : Type := vector bit n.

Fixpoint block_to_nat {n : nat} (b : block n) : nat :=
  match b with
    | []      => 0
    | I :: bs => S (2 * block_to_nat bs)
    | O :: bs => 2 * block_to_nat bs
    end.

Definition min_size (n : nat) : nat := (log2 n) + 1.




Fixpoint block_succ {n : nat} (b : block n) : block n :=
  match b with
    | []      => [] 
    | O :: bs => I :: bs
    | I :: bs => O :: block_succ bs
    end.

Compute block_succ [I;I;I].

Fixpoint cons_n_block (n : nat) : block n :=
  match n with
    | 0    => []
    | S n' => O :: (cons_n_block n')
    end.

Fixpoint n_succ_block {n : nat} (k : nat) (b : block n) : block n :=
  match k with
    | 0    => b
    | S k' => block_succ (n_succ_block k' b)
    end.

Definition nat_to_block (n : nat) : block (min_size n) := 
  n_succ_block n (cons_n_block (min_size n)).

Check nat_to_block.

Notation "'⟦' x '⟧'" := (block_to_nat x) (at level 100, format "⟦ x ⟧").
Notation "'⟨' x '⟩'" := (nat_to_block x) (at level 100, format "⟨ x ⟩").

Definition block_addition {n : nat} (b1 b2 : block n) : block n :=
  n_succ_block (block_to_nat b1) b2.

Notation "x <+> y" := (block_addition x y) (at level 100, right associativity).


Lemma block_nat_zero_eq : forall (n : nat), ⟦cons_n_block n⟧ = 0.
Proof.
  intros.
  induction n. simpl. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma block_add_left_identity : forall {n : nat} (b : block n), (cons_n_block n <+> b) = b.
Proof.
  intros.
  induction n.
  simpl. unfold block_addition. unfold block_to_nat. simpl. reflexivity.
  unfold block_addition. rewrite  (block_nat_zero_eq (S n)). simpl. reflexivity. 
Qed.


Lemma nat_block_iso : forall (k : nat) (b : block (min_size k)), b = nat_to_block k <-> block_to_nat b = k.
Proof.
  induction k.
  - intro b. unfold min_size in b. simpl in b. 
    split. 
      intros. rewrite H. simpl. reflexivity.
      intros. simpl. unfold nat_to_block. simpl. auto.
      destruct b.
      unfold block_to_nat in H.
      destruct b.


  intros.
  unfold nat_to_block.
  (* unfold block_to_nat. *)
  induction k. 
  destruct b.
  tauto. simpl. intros. destruct h. simpl. split.
  all: try intros; try tauto; simpl; try auto; simpl. reflexivity.
  unfold block_to_nat. simpl. auto. reflexivity
  split.
  induction k.
  - intros. simpl. induction b.
    simpl. reflexivity.
    rewrite H.
    simpl.
    rewrite <- (block_nat_zero_eq (S n)).
    rewrite -> (block_nat_zero_eq (S n)).
    rewrite (block_nat_zero_eq n).
    reflexivity.
  - intros.
    (* rewrite H. simpl. *)
    (* unfold block_to_nat. *)
    simpl.
    pose proof (IHk (nat_to_block k)) as b2.
    simpl in b2.
    simpl in H.
    unfold block_to_nat. unfold min_size. unfold block_to_nat. simpl.

    pose proof (IHk (nat_to_block k)).
    unfold nat_to_block in H0.
    simpl in H0. 
    pose proof (H0 eq_refl). simpl. auto.
    rewrite <- b2.
    rewrite <- H1.
    simpl. pose proof (block_nat_zero_eq (min_size k)).
    simpl. rewrite <- H2.
    
    
    
    
    unfold block_to_nat.  simpl. 
    simpl. rewrite <- H2.
    unfold block_to_nat.
    simpl. auto.
    destruct b. simpl. reflexivity.
    rewrite -> H1. simpl.

    rewrite H.
    simpl.

    rewrite <- (block_nat_zero_eq k).
    rewrite (block_nat_zero_eq k).
    unfold block_to_nat.

    simpl.

    pose proof (IHk (nat_to_block k)).

    unfold block_to_nat.

  unfold (min_size). cbv. simpl.
  - simpl. intros. rewrite <- H.
    unfold nat_to_block. simpl. destruct b.
  simpl in H.
  unfold block_to_nat in H. simpl in H.

  rewrite -> H.
  all: simpl; intros.
  pose proof (block_add_left_identity )
  unfold block_to_nat in H.
  simpl in H. auto.

  induction b.
  (* unfold nat_to_block. *)

Lemma block_add_left_succ : forall {n : nat} (b1 b2 : block n), (block_succ b1 <+> b2) = block_succ (b1 <+> b2).
Proof.
  intros.
  unfold block_addition.
  induction b1.
  induction b2.
  simpl. reflexivity.
  simpl. unfold block_to_nat. simpl.




  Theorem nat_block_



Check block_to_nat [].






(* Definition succ_size {n : nat} (b : block n) : nat := min_size (S (block_to_nat b)).

Compute succ_size [I;I;I].
Compute [].
Compute succ_size [].
Compute [I].
Compute succ_size [I].
Compute [O;I].
Compute block_to_nat [O;I].
Compute succ_size [O;I].
Compute min_size 2.
Compute min_size 3.
Compute min_size 4.

Compute block (succ_size []).
*)