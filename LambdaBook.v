

Require Import Coq.Init.Nat.


Require Import List.
Import ListNotations.



Definition string (A : Set) : Set := list A.

Definition e {A} : string A := [].

Definition language (A : Set) : Type := string A -> Prop.

Inductive k_star (A : Set) : language A :=
  | k_star_cons : forall (w : string A), k_star A w.

Lemma all_sub_k_star : 
  forall {A} (L : language A) (w : string A),
    L w -> k_star A w.
Proof.
  intros.
  apply k_star_cons.
Qed.

Inductive regex (A : Set) : language A :=
  | regex_lit (w : string A) : regex A w
  | regex_or (r1 r2 : regex A) (w : string A) : r1 w \/ r2 w.

Fixpoint length {A} (w : string A) : nat :=
  match w with
    | []      => 0
    | c :: w' => S (length w')
  end.


(*


(true(X) & true(Y)) => true(and(X,Y)).
true(and(X,Y)) => (true(X) & true(Y)).

(true(X) | true(Y)) => true(or(X,Y)).
true(or(X,Y)) => (true(X) | true(Y)).

true(p).
true(q).
-true(r).

(true(or(X,r))) => $ans(X).

*)