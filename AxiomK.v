
Theorem confluence : forall (A B : Type) (x y : A) (f : A -> B), x = y -> f x = f y.
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.

Theorem my_thm_1 : forall (A B : Type) (f g : A -> B), 
    f = g -> (fun x : A => f x) = (fun y : A => g y).
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.

(* 
-- uniqueness of identity proofs

uip : [A:Type] -> [x:A] -> [y :A] -> (p : x = y) -> (q:x = y) -> (p = q)
uip = \ [A][x][y] p q . 
  subst (subst Refl by p : p = Refl) by q

-- "axiom" K

k : [A:Type] -> [x:A] -> (p : x = x) -> (p = Refl)
k = \ [A][x] p . 
  subst Refl by p

-- another version of the above
-- From: https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29
k2 : [A:Type] -> [x:A] -> [P : (x = x) -> Type] -> P Refl -> (h:x = x) -> P h
k2 = \ [A][x][P] d h . subst d by h 
*)




Theorem stupid : forall (n : nat), n = n.
Proof.
    reflexivity.
Qed.

Print stupid.

Print eq_refl.


Axiom axiom_k : forall (A : Type) (x : A) (p : x = x), p = eq_refl.

Theorem uip : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
    intros A x y p. 
    destruct p.
    intros q.
    destruct (axiom_k A x q).
    reflexivity.
Qed.


Theorem axiom_k_2 : 
    forall (A : Type) (x : A),
        forall (P : (x = x) -> Type), 
            P eq_refl -> forall (h : x = x), P h.
Proof.
    intros A x P.
    intros Peq.
    intros h.
    (* pose proof axiom_k as AxK. *)
    (* pose proof (axiom_k A x) as H0. *)
    pose proof (axiom_k A x h) as H.
    rewrite H.
    assumption.
Qed.

Print axiom_k_2.


(* 
-- here's j
-- https://ncatlab.org/nlab/show/identity+type#ExplicitDefinition

j : [A:Type]
  -> [C : (x:A) -> (y:A) -> (x = y) -> Type] 
  -> ((x:A) -> C x x Refl) 
  -> (x:A) -> (y:A) -> (p : x = y) -> C x y p
j = \[A][C] t x y p . subst (t x) by p

*)

Theorem j : forall (A : Type),
    forall (C : forall (x y : A), x = y -> Type),
        (forall (x : A), C x x eq_refl) -> 
            forall (x y : A) (p : x = y), C x y p.
Proof.
    intros A C.
    intros H.
    intros x y.
    intros p.
    rewrite <- p.
    apply H.
Qed.
