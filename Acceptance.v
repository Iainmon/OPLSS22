Section Acceptance.
Set Implicit Arguments.


(* 
Inductive logic (Ag At Op : Set) : Prop := 
    | prim (p : At)              : logic Ag At Op
    | not (phi : logic Ag At Op) : logic Ag At Op
    | conj (phi psi : logic Ag At Op) : logic Ag At Op
    | modal (o : Op) (a : Ag) (phi : logic Ag At Op) : logic Ag At Op. *)


Variables Ag At Op : Set.



(* Foramtion rules *)

Inductive T : Prop := tons : T.

Reserved Notation "$ a $" (at level 50).
Inductive prim_prop (p : At) : Prop := prim'  : $ p $
where "$ a $" := (prim_prop a) : type_scope.

Reserved Notation "¬ a" (at level 50).
Inductive neg (A : Prop) : Prop := neg' : ¬ A
where "¬ a" := (neg a) : type_scope.

Reserved Notation "a & b" (at level 50).
Inductive and' (A B : Prop) : Prop := conj' : A & B
where "a & b" := (and' a b) : type_scope.

Reserved Notation "a 'or' b" (at level 50).
Inductive or' (A B : Prop) : Prop := disj' : A or B
where "a 'or' b" := (or' a b) : type_scope.

Reserved Notation "a ==> b" (at level 50).
Inductive implies' (A B : Prop) : Prop := if_then' : A ==> B
where "a ==> b" := (implies' a b) : type_scope.

Reserved Notation "a <==> b" (at level 50).
Inductive biimplies' (A B : Prop) : Prop := iff' : A <==> B
where "a <==> b" := (biimplies' a b) : type_scope.


Reserved Notation "k 'via' a 'of' p" (at level 50).
Inductive modal (k : Op) (a : Ag) (p : Prop) : Prop :=
    | p_introsp : k via a of p
where "k 'via' a 'of' p" := (modal k a p) : type_scope.



(* This are just the productions for our logical languagel. *)
Inductive logic_language : Set := 
    | l_top                             : logic_language 
    | l_prim (p : At)                   : logic_language 
    | l_neg (phi : logic_language)      : logic_language 
    | l_conj (phi psi : logic_language) : logic_language 
    | l_modal (o : Op) (a : Ag) (phi : logic_language) : logic_language.

Fixpoint logic_language_to_prop (p : logic_language) : Prop := 
    match p with 
        | l_top           => T 
        | l_prim p'        => $ p' $ 
        | l_neg phi       => ¬ (logic_language_to_prop phi)
        | l_conj phi psi  => (logic_language_to_prop phi) & (logic_language_to_prop psi) 
        | l_modal o a phi => o via a of (logic_language_to_prop phi)
        end.


Check logic_language.
Definition L := logic_language.




Axiom abreviation_1 : forall {P Q : Prop}, P or Q   = ¬ ((¬ P) & (¬ Q)).
Axiom abreviation_2 : forall {P Q : Prop}, P ==> Q  = (¬ P) or Q.
Axiom abreviation_3 : forall {P Q : Prop}, P <==> Q = (P ==> Q) & (Q ==> P).

Axiom demorgans_1 : forall {P Q : Prop}, ¬ (P & Q) = (¬ P) or (¬ Q).
Axiom demorgans_2 : forall {P Q : Prop}, ¬ (P or Q) = (¬ P) & (¬ Q).


(* 
Notation "P 'or' Q" := (¬ ((¬ P) & (¬ Q))) (at level 50, left associativity).
Notation "P => Q" := ((¬ P) or Q) (at level 80, right associativity).
Notation "P <=> Q" := ((P => Q) & (Q => P)) (at level 50, no associativity). *)

Reserved Notation "a :- b" (at level 80, no associativity).

Inductive judgment : Prop -> bool -> Prop := 
    | j_top     : T :- true
    | j_bot     : ¬ T :- false
    | j_and_i   {A B : Prop} : A :- true -> B :- true -> A & B :- true
    | j_and_e1  {A B : Prop} : A & B :- true -> A :- true
    | j_and_e2  {A B : Prop} : A & B :- true -> B :- true
    | j_and_sym {A B : Prop} : A & B :- true -> B & A :- true
    | j_or_i1   {A B : Prop} {b : bool} : A :- true -> B :- b -> A or B :- true
    | j_or_i2   {A B : Prop} {b : bool} : B :- true -> A :- b -> A or B :- true
    | j_or_e1   {A B : Prop} : A or B :- true -> A :- false -> B :- true
    | j_or_e2   {A B : Prop} : A or B :- true -> B :- false -> A :- true
    | j_or_sym  {A B : Prop} {b : bool} : A or B :- b -> B or A :- b
    | j_neg_em_i  {A : Prop} {b : bool} : A :- b -> ¬ A :- (negb b)
    | j_neg_em_e  {A : Prop} {b : bool} : ¬ A :- b -> A :- (negb b)

where "a :- b" := (judgment a b) : type_scope.



Axiom conjunction_assoc : forall {A B C : Prop}, (A & B) & C = A & (B & C).
Axiom conjunction_comm : forall {A B C : Prop}, A & B = B & A.

Axiom disjunction_assoc : forall {A B C : Prop}, (A or B) or C = A or (B or C).
Axiom disjunction_comm : forall {A B : Prop}, A or B = B or A. 

(* You can prove these with *)
(* 
Axiom interchangability : forall {A B : Prop}, A <==> B :- true <-> A = B. *)

Axiom interchangability : forall {A B : Prop}, A = B -> A :- true -> B :- true.


Theorem modes_ponens : forall {P Q : Prop}, P ==> Q :- true -> P :- true -> Q :- true.
Proof.
    intros P Q.
    rewrite abreviation_2.
    intros.
    apply j_neg_em_i in H0. simpl in H0.
    apply j_or_e1 in H.
    assumption. assumption.
Qed.

Print modes_ponens.

Theorem cut_rule : forall (P Q R : Prop), P ==> Q :- true -> Q ==> R :- true -> P ==> R :- true.
Proof.
    intros P Q R.
    intros H1.
    pose proof (modes_ponens H1).
    rewrite abreviation_2 in H1. 

    intros H2.
    pose proof (modes_ponens H2).
    rewrite abreviation_2 in H2.
    pose proof H1 as H3.
    apply j_neg_em_i in H3. simpl in H3.
    pose proof (j_or_i1 H2 H3).
    rewrite <- disjunction_comm in H4.
    rewrite <- abreviation_2 in H4.
    rewrite <- abreviation_2 in H4.
    rewrite <- abreviation_2 in H4.

    pose proof (modes_ponens H4).
    pose proof (modes_ponens H5).

    apply modes_ponens.

    rewrite <-  abreviation_2 in H4.


    rewrite <- disjunction_assoc in H3.

    pose proof H3.
    pose proof H3.
    rewrite disjunction_assoc in H4.
    rewrite <- disjunction_assoc in H5.
    rewrite <- abreviation_2 in H4.
    rewrite <- abreviation_2 in H5.
    rewrite disjunction_assoc in H5.
    rewrite <- abreviation_2 in H5.
    
    (* pose proof (j_or_i1 H1 H2). *)

    rewrite <- abreviation_2 in H5.

    assumption.

    rewrite disjunction_assoc.
    rewrite abreviation_1.
    rewrite <- disjunction_assoc in H3.

    rewrite abreviation_2. 

    rewrite (abreviation_2 Q R).
    rewrite (abreviation_2 Q R).

    apply modes_ponens.
    intros H3.
    pose proof (modes_ponens H3).


Inductive log_eq (p : Prop) : Prop :=
    | leq_refl : log_eq p p
    | 


Example ez : T :- false -> ¬ T :- true.
Proof.
    simpl.
    intros. auto.
    apply j_neg_em. assumption.
Qed.

Inductive conjuction (a b : judgment) : Prop :=
    | conj : classical a treu

Inductive atomic_truth (p : At) : Prop :=
    mathc 

Inductive or (a b : L) : Prop :=
    | disj : a -> or a b.


Definition disj ()


End Acceptance.