Require Import List.
Import ListNotations.
Check [1].



Definition stack := list nat.


Definition evaluation (prog_rep sem_dom : Type) := prog_rep -> sem_dom.




Inductive stk_op_s : Set :=
  | load : nat -> stk_op_s
  | add : stk_op_s
  | mul : stk_op_s
  | pop : stk_op_s.

Definition program_s := list stk_op_s.
Definition sem_dom_s := stack -> stack.
  

(* Small Step *)
Definition eval_op_s (i : stk_op_s) (s : stack) : stack := 
  match i,s with
    | load n,_ => n :: s
    | add, (a :: b :: s') => (a + b) :: s'
    | mul, (a :: b :: s') => (a * b) :: s'
    | pop,(_ :: s') => s'
    | _,_ => s
  end.
Print eval_op_s.
Fixpoint eval_s (p : program_s) : sem_dom_s :=
  match p with
    | i :: p' => fun s : stack => eval_s p' (eval_op_s i s)
    | []      => id
    end.

Check eval_s : evaluation program_s sem_dom_s.





Inductive stk_op_t : Set :=
  | LD   : nat -> stk_op_t
  | ADD  : stk_op_t
  | MUL  : stk_op_t
  | DUP  : stk_op_t
  | SWAP : stk_op_t
  | POP  : nat -> stk_op_t.

(* Small Step *)
Fixpoint eval_op_t (i : stk_op_t) (s : stack) : stack := 
  match i,s with
    | LD n,_ => n :: s
    | ADD, (a :: b :: s') => (a + b) :: s'
    | MUL, (a :: b :: s') => (a * b) :: s'
    | DUP, (a :: s') => a :: a :: s'
    | SWAP, (a :: b :: s') => b :: a :: s'
    | POP 0,_ => s
    | POP n,(a :: s') => eval_op_t (POP (n - 1)) s'
    | _,_ => s
  end.


Definition program_t := list stk_op_t.
Definition sem_dom_t := stack -> stack.
  
Fixpoint eval_t (p : program_t) : sem_dom_t :=
  match p with
    | i :: p' => fun s : stack => eval_t p' (eval_op_t i s)
    | []      => id
    end.

Check eval_t : evaluation program_t sem_dom_t.






Definition compiler (L1 L2 : Type) := L1 -> L2.


(* P ---> c(P) *)
Fixpoint stk_op_compiler (p : program_s) : program_t :=
  match p with
    | load n :: p' => LD n  :: (stk_op_compiler p')
    | add    :: p' => ADD   :: (stk_op_compiler p')
    | mul    :: p' => MUL   :: (stk_op_compiler p')
    | pop    :: p' => POP 1 :: (stk_op_compiler p')
    | []           => []
    end.

Check stk_op_compiler : compiler program_s program_t.
  

(* Definition semantic_equivelence (s : sem_dom_s) (t : sem_dom_t) := 
  forall (stk : stack), s stk = t stk. *)

(* Theorem stk_op_compiler_correctness : 
  forall (p : program_s) (s s' : sem_dom_s), eval_s p s = s' -> 
    forall (t : sem_dom_t), semantic_equivelence s t -> 
      exists (t' : sem_dom_t), 
        eval_t (stk_op_compiler p) t = t' /\ semantic_equivelence s' t'. *)

Definition semantic_equivelence (s : stack) (t : stack) := s = t.


Theorem stk_op_compiler_function : 
  forall (p : program_s), forall (s : stack),
    semantic_equivelence (eval_s p s) (eval_t (stk_op_compiler p) s).
Proof.
  intros.
  unfold semantic_equivelence.
  induction p.
  simpl. reflexivity.
  destruct a.  simpl.
  unfold eval_op_t. simpl.



Theorem stk_op_compiler_correctness_2 : 
  forall (p : program_s) (p' : program_t) (s s' : stack) (t t' : stack),
    semantic_equivelence s t -> 
    eval_s p s = s' ->
    stk_op_compiler p = p' ->
    eval_t p' t = t' ->
    semantic_equivelence s' t'.
Proof.
  unfold semantic_equivelence.
  intros.
  rewrite <- H0.
  rewrite <- H2.
  rewrite H.
  rewrite <- H1.

Theorem stk_op_compiler_correctness : 
forall (p : program_s) (s s' : stack), eval_s p s = s' -> 
  forall (t : stack), semantic_equivelence s t -> 
    exists (t' : stack), 
      eval_t (stk_op_compiler p) t = t' /\ semantic_equivelence s' t'.
Proof.
  intros p.
  intros s s'.
  intros H0.
  intros t.
  unfold semantic_equivelence.

  intros H1.
  destruct H1.


  (* Definition eval_op_s (i : stk_op_s) : eval_op_s_type i := *)

  Inductive fixed_stack : nat -> Set :=
  | wrap : forall (s : stack), fixed_stack (length s).

Definition unwrap {n : nat} (fs : fixed_stack n) : stack :=
  match fs with
    | wrap s => s
  end.

(* Check length.
Check wrap. *)

Lemma wrap_unwrap_eq : forall (s : stack), unwrap (wrap s) = s.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Definition program_s (n m : nat) := fixed_stack n -> fixed_stack m.

Definition eval_op_s_type (i : stk_op_s) :=
  match i with
    | load _ => forall (n : nat), program_s n (n + 1)
    | add    => forall (n : nat), program_s (n + 2) (n + 1)
    | mul    => forall (n : nat), program_s (n + 2) (n + 1)
    | pop    => forall (n : nat), program_s (n + 1) n
    end.
