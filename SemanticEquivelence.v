

Require Import List.
Import ListNotations.
Check [1].



Definition stack := list nat.

Inductive bit : Set :=
  | I : bit
  | O : bit.

Definition bitstr := list bit.

Inductive expr (ops : Set) (lits : Set) : Set :=
  | Lit : lits -> expr ops lits
  | Bin : ops -> expr ops lits -> expr ops lits -> expr ops lits.

Arguments Lit {ops} {lits}.
Arguments Bin {ops} {lits}.

Check Lit 1.


Inductive semantics (L : Set) (D : Set) : Type := 
  sem_f : (L -> D) -> semantics L D.

Arguments sem_f {L} {D}.


Inductive semantic_evaluation {L D : Set} (sem : L -> D) | (e : L) (d : D) : Prop 
  := sem_eval : sem e = d -> semantic_evaluation e d.

Definition sem {L D} {s : semantics L D} : L -> D := 
  let 'sem_f sem_fun := s in sem_fun.

Notation "[[ x ]]" := (sem x).





Fixpoint expr_semantics' 
  {ops lits : Set} {D : Set} (sem_lit : lits -> D) 
  (sem_op : ops -> D -> D -> D) (e : expr ops lits) : D :=
  let expr_sem := expr_semantics' sem_lit sem_op in
    match e with
      | Lit x  => sem_lit x
      | Bin op e1 e2 => sem_op op (expr_sem e1) (expr_sem e2)
      end.

Definition expr_semantics 
  {ops lits D : Set} (sem_lit : lits -> D) (sem_op : ops -> D -> D -> D) : semantics (expr ops lits) D :=
  sem_f (expr_semantics' sem_lit sem_op).

(* Record expr_sem_def_parts (lits ops D : Set) : Set := mkParts { sem_lit : lits -> D ; sem_op : ops -> D -> D -> D }. *)


Inductive expr_semantics_definition (lits ops D : Set) : Set := 
  | expr_sem_def_parts : forall (sem_lit : lits -> D) (sem_op : ops -> D -> D -> D), expr_semantics_definition lits ops D.
  
