module A where

open import Agda.Builtin.Nat

variable A B C : Set
variable m n : Nat


data Greeting : Set where
  hello : Greeting
  david : Greeting
 

greet : Greeting
greet = hello

data Fin : Nat -> Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) -> Fin (suc n)


myVal : Greeting
myVal = david



h : Fin 3
h = zero