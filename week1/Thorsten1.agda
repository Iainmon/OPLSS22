


open import Data.Nat

module Thorsten1 where


{-



-}



f : ℕ → ℕ 

f n = n + 2



variable A B C : Set



_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

compose = λ x y → x ∘ y

K : A → B → A
K a b = a


S : (A → B → C) → (A → B) → (A → C)
S f g a = f a (g a)


I : A → A
I {A} = S K (K {B = A})



CC : (B → C) → (A → B) → (A → C)
CC = λ z z₁ z₂ → z (z₁ z₂)

CC-sk : (B → C) → (A → B) → (A → C)
CC-sk = {!   !}


