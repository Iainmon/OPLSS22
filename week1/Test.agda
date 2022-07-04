module Test where

data Bool : Set where
  true : Bool
  false : Bool
  
¬ : Bool → Bool
¬ true = false
¬ false = true



