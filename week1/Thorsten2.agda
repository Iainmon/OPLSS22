
{-

A, B : Set
-----------
A → B : Set


A · B -- product
A + B -- sum, coproduct

-}

-- pragmatist ()
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

variable A B C : Set

swap : A × B → B × A
proj₁ (swap x) = proj₂ x
proj₂ (swap x) = proj₁ x

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : (A → B → C) → (A × B → C)
uncurry f x = f (proj₁ x) (proj₂ x)

{-
curry (uncurry f) = f
uncurry (curry f) = f


-}

-- verificationist 
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

case' : ((A → C) × (B → C)) → (A ⊎ B → C)
case' = uncurry case

-- uncase : (A ⊎ B → C) → (A → C) × (B → C)
-- unca


data Bool : Set where
  true : Bool
  false : Bool

  
data Three : Set where
  zero one two : Three

{-
How many elements in

-}