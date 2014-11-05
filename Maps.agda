module Maps where

open import Agda.Primitive
open import Identity renaming (_≗_ to _≡_) 
open import Sigma 

data _~_ {ℓ} {A B : Set ℓ} (f g : A → B) : Set ℓ where
  feq : {a : A}  → f a ≡ g a → f ~ g


_∘_ : {ℓ : Level} → {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → (g (f x))




