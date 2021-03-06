{-# OPTIONS --without-K #-}
module Boolean where

open import Agda.Primitive
open import Identity renaming (_≗_ to _≡_)
open import Coproduct

data Boolean : Set lzero where
  false true : Boolean

rec₂ : ∀ {ℓ}  {C : Set ℓ} → C → C → Boolean → C
rec₂ fal _ false  = fal
rec₂ _ tru true  = tru

ind₂ : ∀ {ℓ} (C : Boolean → Set ℓ) → C false → C true → ((x : Boolean) → C x)
ind₂ C c0 _ false = c0
ind₂ C _ c1 true = c1

theorem′ : (x : Boolean) → ((x ≡ false) ∨ (x ≡ true))
theorem′  = ind₂ C (inl refl) (inr refl)
            where C = λ y → (y ≡ false) ∨ (y ≡ true)


Not : Boolean → Boolean
Not = rec₂ true false

_∧_ : Boolean → Boolean → Boolean
true ∧ true = true
_    ∧ _    = false

_⊕_ : Boolean → Boolean → Boolean
true  ⊕ true  = false
true  ⊕ false = true
false ⊕ true  = true
false ⊕ false = false 

_⊹_ : Boolean → Boolean → Boolean
true ⊹ _    = true
_    ⊹ true = true
_    ⊹ _    = false

IsTrue : Boolean → Boolean
IsTrue x = x
