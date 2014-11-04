module Group where

open import Identity renaming (_≗_ to _≡_)
open import Agda.Primitive renaming (lsuc to ↑)

record Group {ℓ} (G : Set ℓ) : Set ℓ where
  field
    unit : G
    mul : G → G → G
    inv : G → G 
    unit-r-cancel : ∀ {a} → (mul unit a) ≡ a
    unit-l-cancel : ∀{a} → (mul a unit) ≡ a
    assoc : ∀ {a b c} → mul (mul a b) c ≡ mul a (mul b c)
    inv-lunit : ∀ {a} → mul (inv a) a ≡ unit
    inv-lrunit : ∀ {a} → mul a (inv a) ≡ unit


