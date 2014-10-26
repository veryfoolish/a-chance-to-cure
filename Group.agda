module Group where

open import Identity
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

module Homomorphism {ℓ m} (A : Set ℓ) (B : Set m) where
       open Group A renaming (mul to _●_; unit to g)
       open Group B renaming (mul to _*_; unit to h)
       data Map : Set (ℓ ⊔ m) where
         map : (f : A → B) → (f g ≡ h) → ((a b : A) → (f (a ● b)) ≡ ((f a) * (f b))) → Map
