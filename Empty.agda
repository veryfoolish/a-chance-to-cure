open import Level renaming (zero to ∘)
module Empty where

data ⊥ : Set ∘ where

⊥-elim : ∀ {i} {P : ⊥ → Set i} → ((x : ⊥) → P x)
⊥-elim ()

¬ : ∀ {i} (A : Set i) → Set i
¬ A = A → ⊥
