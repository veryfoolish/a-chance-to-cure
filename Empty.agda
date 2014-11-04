open import Agda.Primitive
module Empty where

data ⊥ : Set where

⊥-elim : ∀ {i} {P : ⊥ → Set i} → ((x : ⊥) → P x)
⊥-elim ()

¬ : {ℓ : Level} → (A : Set ℓ) → Set ℓ
¬ A = A → ⊥

module Theorems {ℓ : Level} (A : Set ℓ) where
  theorem-α : ¬ (¬ (¬ A)) → ¬ A
  theorem-α ¬¬¬A a = ¬¬¬A (λ z → z a)
