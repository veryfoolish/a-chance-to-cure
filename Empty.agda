module Empty where

open import Level

data ⊥ : Set zero where

⊥-elim : {ℓ : Level} {A : Empty → Set ℓ} → ((x : Empty) → A x)
⊥-elim ()

⊥-rec : {ℓ : Level} {A : Type ℓ} → (⊥ → A)
⊥-rec = ⊥-elim