module Boolean where

open import Level using (Level) renaming (zero to lzero)
open import Equality
open import Coproduct

data Boolean : Set lzero where
  ⊥ ⊤ : Boolean

rec₂ : ∀ {ℓ}  {C : Set ℓ} → C → C → Boolean → C
rec₂ fal _ ⊥  = fal
rec₂ _ tru ⊤  = tru

ind₂ : ∀ {ℓ} (C : Boolean → Set ℓ) → C ⊥ → C ⊤ → ((x : Boolean) → C x)
ind₂ C c0 _ ⊥ = c0
ind₂ C _ c1 ⊤ = c1

theorem′ : (x : Boolean) → ((x ≡ ⊥) ∨ (x ≡ ⊤))
theorem′  = ind₂ C (inl refl) (inr refl)
            where C = λ y → (y ≡ ⊥) ∨ (y ≡ ⊤)


Not : Boolean → Boolean
Not = rec₂ ⊤ ⊥

_∧_ : Boolean → Boolean → Boolean
⊤ ∧ ⊤ = ⊤
_ ∧ _ = ⊥

_⊕_ : Boolean → Boolean → Boolean
⊤ ⊕ ⊤ = ⊥
⊤ ⊕ ⊥ = ⊤
⊥ ⊕ ⊤ = ⊤
⊥ ⊕ ⊥ = ⊥ 

_⊹_ : Boolean → Boolean → Boolean
⊤ ⊹ _ = ⊤
_ ⊹ ⊤ = ⊤
_ ⊹ _ = ⊥

IsTrue : Boolean → Boolean
IsTrue x = x