module Unit where

open import Level using (Level) renaming (zero to l₀)
open import Identity
open import Contractible
open import Sigma

data ❶ : Set l₀ where
  ● : ❶

open import Empty
open import Coproduct

❷ = ❶ ∨ ❶
true : ❷
true = inl ●

false : ❷
false = inr ●

cond : ❷ → ❷ → ❷
cond (inl ●) b = b
cond _ _ = true


open import Boolean renaming (true to 1₂; false to 0₂)

f : ❷ → Boolean
f (inl x) = 1₂
f (inr x) = 0₂

f⁻ : Boolean → ❷
f⁻ 0₂ = false
f⁻ 1₂ = true

thm : (x : Boolean) → (f (f⁻ x)) ≡ x
thm 0₂ = refl
thm 1₂ = refl

thm′ : (x : ❷) → (f⁻ (f x)) ≡ x
thm′ (inl ●) = refl
thm′ (inr ●) = refl



-- ghetto equality

  


