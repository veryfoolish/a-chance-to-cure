module Map where

open import Level

_∘_ : {i j k : Level} {A : Set i} {B : Set j} {C : Set k} → (g : B → C) → (f : A → B) → (A → C)
g ∘ f = λ x → g (f x)