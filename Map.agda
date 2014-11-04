open import Agda.Primitive
module Map {i j k : Level} (A : Set i) (B : Set j) (C : Set k) where

_∘_ : (g : B → C) → (f : A → B) → (A → C)
g ∘ f = λ x → g (f x)
