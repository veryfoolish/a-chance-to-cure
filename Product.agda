module Product where

open import Agda.Primitive
open import Sigma

--- cartesian product type

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

π₁  : ∀ {a b} {A : Set a} {B : Set b} → ((A × B) → A)
π₁ p = proj₁ p

π₂  : ∀ {a b} {A : Set a} {B : Set b} → ((A × B) → B)
π₂ p = proj₂ p

⟦_,_⟧ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
⟦ a , b ⟧ = a , b
