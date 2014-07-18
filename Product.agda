module Product where

open import Agda.Primitive
open import Sigma

--- cartesian product type

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B