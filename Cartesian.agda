module Cartesian where

open import Level using (_⊔_; Level)
open import Sigma

--- cartesian product type

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B