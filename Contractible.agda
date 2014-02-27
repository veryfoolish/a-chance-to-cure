module Contractible where

open import Level
open import Sigma
open import Equality

Contractible : {ℓ : Level} (X : Set ℓ) → Set ℓ
Contractible X = Σ[ x₁ ∈ X ] ((x₂ : X) → x₁ ≡ x₂)

