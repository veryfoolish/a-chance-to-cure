module Identity where

open import Level
open import Equality
open import Sigmax

-- total identity space (see : Gambino, et al. “The Univalence Axiom ...”
Id : {ℓ : Level} (X : Set ℓ) → Set ℓ
Id X = Σ[ x ∈ X ] (Σ[ x′ ∈ X ] x ≡ x′)






