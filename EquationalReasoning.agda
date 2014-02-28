open import Level
open import Equality

module EquationalReasoning { ℓ : Level} {A : Set ℓ} where

infixr 2 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ refl ⟩ refl = refl

_∎ : (x : A) → x ≡ x
_ ∎ = refl
