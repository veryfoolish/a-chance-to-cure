open import Level using (Level)


module Equality where

infix 3 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

module Equality-Props {ℓ : Level} (A : Set ℓ) where
  ≡-symmetric : {a b : A} → (a ≡ b) → (b ≡ a)
  ≡-symmetric refl = refl

  ≡-trans : {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
  ≡-trans refl refl = refl
open Equality-Props public
