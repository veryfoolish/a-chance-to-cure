open import Level using (Level)

module Equality where

infix 3 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x


≡-symmetric : {ℓ : Level} {A : Set ℓ} {a b : A} → (a ≡ b) → (b ≡ a)
≡-symmetric refl = refl

≡-trans : {ℓ : Level} {A : Set ℓ} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
≡-trans refl refl = refl

≡-trans-flip : {ℓ : Level} {A : Set ℓ} {a b c : A} → (a ≡ b) → (c ≡ b) → (a ≡ c)
≡-trans-flip a p = ≡-trans a (≡-symmetric p)

≡-fun-ap : {i j : Level} {A : Set i} {B : Set j} (f : A → B) → 
           {x y : A} → x ≡ y → f x ≡ f y
≡-fun-ap f refl = refl