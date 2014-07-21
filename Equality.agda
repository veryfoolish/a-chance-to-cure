open import Agda.Primitive

module Equality where

infix 3 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x


flip : ∀ {ℓ} {A : Set ℓ} {a b : A} → (a ≡ b) → (b ≡ a)
flip refl = refl

_□_ : ∀ {ℓ} {A : Set ℓ} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
refl □ refl = refl

⇕ : ∀ {ℓ} {A : Set ℓ} {a b c : A} → (a ≡ b) → (c ≡ b) → (a ≡ c)
⇕ a p = a □ flip p

trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
trans refl refl = refl

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) →  {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

data Homotopy {i j : Level} {A : Set i} (P : A → Set j) (f g : (x : A) → P x) : Set (i ⊔ j) where
  isHomotopy : ((x : A) → f x ≡ g x) → Homotopy P f g 

id : ∀ {i} {A : Set i} →  A → A
id x = x

theorem : {i : Level} {A : Set i} → Homotopy {i = i} {j = i} {A = A} (λ x → A) id id 
theorem = isHomotopy (λ x → refl)

