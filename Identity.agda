open import Agda.Primitive

module Identity where

infix 3 _≗_


data _≗_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≗ x

{-# BUILTIN EQUALITY _≗_ #-}
{-# BUILTIN REFL refl #-}

module ops {ℓ} {A : Set ℓ} where
  infix 4 _▮_ _⁻

  _⁻ : {a b : A} → (a ≗ b) → (b ≗ a)
  refl ⁻ = refl

  _▮_ : {a b c : A} → (a ≗ b) → (b ≗ c) → (a ≗ c)
  refl ▮ refl = refl

  ap : {B : A → Set ℓ} → {x y : A} → (f : A → B x) → x ≗ y → f x ≗ f y
  ap f refl = refl
open ops public

module Identity {ℓ} {A : Set ℓ} where

  id : A → A
  id x = x

open Identity public

module induction {ℓ : Level} {A : Set ℓ} where

  ind= : (C : (x y : A) → (x ≗ y) → Set ℓ) → ((x : A) → (C x x refl)) → (x y : A) → (p : x ≗ y) → C x y p
  ind= C c x .x refl = c x

open induction public

module based-path-induction {ℓ : Level} {A : Set ℓ} (a : A) where

  module based (C : (x : A) → (a ≗ x) → Set ℓ) (c : C a refl) where
    f : (x : A) → (p : a ≗ x) → C x p
    f .a refl = c
