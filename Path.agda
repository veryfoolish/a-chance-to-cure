module Path where

open import Agda.Primitive

module A {ℓ : Level} where

  data Id (A : Set ℓ) : A → A → Set ℓ where
    ℜ : (x : A) → Id A x x

open A public

data ② : Set₁ where
  ⊥ ⊤ : ②

⊤==⊤ : Id ②  ⊤ ⊤
⊤==⊤ = ℜ ⊤


module PathInduction 
       {ℓ : Level} 
       (A : Set ℓ)
       (C : (x y : A) → (Id A x y) → Set ℓ)
       (c : (x : A) → (C x x (ℜ x)))
       where

       f′ : (x y : A) → (p : Id A x y) → C x y p
       f′ x .x (ℜ .x) = c x
open PathInduction

module J
  {ℓ : Level}
  (A : Set ℓ)
  (C : (x y : A) → Id A x y → Set ℓ)
  where
  ind= : ((x : A) → C x x (ℜ x)) → (x y : A) → (p : Id A x y) → C x y p
  ind= c x .x (ℜ .x) = c x
open J

module BasedPathInduction
       {ℓ : Level}
       (A : Set ℓ)
       (C : ∀ {a} → ((x : A) → ((Id A a x) → Set ℓ)))
       (c : ∀ {a} → (C a (ℜ a)))
       where
       f : ∀ {a} → (x : A) → (p : Id A a x) → (C x p)
       f a (ℜ .a) = c
open BasedPathInduction

