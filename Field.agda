module Field where

open import Equality
open import Sigma
open import Coproduct
open import Agda.Primitive

record Field {ℓ : Level} (F : Set ℓ) : Set ℓ where
  field
    _*_ : F → F → F
    _+_ : F → F → F
    assoc+ : (a b c : F) → a + (b + c) ≡ (a + b) + c
    assoc* : (a b c : F) → a * (b * c) ≡ (a * b) * c
    comm+ : (a b : F) → a + b ≡ b + a
    comm* : (a b : F) → a * b ≡ b * a
    id+ : Σ[ O ∈ F ] ((a : F) → a + O ≡ a)
    id* : Σ[ I ∈ F ] ((a : F) → a * I ≡ a)
    inv+ : (a : F) → Σ[ -a ∈ F ] (a + -a ≡ (proj₁ id+))
    inv* : (a : F) → ((a ≡ proj₁ id+) ∨ (Σ[ a′ ∈ F ] (a * a′ ≡ (proj₁ id*))))
    distr : (a b c : F) → a * (b + c) ≡ (a * b) + (a * c)


module Theorems where
  data F₂ : Set where 0₂ 1₂ : F₂

  _+F₂_ : F₂ → F₂ → F₂
  0₂ +F₂ 0₂ = 0₂
  0₂ +F₂ 1₂ = 1₂
  1₂ +F₂ 0₂ = 1₂
  1₂ +F₂ 1₂ = 0₂

  _*F₂_ : F₂ → F₂ → F₂
  0₂ *F₂ _ =  0₂
  1₂ *F₂ b = b

  assoc*F₂ : (a b c : F₂) → a *F₂ (b *F₂ c) ≡ (a *F₂ b) *F₂ c
  assoc*F₂ 0₂ _ _ = refl
  assoc*F₂ 1₂ _ _ = refl

  assoc+F₂ : (a b c : F₂) → a +F₂ (b +F₂ c) ≡ (a +F₂ b) +F₂ c
  assoc+F₂ 0₂ 0₂ 0₂ = refl
  assoc+F₂ 0₂ 0₂ 1₂ = refl
  assoc+F₂ 0₂ 1₂ 0₂ = refl
  assoc+F₂ 0₂ 1₂ 1₂ = refl
  assoc+F₂ 1₂ 0₂ 0₂ = refl
  assoc+F₂ 1₂ 0₂ 1₂ = refl
  assoc+F₂ 1₂ 1₂ 0₂ = refl
  assoc+F₂ 1₂ 1₂ 1₂ = refl

  assoc+F₂′ : (a b c : F₂) → Σ[ d ∈ F₂ ] (a *F₂ (b *F₂ c) ≡ d)
  assoc+F₂′ a b c = (a *F₂ (b *F₂ c)) , refl

  thm′ : (a : F₂) → (a ≡ 0₂) ∨ (a ≡ 1₂)
  thm′ 0₂ = inl refl
  thm′ 1₂ = inr refl

  thm : (a : F₂) → (f : F₂ → F₂) → (f a ≡ 0₂) ∨ (f a ≡ 1₂)
  thm a f = thm′ (f a)


  id+F₂′ : (x : F₂) → (x +F₂ 0₂ ≡ x)
  id+F₂′ m with m
  ... | 0₂ = refl
  ... | 1₂ = refl
  
  id+F₂ : Σ[ O ∈ F₂ ] ((f : F₂) → f +F₂ O ≡ f)
  id+F₂ = 0₂ , id+F₂′

  id*F₂′ : (f′ : F₂) → (f′ *F₂ 1₂ ≡ f′)
  id*F₂′ m with m
  ... | 0₂ = refl
  ... | 1₂ = refl


  id*F₂ : Σ[ I ∈ F₂ ] ((f : F₂) → f *F₂ I ≡ f)
  id*F₂ = 1₂ , id*F₂′ 

  inv+ : (x : F₂) → Σ[ -x ∈ F₂ ] x +F₂ -x ≡ proj₁ id+F₂
  inv+ 0₂ = 0₂ , refl
  inv+ 1₂ = 1₂ , refl

  inv* : (x : F₂) → ((x ≡ proj₁ id+F₂) ∨ (Σ[ x′ ∈ F₂ ] (x *F₂ x′ ≡ proj₁ id*F₂)))
  inv* 0₂ = inl refl
  inv* 1₂ = inr (1₂ , refl)

  distr-F₂ : (a b c : F₂) → a *F₂ (b +F₂ c) ≡ (a *F₂ b) +F₂ (a *F₂ c)
  distr-F₂ 0₂ b c = refl
  distr-F₂ 1₂ b c = refl

  comm+ : (a b : F₂) → a +F₂ b ≡ b +F₂ a
  comm+ 0₂ 0₂ = refl
  comm+ 0₂ 1₂ = refl
  comm+ 1₂ 0₂ = refl
  comm+ 1₂ 1₂ = refl

  comm* : (a b : F₂) → a *F₂ b ≡ b *F₂ a
  comm* 0₂ 0₂ = refl
  comm* 0₂ 1₂ = refl
  comm* 1₂ 0₂ = refl
  comm* 1₂ 1₂ = refl

  F₂-is-field : Field F₂
  F₂-is-field = record {
                  _*_ = _*F₂_;
                  _+_ = _+F₂_;
                  assoc* = assoc*F₂;
                  assoc+ = assoc+F₂;
                  comm+ = comm+;
                  comm* = comm*;
                  id+ = id+F₂;
                  id* = id*F₂;
                  inv+ = inv+;
                  inv* = inv*;
                  distr = distr-F₂ }

open Theorems public

