{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --without-K #-}
open import Agda.Primitive


module Sketch where

  data sigma {ℓ : Level} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
    pair : (a : A) → B a → sigma A B

  data Id {ℓ : Level} (A : Set ℓ) (a : A) : A → Set ℓ where
    refl : Id A a a 

  contractible : {p : Level} (A : Set p) → A → Set p
  contractible A a = (b : A) → Id A a b

  data 𝟚 : Set where
    0₂ 1₂ : 𝟚

  module contr-theorem  where
    data Unit : Set where
      ∙ : Unit

    data ⊥ : Set where
    
    ↯ = contractible
    
    module ⋆ {ℓ : Level} where
      not : Set ℓ → Set ℓ
      not A = A → ⊥

      theorem-con : (A : Set ℓ) → (a b : A) → ↯ A a → ↯ A b → Id A a b
      theorem-con A a b p q = p b

      ¬_ = λ x  → not x
      
      neq : (A : Set ℓ) → A → A → Set ℓ
      neq A a b = ¬ (Id A a b)

      aneqbimpnocontr : (A : Set ℓ) → (a b : A) → (p : neq A a b) → ¬ (↯ A a)
      aneqbimpnocontr A a b p = λ x → p (x b)
    open ⋆ public

    𝟙-is-contractible : ↯ Unit ∙
    𝟙-is-contractible ∙ = refl

    𝟚-not-contr = aneqbimpnocontr 𝟚 0₂ 1₂ abin𝟚neq where
      abin𝟚neq : neq 𝟚 0₂ 1₂
      abin𝟚neq = λ ()

  open contr-theorem


