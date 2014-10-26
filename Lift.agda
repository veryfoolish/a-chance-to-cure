open import Identity
open import Level
open import Sigma 

module Lift where

module theorems {ℓ} {A : Set ℓ} (P : A → Set ℓ) where 
  D : (x y : A) → (x ≡ y) → Set ℓ
  D x y p = P x → P y

  d : (x : A) → D x x refl
  d = λ x → id
  
  transport : {x y : A} (p : x ≡ y) → (P x → P y)
  transport {x} {y} p = (ind= D d x y p)


  {-- lemma 2.3.2 --}
  ∙Lift : {x y : A} → (u : P x) → (p : x ≡ y) → Σ A P
  ∙Lift {x} u p = (x , u)


--  th′ : {x y : A} → (u : P x) → (p : x ≡ y) → proj₁ (∙Lift u p) ≡ p
  --th′ u p = ?
  module T (x y : A)  (u : (P x)) (p : x ≡ y) where
    typ = (proj₁ (∙Lift u p))


open theorems public



