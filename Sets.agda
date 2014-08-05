open import Level
open import Sigma
open import Product renaming (_×_ to _⋀_)
open import Coproduct
open import Empty
module Sets where

{-- this is kinda cool --}

module setops {ℓ : Level} {A : Set ℓ} where
  _∩_ : (P Q : A → Set ℓ) → (A → Set ℓ)
  P ∩ Q = (λ x  → (P x ⋀ Q x))

  _∪_ : (P Q : A → Set ℓ) → Set ℓ
  P ∪ Q = (x : A) → ((P x) ∨ (Q x))

open setops public


{-- out of curiosity... --}

family : {ℓ : Level} → Set ℓ → Set _
family {ℓ} A = A → (Set ℓ)

_∁_ : {ℓ : Level} (A : Set ℓ) → (P : family A) → Set ℓ
A ∁ P = (x : A) → (¬ (P x))





  
