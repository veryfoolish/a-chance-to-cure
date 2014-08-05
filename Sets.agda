open import Level
open import Natural
open import Sigma
open import Product renaming (_×_ to _⋀_)
open import Coproduct
open import Empty
open import Equality
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


is∙Contr : {ℓ : Level} → Set ℓ → Set ℓ
is∙Contr A = Σ[ x ∈ A ] ((y : A) → x ≡ y)

is∙Prop : {ℓ : Level} → Set ℓ → Set ℓ
is∙Prop A = (p q : A) → (p ≡ q)

is∙Set : {ℓ : Level} → Set ℓ → Set ℓ
is∙Set A = (x y : A) → is∙Prop (x ≡ y)

data NLevel {ℓ : Level} : Set ℓ where
  ⟨_⟩ : ℕ → NLevel

is∙_∙type : {ℓ : Level} → NLevel {ℓ} → Set ℓ → Set ℓ
is∙_∙type   ⟨ 0 ⟩ X = is∙Contr X
is∙_∙type ⟨ S n ⟩ X = (x y : X) → is∙ ⟨ n ⟩ ∙type (x ≡ y)


⟪_⟫-type : {ℓ : Level} → NLevel {ℓ} → Set (suc ℓ)  
⟪_⟫-type {ℓ} n  = Σ[ U ∈ Set ℓ ] (is∙ n ∙type U)
