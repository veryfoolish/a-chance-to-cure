open import Level
open import Natural
open import Sigma
open import Product renaming (_×_ to _⋀_)
open import Coproduct
open import Empty
open import Identity
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

data is∙Prop {ℓ} (A : Set ℓ) {p q : A} : Set ℓ where
  isprop : (p ≡ q) → is∙Prop A

is∙Set : {ℓ : Level} → Set ℓ → Set ℓ
is∙Set A = (x y : A) → is∙Prop A

data NLevel {ℓ : Level} : Set ℓ where
  ⟨_⟩ : ℕ → NLevel

is∙_∙type : {ℓ : Level} → NLevel {ℓ} → Set ℓ → Set ℓ
is∙_∙type   ⟨ 0 ⟩ X = is∙Contr X
is∙_∙type ⟨ S n ⟩ X = (x y : X) → is∙ ⟨ n ⟩ ∙type (x ≡ y)


n-type : {ℓ : Level} → (NLevel) {ℓ} → Set (suc ℓ)  
n-type {ℓ} n  = Σ[ U ∈ Set ℓ ] (is∙ n ∙type U)

thm : ∀ {ℓ} {A : Set ℓ} → (q p : is∙Prop A) → q ≡ p
thm (isprop x) (isprop x₁) = {!!}
