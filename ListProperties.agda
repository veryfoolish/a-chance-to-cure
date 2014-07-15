open import List renaming (length to ∣_∣; _++_ to _⋈_)
open import Natural
open import Equality
open import Level

module ListProperties {ℓ : Level} {A : Set ℓ} where
  
Lemma₁ : (X Y : List A) → ∣ X ∣ + ∣ Y ∣ ≡ ∣ X ⋈ Y ∣ 
Lemma₁ [] b = refl
Lemma₁ (x ∷ xs) b = ap S (Lemma₁ xs b)




