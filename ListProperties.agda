open import List renaming (length to len)
open import Natural
open import Equality
open import Level

module ListProperties {ℓ : Level} {A : Set ℓ} where
  
Lemma₁ : (a b : List A) → (len a) + (len b) ≡ len (a ++ b)
Lemma₁ [] b = refl
Lemma₁ (x ∷ xs) b = ≡-fun-ap S (Lemma₁ xs b)


