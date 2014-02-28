module NaturalProperties where

open import Natural
open import Equality

-- addition: commutative.

+comm-lemma₁ : {a : ℕ} → 0 + a ≡ a
+comm-lemma₁ = refl

+comm-lemma₂∙₁ : {a b : ℕ} → a ≡ b → S a ≡ S b
+comm-lemma₂∙₁ refl = refl

+comm-lemma₂ : {a : ℕ} → a + 0 ≡ a
+comm-lemma₂ {0} = refl
+comm-lemma₂ {(S n)} = +comm-lemma₂∙₁ +comm-lemma₂

+comm-lemma₃ : {a : ℕ} → 0 + a ≡ a
+comm-lemma₃ = refl 

+comm-zero-id₁ : {a : ℕ} → a + 0 ≡ 0 + a
+comm-zero-id₁ = ≡-trans-flip +comm-lemma₂ +comm-lemma₃

+comm-zero-id₂ : {a : ℕ} → 0 + a ≡ a + 0
+comm-zero-id₂ = ≡-trans-flip +comm-lemma₃ +comm-lemma₂

+comm-support₁ : {a b : ℕ} → (a + b) ≡ (b + a) → S (a + b) ≡ S (b + a)
+comm-support₁ p = +comm-lemma₂∙₁ p