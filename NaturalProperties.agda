module NaturalProperties where

open import Natural
open import Equality

-- The algebraic structure (ℕ, +, *, 0, 1) forms a commutative semi-ring.


+0-left-id : {a : ℕ} → 0 + a ≡ a
+0-left-id = refl

+0-right-id : {a : ℕ} → a + 0 ≡ a
+0-right-id {0} = refl
+0-right-id {S n} = ≡-fun-ap S +0-right-id

+comm-zero-id₁ : {a : ℕ} → a + 0 ≡ 0 + a
+comm-zero-id₁ = ≡-trans-flip +0-right-id +0-left-id

+comm-zero-id₂ : {a : ℕ} → 0 + a ≡ a + 0
+comm-zero-id₂ = ≡-trans-flip +0-left-id +0-right-id

