module NaturalProperties where

open import Natural
open import Equality
open import EquationalReasoning


+0-left-id : {a : ℕ} → 0 + a ≡ a
+0-left-id = refl

+0-right-id : {a : ℕ} → a + 0 ≡ a
+0-right-id {0} = refl
+0-right-id {S n} = ≡-fun-ap S +0-right-id

+comm-zero-id₁ : {a : ℕ} → a + 0 ≡ 0 + a
+comm-zero-id₁ = ≡-trans-flip +0-right-id +0-left-id

+comm-zero-id₂ : {a : ℕ} → 0 + a ≡ a + 0
+comm-zero-id₂ = ≡-trans-flip +0-left-id +0-right-id

m+1+n≡1+m+n : (m n : ℕ) → m + S n ≡ S (m + n)
m+1+n≡1+m+n 0 n = refl
m+1+n≡1+m+n (S m) n = ≡-fun-ap S (m+1+n≡1+m+n m n)

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm 0     n = +comm-zero-id₂
+-comm (S m) n = 
            S m + n
          ≡⟨ refl ⟩
            S (m + n)
          ≡⟨ ≡-fun-ap S (+-comm m n) ⟩
           S (n + m)
          ≡⟨ ≡-symmetric (m+1+n≡1+m+n n m) ⟩
           n + S m
          ∎
