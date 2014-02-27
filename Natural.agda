module Natural where

open import Level using (Level) renaming (zero to ∘)

data ℕ : (Set ∘) where
  O : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN SUC S #-}
{-# BUILTIN ZERO O #-}

_+_ : ℕ → ℕ → ℕ
0 + m = m
(S n) + m = S (n + m)


open import Equality

sym : {m n : ℕ} → m ≡ n → n ≡ m
sym refl = refl

S-≡ : {m n : ℕ} → m ≡ n → 1 + m ≡ 1 + n
S-≡ refl = refl

+assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+assoc 0 n p = refl
+assoc (S m) n p = S-≡ (+assoc m n p)

x+0≡x : (m : ℕ) → m + 0 ≡ m
x+0≡x 0 = refl
x+0≡x (S m) = S-≡ (x+0≡x m)

m+1+n≡1+m+n : (m n : ℕ) → m + (1 + n) ≡ 1 + (m + n)
m+1+n≡1+m+n O     n = refl
m+1+n≡1+m+n (S m) n = S-≡ (m+1+n≡1+m+n m n)









