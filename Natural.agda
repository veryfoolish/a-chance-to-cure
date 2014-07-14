{-# OPTIONS --without-K #-}
module Natural where

open import Equality
open import Level using (Level) renaming (suc to lsuc; zero to lzero)

data ℕ : Set lzero where
  O : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN SUC S #-}
{-# BUILTIN ZERO O #-}

infixl 7 _*_ _max_
infixl 6 _+_ _min_ _∸_

-- addition
_+_ : ℕ → ℕ → ℕ
0   + m = m
S n + m = S (n + m)

{-# BUILTIN NATPLUS _+_ #-}

-- saturating subtraction (clamped to 0)
_∸_ : ℕ → ℕ → ℕ
n   ∸ 0   = n
0   ∸ S n = 0
S m ∸ S n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}

-- multiplication
_*_ : ℕ → ℕ → ℕ
0   * m = 0
S n * m = n * m + m

{-# BUILTIN NATTIMES _*_ #-}

-- exponentiation
exp : ℕ → ℕ → ℕ
exp n 0     = 1
exp n (S m) = n * exp n m

-- factorial
_! : ℕ → ℕ
0   ! = 1
S n ! = S n * n !

-- maximum
_max_ : ℕ → ℕ → ℕ
0   max n   = n
S m max 0   = S m
S m max S n = S (m max n)

_min_ : ℕ → ℕ → ℕ
0   min n   = 0
S m min 0   = 0
S m min S n = S (m min n)

infix 4 _≤_ _<_

{- inequalities (note) : Eventually I'll probably have a 'Rel' abstract type like Agda's
standard library. But for now I'm trying to keep things concrete. -}

-- less than or equal to
data _≤_ : ℕ → ℕ → Set (lsuc lzero)  where
  0≤n : ∀ {n}                 → 0 ≤ n
  +1≤ : ∀ {m n} (m≤n : m ≤ n) → (S m) ≤ (S n)

-- less than
_<_ : ℕ → ℕ → Set (lsuc lzero)
m < n = S m ≤ n

-- greater than

_>_ : ℕ → ℕ → Set (lsuc lzero)
m > n = n < m
